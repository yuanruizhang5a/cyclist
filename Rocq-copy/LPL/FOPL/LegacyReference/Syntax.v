(** * Reified syntax and its executable checks

    This file defines data, not truth in a model. Read it in four parts:
    terms and mutually defined formulas/programs; named FOL substitution;
    updates and labels; occurrences, judgments and reflected syntax checks.
    Semantics.v gives these objects meanings, and RuleGeneration.v uses the
    Boolean checks to construct rules together with their required evidence.

    Names ending in [b] return Booleans; later [_spec] lemmas connect those
    computations to propositions. [Defined] keeps equality decisions and
    other computational proofs transparent so generators can reduce them. *)
From Stdlib Require Import List Bool Arith Lia.
From CyclistRocq.LPL.FOPL Require Import Signature.
Import ListNotations.

Module MakeSyntax (S : SIGNATURE).

(** Program variables, world variables, trace variables and occurrence tags
    occupy distinct syntactic fields. Quantifiers bind named program variables.
    Raw applications have checked arities; raw quantified bodies have checked
    purity. The rule boundary must require [judgment_wfb]. *)
Inductive term : Type :=
| Var (x : nat)
| Fun (f : S.function_symbol) (args : list term).

Fixpoint term_eq_dec (x y : term) : {x = y} + {x <> y}.
Proof.
  decide equality; try apply Nat.eq_dec; try apply S.function_eq_dec.
  apply list_eq_dec; exact term_eq_dec.
Defined.

(** Lists make terms easy to construct. The price is that arity correctness
    is checked explicitly rather than built into the type of [Fun]. *)
Fixpoint term_wfb (t : term) : bool :=
  match t with
  | Var _ => true
  | Fun f ts => Nat.eqb (length ts) (S.function_arity f) && forallb term_wfb ts
  end.

Fixpoint term_vars (t : term) : list nat :=
  match t with
  | Var x => [x]
  | Fun _ ts => flat_map term_vars ts
  end.

(** Terms have no binders, so substitution here is a structural traversal.
    Binder capture is handled by the formula substitution operations below. *)
Fixpoint subst_term (x : nat) (replacement t : term) : term :=
  match t with
  | Var y => if Nat.eqb x y then replacement else t
  | Fun f ts => Fun f (map (subst_term x replacement) ts)
  end.

(** Formulas mention programs through modalities, while programs mention
    formulas through tests. Mutual definitions and a combined induction
    principle are therefore needed for proofs about the whole language. *)
Inductive formula : Type :=
| Truth | Falsity
| Pred (p : S.predicate_symbol) (args : list term)
| Equal (a b : term)
| Neg (a : formula)
| Conj (a b : formula)
| Disj (a b : formula)
| Impl (a b : formula)
| All (x : nat) (body : formula)
| Ex (x : nat) (body : formula)
| First (a : formula)
| Suffix (a b : formula)
| DualSuffix (a b : formula)
| Box (p : program) (a : formula)
| Diamond (p : program) (a : formula)
with program : Type :=
| Assign (x : nat) (value : term)
| Test (guard : formula)
| Seq (a b : program)
| Choice (a b : program)
| Star (body : program).

Scheme formula_mut := Induction for formula Sort Prop
  with program_mut := Induction for program Sort Prop.
Combined Scheme formula_program_mutind from formula_mut, program_mut.

Fixpoint formula_eq_dec (a b : formula) : {a = b} + {a <> b}
with program_eq_dec (a b : program) : {a = b} + {a <> b}.
Proof.
  - decide equality; try apply formula_eq_dec; try apply program_eq_dec;
      try apply term_eq_dec; try apply Nat.eq_dec; try apply S.predicate_eq_dec.
    apply list_eq_dec; exact term_eq_dec.
  - decide equality; try apply program_eq_dec; try apply formula_eq_dec;
      try apply term_eq_dec; apply Nat.eq_dec.
Defined.

(** This single recognizer controls both D2 and the manual pure boundary. *)
Fixpoint pureb (a : formula) : bool :=
  match a with
  | Truth | Falsity | Pred _ _ | Equal _ _ => true
  | Neg a | All _ a | Ex _ a => pureb a
  | Conj a b | Disj a b | Impl a b => pureb a && pureb b
  | _ => false
  end.

(** Raw [All]/[Ex] constructors can contain any formula. This check enforces
    the intended language: their bodies must be recursively pure FOL, as well
    as arity-correct. A modality outside a quantifier remains permitted. *)
Fixpoint formula_wfb (a : formula) : bool :=
  match a with
  | Truth | Falsity => true
  | Pred p ts => Nat.eqb (length ts) (S.predicate_arity p) && forallb term_wfb ts
  | Equal a b => term_wfb a && term_wfb b
  | Neg a | First a => formula_wfb a
  | Conj a b | Disj a b | Impl a b | Suffix a b | DualSuffix a b =>
      formula_wfb a && formula_wfb b
  | All _ a | Ex _ a => pureb a && formula_wfb a
  | Box p a | Diamond p a => program_wfb p && formula_wfb a
  end
with program_wfb (p : program) : bool :=
  match p with
  | Assign _ t => term_wfb t
  | Test a => formula_wfb a
  | Seq a b | Choice a b => program_wfb a && program_wfb b
  | Star a => program_wfb a
  end.

(** Collect all names, including bound names and assignment targets. This
    deliberately conservative collection is suitable for eigenvariable checks. *)
Fixpoint formula_vars (a : formula) : list nat :=
  match a with
  | Truth | Falsity => []
  | Pred _ ts => flat_map term_vars ts
  | Equal a b => term_vars a ++ term_vars b
  | Neg a | First a => formula_vars a
  | Conj a b | Disj a b | Impl a b | Suffix a b | DualSuffix a b =>
      formula_vars a ++ formula_vars b
  | All x a | Ex x a => x :: formula_vars a
  | Box p a | Diamond p a => program_vars p ++ formula_vars a
  end
with program_vars (p : program) : list nat :=
  match p with
  | Assign x t => x :: term_vars t
  | Test a => formula_vars a
  | Seq a b | Choice a b => program_vars a ++ program_vars b
  | Star a => program_vars a
  end.

(** Binding-aware substitution on pure syntax. This raw helper stops at a
    binder for [x], but does not rename other binders. [free_forb] supplies a
    sufficient no-capture condition for its semantic correctness theorem.
    Nonpure constructors are left unchanged; this is not an unrestricted
    term-substitution operation for programs or temporal formulas. Public
    quantifier rules use the capture-avoiding [subst_fo] defined below. *)
Fixpoint raw_subst_fo (x : nat) (t : term) (a : formula) : formula :=
  match a with
  | Truth => Truth
  | Falsity => Falsity
  | Pred p ts => Pred p (map (subst_term x t) ts)
  | Equal l r => Equal (subst_term x t l) (subst_term x t r)
  | Neg a => Neg (raw_subst_fo x t a)
  | Conj a b => Conj (raw_subst_fo x t a) (raw_subst_fo x t b)
  | Disj a b => Disj (raw_subst_fo x t a) (raw_subst_fo x t b)
  | Impl a b => Impl (raw_subst_fo x t a) (raw_subst_fo x t b)
  | All y a => All y (if Nat.eqb x y then a else raw_subst_fo x t a)
  | Ex y a => Ex y (if Nat.eqb x y then a else raw_subst_fo x t a)
  | _ => a
  end.

Fixpoint free_forb (x : nat) (t : term) (a : formula) : bool :=
  match a with
  | Truth | Falsity | Pred _ _ | Equal _ _ => true
  | Neg a => free_forb x t a
  | Conj a b | Disj a b | Impl a b => free_forb x t a && free_forb x t b
  | All y a | Ex y a =>
      if Nat.eqb x y then true
      else negb (existsb (Nat.eqb y) (term_vars t)) && free_forb x t a
  | _ => false
  end.

(** Choosing one above the maximum is deterministic and needs no search for
    a witness. Collecting bound names too makes fresh renaming conservative. *)
Definition fresh_name (names : list nat) := Datatypes.S (fold_right Nat.max 0 names).

Lemma occursb_false x names : existsb (Nat.eqb x) names = false <-> ~ In x names.
Proof.
  rewrite <- not_true_iff_false, existsb_exists. split.
  - intros H Hin; apply H; exists x; split; [exact Hin|apply Nat.eqb_refl].
  - intros H [y [Hin Heq]]; apply Nat.eqb_eq in Heq; subst; contradiction.
Qed.

Lemma fresh_name_not_in names : ~ In (fresh_name names) names.
Proof.
  assert (forall x, In x names -> x <= fold_right Nat.max 0 names) as Hbound.
  { induction names as [|a names IH]; cbn; [tauto|].
    intros x [->|Hin]; [apply Nat.le_max_l|]. eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r]. }
  intro Hin; specialize (Hbound _ Hin); unfold fresh_name in Hbound; lia.
Qed.

(** Renaming a binder changes its body before substitution recurses, so that
    body is not literally a subterm of the original input. A size bound gives
    a terminating fuel implementation; [raw_subst_size] justifies renaming
    without consuming additional formula depth. *)
Fixpoint fol_size (a : formula) : nat :=
  match a with
  | Neg a | All _ a | Ex _ a | First a | Box _ a | Diamond _ a => Datatypes.S (fol_size a)
  | Conj a b | Disj a b | Impl a b | Suffix a b | DualSuffix a b => Datatypes.S (fol_size a + fol_size b)
  | _ => 1
  end.

Lemma raw_subst_size a x t : fol_size (raw_subst_fo x t a) = fol_size a.
Proof.
  induction a; cbn [raw_subst_fo fol_size]; try congruence;
    destruct (Nat.eqb x x0); cbn [fol_size]; congruence.
Qed.

Lemma raw_subst_pure a x t : pureb a = true -> pureb (raw_subst_fo x t a) = true.
Proof.
  induction a; cbn [pureb raw_subst_fo]; intro H; try discriminate; try reflexivity;
    try (apply andb_true_iff in H; rewrite IHa1, IHa2 by tauto; reflexivity);
    try (apply IHa; exact H);
    destruct (Nat.eqb x x0); cbn [pureb]; auto.
Qed.

Lemma rename_free_for a u v : pureb a = true -> ~ In v (formula_vars a) -> free_forb u (Var v) a = true.
Proof.
  induction a; cbn [pureb free_forb formula_vars]; intros Hp Hv; try discriminate; try reflexivity;
    try (apply IHa; assumption).
  - apply andb_true_iff in Hp as [Ha Hb]; apply andb_true_iff; split;
      [apply IHa1|apply IHa2]; try assumption; intro H; apply Hv; apply in_app_iff; auto.
  - apply andb_true_iff in Hp as [Ha Hb]; apply andb_true_iff; split;
      [apply IHa1|apply IHa2]; try assumption; intro H; apply Hv; apply in_app_iff; auto.
  - apply andb_true_iff in Hp as [Ha Hb]; apply andb_true_iff; split;
      [apply IHa1|apply IHa2]; try assumption; intro H; apply Hv; apply in_app_iff; auto.
  - destruct (Nat.eqb u x); [reflexivity|]. apply andb_true_iff; split.
    + apply negb_true_iff, occursb_false; cbn [term_vars]; intro H; destruct H; [subst|contradiction]; apply Hv; now left.
    + apply IHa; [exact Hp|intro H; apply Hv; now right].
  - destruct (Nat.eqb u x); [reflexivity|]. apply andb_true_iff; split.
    + apply negb_true_iff, occursb_false; cbn [term_vars]; intro H; destruct H; [subst|contradiction]; apply Hv; now left.
    + apply IHa; [exact Hp|intro H; apply Hv; now right].
Qed.

(** Total capture-avoiding substitution. At a quantifier there are three
    cases: its binder shadows [x]; its binder would capture a name of [t]; or
    substitution may descend directly. In the second case, rename first to a
    name fresh for the body, replacement and substituted variable. The fuel
    is a proved structural bound; public callers do not choose it. *)
Fixpoint subst_fo_fuel (fuel x : nat) (t : term) (a : formula) : formula :=
  match fuel with
  | 0 => a
  | Datatypes.S fuel =>
    match a with
    | Truth => Truth
    | Falsity => Falsity
    | Pred p ts => Pred p (map (subst_term x t) ts)
    | Equal l r => Equal (subst_term x t l) (subst_term x t r)
    | Neg a => Neg (subst_fo_fuel fuel x t a)
    | Conj a b => Conj (subst_fo_fuel fuel x t a) (subst_fo_fuel fuel x t b)
    | Disj a b => Disj (subst_fo_fuel fuel x t a) (subst_fo_fuel fuel x t b)
    | Impl a b => Impl (subst_fo_fuel fuel x t a) (subst_fo_fuel fuel x t b)
    | All y body =>
        if Nat.eqb x y then a
        else if existsb (Nat.eqb y) (term_vars t) then
          let z := fresh_name (x :: y :: (formula_vars body ++ term_vars t)) in
          All z (subst_fo_fuel fuel x t (raw_subst_fo y (Var z) body))
        else All y (subst_fo_fuel fuel x t body)
    | Ex y body =>
        if Nat.eqb x y then a
        else if existsb (Nat.eqb y) (term_vars t) then
          let z := fresh_name (x :: y :: (formula_vars body ++ term_vars t)) in
          Ex z (subst_fo_fuel fuel x t (raw_subst_fo y (Var z) body))
        else Ex y (subst_fo_fuel fuel x t body)
    | _ => a
    end
  end.

Definition subst_fo x t a := subst_fo_fuel (fol_size a) x t a.

Lemma subst_fo_fuel_pure fuel : forall x t a, pureb a = true -> pureb (subst_fo_fuel fuel x t a) = true.
Proof.
  induction fuel as [|fuel IH]; intros x t a Hp; [exact Hp|].
  destruct a; cbn [subst_fo_fuel pureb] in *; try discriminate; try reflexivity;
    try (apply IH; exact Hp);
    try (apply andb_true_iff in Hp; rewrite !IH by tauto; reflexivity);
    destruct (Nat.eqb x x0); [exact Hp| |exact Hp|];
    destruct (existsb (Nat.eqb x0) (term_vars t)); cbn [pureb];
    apply IH; try (apply raw_subst_pure); exact Hp.
Qed.

(** These abbreviations inherit finite-trace suffix semantics. In particular
    [Next] is false at the last state; [Always] includes the current state.
    Their semantic boundary laws are proved in Semantics.v. *)
Definition Next a := Suffix Falsity a.
Definition Eventually a := Disj a (Suffix Truth a).
Definition Always a := Neg (Eventually (Neg a)).

(** An update is a description of one state, rooted at a world variable.
    [AssignUpdate x t previous] evaluates [t] after [previous], then writes
    [x]. It does not itself store the sequence of intermediate states. *)
Inductive update : Type :=
| Base (world_variable : nat)
| AssignUpdate (x : nat) (value : term) (previous : update).

Fixpoint update_eq_dec (a b : update) : {a = b} + {a <> b}.
Proof. decide equality; try apply term_eq_dec; apply Nat.eq_dec. Defined.

Fixpoint update_wfb (u : update) : bool :=
  match u with
  | Base _ => true
  | AssignUpdate _ t u => term_wfb t && update_wfb u
  end.

Fixpoint update_vars (u : update) : list nat :=
  match u with
  | Base _ => []
  | AssignUpdate x t u => x :: (term_vars t ++ update_vars u)
  end.

(** Labels describe traces. [Join] is kept as a binary syntax tree so exact
    graph matching sees its parentheses; evaluation will use ordinary append.
    A separate label component is needed for each intermediate update state. *)
Inductive label : Type :=
| Empty
| StateLabel (u : update)
| TraceLabel (trace_variable : nat)
| Join (a b : label).

Fixpoint label_eq_dec (a b : label) : {a = b} + {a <> b}.
Proof. decide equality; try apply update_eq_dec; apply Nat.eq_dec. Defined.

Fixpoint label_wfb (l : label) : bool :=
  match l with
  | StateLabel u => update_wfb u
  | Join a b => label_wfb a && label_wfb b
  | _ => true
  end.

(** A join is nonempty when either component is nonempty. Empty components
    are valid units; only an empty complete assertion label is forbidden.
    Trace variables are nonempty because semantic worlds carry that proof. *)
Fixpoint label_nonemptyb (l : label) : bool :=
  match l with
  | Empty => false
  | StateLabel _ | TraceLabel _ => true
  | Join a b => label_nonemptyb a || label_nonemptyb b
  end.

(** These are program-variable names occurring in updates, for eigenvariable
    freshness. World and trace names belong to different syntactic sorts and
    must not be added just because all three are represented by [nat]. *)
Fixpoint label_vars (l : label) : list nat :=
  match l with
  | Empty | TraceLabel _ => []
  | StateLabel u => update_vars u
  | Join a b => label_vars a ++ label_vars b
  end.

(** Sorted label substitutions: a world name receives an update, and a trace
    name receives a label. No arbitrary trace can become the base of an update. *)
Fixpoint subst_world_update (x : nat) (replacement u : update) : update :=
  match u with
  | Base y => if Nat.eqb x y then replacement else u
  | AssignUpdate y t u => AssignUpdate y t (subst_world_update x replacement u)
  end.

Fixpoint subst_world_label (x : nat) (replacement : update) (l : label) : label :=
  match l with
  | StateLabel u => StateLabel (subst_world_update x replacement u)
  | Join a b => Join (subst_world_label x replacement a) (subst_world_label x replacement b)
  | _ => l
  end.

Fixpoint subst_trace_label (x : nat) (replacement l : label) : label :=
  match l with
  | TraceLabel y => if Nat.eqb x y then replacement else l
  | Join a b => Join (subst_trace_label x replacement a) (subst_trace_label x replacement b)
  | _ => l
  end.

(** Explicit label algebra, with a caller-selected path: [false] descends
    left, [true] descends right. At the selected node, [left = true] groups
    to the left. An inapplicable path/rotation leaves the relevant syntax
    unchanged. These operations perform no normalization search. *)
Fixpoint rotate_label (path : list bool) (left : bool) (l : label) : label :=
  match path with
  | [] => if left then
      match l with Join a (Join b c) => Join (Join a b) c | _ => l end
    else match l with Join (Join a b) c => Join a (Join b c) | _ => l end
  | direction :: path => match l with
    | Join a b => if direction then Join a (rotate_label path left b)
        else Join (rotate_label path left a) b
    | _ => l end
  end.

(** Use the same paths to insert or remove an explicit [Empty] component.
    Semantics.v proves that both label-algebra operations preserve evaluation. *)
Fixpoint unit_label (path : list bool) (on_left insert : bool) (l : label) : label :=
  match path with
  | [] => if insert then if on_left then Join Empty l else Join l Empty
      else if on_left then match l with Join Empty a => a | _ => l end
      else match l with Join a Empty => a | _ => l end
  | direction :: path => match l with
    | Join a b => if direction then Join a (unit_label path on_left insert b)
        else Join (unit_label path on_left insert a) b
    | _ => l end
  end.

(** Only these succedent formulas can be followed by a cyclic trace. A tag
    identifies an occurrence, not a formula's syntactic position in a list. *)
Definition traceableb (a : formula) : bool :=
  match a with Box _ _ | Suffix _ _ | DualSuffix _ _ => true | _ => false end.

(** Tags are proof metadata: Semantics.v ignores them when interpreting
    truth, while Progress.v uses them to find the occurrence whose rank is
    followed. Distinct copies of the same labelled formula remain distinct
    occurrences and need distinct tags when both are tagged. *)
Record occurrence : Type := Occ {
  occurrence_label : label;
  occurrence_formula : formula;
  occurrence_tag : option nat
}.

(** [Jdg Gamma Delta] represents a two-sided sequent. Lists preserve exact
    order for graph checking; explicit exchange rules account for reordering.
    Semantically the antecedent is a conjunction and the succedent a
    disjunction, including their empty-list cases. *)
Record judgment : Type := Jdg {
  antecedent : list occurrence;
  succedent : list occurrence
}.

Definition map_label_occurrence (f : label -> label) o :=
  Occ (f o.(occurrence_label)) o.(occurrence_formula) o.(occurrence_tag).
Definition map_labels (f : label -> label) j :=
  Jdg (map (map_label_occurrence f) j.(antecedent)) (map (map_label_occurrence f) j.(succedent)).
Definition rename_occurrence_tag (f : nat -> nat) o :=
  Occ o.(occurrence_label) o.(occurrence_formula) (option_map f o.(occurrence_tag)).
Definition rename_tags (f : nat -> nat) j :=
  Jdg (map (rename_occurrence_tag f) j.(antecedent)) (map (rename_occurrence_tag f) j.(succedent)).

Definition occurrence_eq_dec : forall a b : occurrence, {a = b} + {a <> b}.
Proof.
  decide equality; [decide equality; apply Nat.eq_dec | apply formula_eq_dec | apply label_eq_dec].
Defined.

Definition judgment_eq_dec : forall a b : judgment, {a = b} + {a <> b}.
Proof. decide equality; apply list_eq_dec; apply occurrence_eq_dec. Defined.

Definition judgment_eqb a b := if judgment_eq_dec a b then true else false.
Lemma judgment_eqb_spec a b : judgment_eqb a b = true <-> a = b.
Proof. unfold judgment_eqb; destruct (judgment_eq_dec a b); intuition discriminate. Qed.

(** Exact equality includes tags. Backlink equality ignores only tags:
    labels, update histories, formulas, programs and context order must still
    match. Explicit tag-renaming rules later justify the corresponding ranks. *)
Definition erase_tag o := Occ o.(occurrence_label) o.(occurrence_formula) None.
Definition erase_tags j := Jdg (map erase_tag j.(antecedent)) (map erase_tag j.(succedent)).
Definition backlink_eqb a b := judgment_eqb (erase_tags a) (erase_tags b).

Definition occurrence_vars o := label_vars o.(occurrence_label) ++ formula_vars o.(occurrence_formula).
Definition judgment_vars j := flat_map occurrence_vars (j.(antecedent) ++ j.(succedent)).
Definition eigen_freshb v j l a :=
  negb (existsb (Nat.eqb v) (judgment_vars j ++ label_vars l ++ formula_vars a)).

(** The occurrence check combines four independent requirements: valid label
    syntax, nonempty complete label, valid formula syntax, and legal tagging.
    [right] rejects every antecedent tag, even on a box formula. *)
Definition occurrence_wfb (right : bool) o :=
  label_wfb o.(occurrence_label) && label_nonemptyb o.(occurrence_label) &&
  formula_wfb o.(occurrence_formula) &&
  match o.(occurrence_tag) with
  | None => true
  | Some _ => right && traceableb o.(occurrence_formula)
  end.

Definition judgment_tags j :=
  flat_map (fun o => match o.(occurrence_tag) with None => [] | Some n => [n] end)
    j.(succedent).

Fixpoint unique_tagsb (ts : list nat) :=
  match ts with
  | [] => true
  | t :: ts => negb (existsb (Nat.eqb t) ts) && unique_tagsb ts
  end.

(** Uniqueness makes lookup by tag unambiguous. The generic cyclic framework
    checks edge endpoints, but these object-language invariants belong here. *)
Definition judgment_wfb j :=
  forallb (occurrence_wfb false) j.(antecedent) &&
  forallb (occurrence_wfb true) j.(succedent) && unique_tagsb (judgment_tags j).

Lemma unique_tagsb_spec ts : unique_tagsb ts = true <-> NoDup ts.
Proof.
  induction ts as [|t ts IH]; cbn.
  - split; constructor.
  - rewrite andb_true_iff, negb_true_iff, IH.
    assert (existsb (Nat.eqb t) ts = false <-> ~ In t ts) as H.
    { rewrite <- not_true_iff_false, existsb_exists.
      split.
      - intros H Hin. apply H. exists t; split; [exact Hin | apply Nat.eqb_refl].
      - intros H [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst; contradiction. }
    rewrite H. split; [intros [Hn Hd]; constructor; assumption | intro Hd; inversion Hd; auto].
Qed.

Lemma eigen_freshb_spec v j l a :
  eigen_freshb v j l a = true <->
  ~ In v (judgment_vars j ++ label_vars l ++ formula_vars a).
Proof.
  unfold eigen_freshb. rewrite negb_true_iff, <- not_true_iff_false, existsb_exists.
  split.
  - intros H Hin. apply H. exists v; split; [exact Hin | apply Nat.eqb_refl].
  - intros H [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst; contradiction.
Qed.

(** Propositional specifications for the executable syntax boundary. In
    particular [pure_formula] is exactly D2's grammar, independently of the
    Boolean recognizer used by generators. *)
Inductive pure_formula : formula -> Prop :=
| PureTruth : pure_formula Truth
| PureFalsity : pure_formula Falsity
| PurePred p ts : pure_formula (Pred p ts)
| PureEqual t u : pure_formula (Equal t u)
| PureNeg a : pure_formula a -> pure_formula (Neg a)
| PureConj a b : pure_formula a -> pure_formula b -> pure_formula (Conj a b)
| PureDisj a b : pure_formula a -> pure_formula b -> pure_formula (Disj a b)
| PureImpl a b : pure_formula a -> pure_formula b -> pure_formula (Impl a b)
| PureAll x a : pure_formula a -> pure_formula (All x a)
| PureEx x a : pure_formula a -> pure_formula (Ex x a).

Lemma pureb_spec a : pureb a = true <-> pure_formula a.
Proof.
  split.
  - induction a; cbn [pureb]; intro H; try discriminate;
      try solve [constructor]; try solve [constructor; apply IHa; exact H].
    all: apply andb_true_iff in H as [Ha Hb]; constructor;
      [apply IHa1; exact Ha | apply IHa2; exact Hb].
  - intro H; induction H; cbn [pureb];
      rewrite ?IHpure_formula, ?IHpure_formula1, ?IHpure_formula2; reflexivity.
Qed.

Inductive term_wf : term -> Prop :=
| WfVar x : term_wf (Var x)
| WfFun f ts : length ts = S.function_arity f ->
    Forall term_wf ts -> term_wf (Fun f ts).

Lemma term_wfb_spec t : term_wfb t = true <-> term_wf t.
Proof.
  revert t; fix IH 1; intro t; destruct t as [x|f ts]; cbn [term_wfb].
  - split; intro H; [constructor | reflexivity].
  - assert (forallb term_wfb ts = true <-> Forall term_wf ts) as Hargs.
    { induction ts as [|a ts IHts]; cbn.
      - split; intro H; [constructor | reflexivity].
      - rewrite andb_true_iff, (IH a), IHts.
        split; [intros [Ha Hts]; constructor; assumption | intro H; inversion H; auto]. }
    rewrite andb_true_iff, Nat.eqb_eq, Hargs.
    split; [intros [Harity Hts]; constructor; assumption | intro H; inversion H; auto].
Qed.

Lemma terms_wfb_spec ts : forallb term_wfb ts = true <-> Forall term_wf ts.
Proof.
  induction ts as [|t ts IH]; cbn.
  - split; intro H; [constructor | reflexivity].
  - rewrite andb_true_iff, term_wfb_spec, IH.
    split; [intros [Ht Hts]; constructor; assumption | intro H; inversion H; auto].
Qed.

(** These propositional specifications separate what well-formedness means
    from the executable checks. The mutual reflection proof follows the same
    formula/program induction principle used for semantic freshness later. *)
Fixpoint formula_wf (a : formula) : Prop :=
  match a with
  | Truth | Falsity => True
  | Pred p ts => length ts = S.predicate_arity p /\ Forall term_wf ts
  | Equal a b => term_wf a /\ term_wf b
  | Neg a | First a => formula_wf a
  | Conj a b | Disj a b | Impl a b | Suffix a b | DualSuffix a b =>
      formula_wf a /\ formula_wf b
  | All _ a | Ex _ a => pure_formula a /\ formula_wf a
  | Box p a | Diamond p a => program_wf p /\ formula_wf a
  end
with program_wf (p : program) : Prop :=
  match p with
  | Assign _ t => term_wf t
  | Test a => formula_wf a
  | Seq a b | Choice a b => program_wf a /\ program_wf b
  | Star a => program_wf a
  end.

Lemma formula_program_wfb_spec :
  (forall a, formula_wfb a = true <-> formula_wf a) /\
  (forall p, program_wfb p = true <-> program_wf p).
Proof.
  apply formula_program_mutind; intros; cbn [formula_wfb program_wfb formula_wf program_wf];
    rewrite ?andb_true_iff, ?Nat.eqb_eq, ?terms_wfb_spec, ?term_wfb_spec,
      ?pureb_spec; intuition.
Qed.

Lemma formula_wfb_spec a : formula_wfb a = true <-> formula_wf a.
Proof. apply formula_program_wfb_spec. Qed.

Lemma program_wfb_spec p : program_wfb p = true <-> program_wf p.
Proof. apply formula_program_wfb_spec. Qed.

Fixpoint update_wf u : Prop :=
  match u with
  | Base _ => True
  | AssignUpdate _ t u => term_wf t /\ update_wf u
  end.

Fixpoint label_wf l : Prop :=
  match l with
  | StateLabel u => update_wf u
  | Join a b => label_wf a /\ label_wf b
  | _ => True
  end.

Lemma update_wfb_spec u : update_wfb u = true <-> update_wf u.
Proof.
  induction u; cbn [update_wfb update_wf];
    rewrite ?andb_true_iff, ?term_wfb_spec; intuition.
Qed.

Lemma label_wfb_spec l : label_wfb l = true <-> label_wf l.
Proof.
  induction l; cbn [label_wfb label_wf];
    rewrite ?andb_true_iff, ?update_wfb_spec; intuition.
Qed.

Definition occurrence_wf right o : Prop :=
  label_wf o.(occurrence_label) /\ label_nonemptyb o.(occurrence_label) = true /\
  formula_wf o.(occurrence_formula) /\
  match o.(occurrence_tag) with
  | None => True
  | Some _ => right = true /\ traceableb o.(occurrence_formula) = true
  end.

Definition judgment_wf j : Prop :=
  Forall (occurrence_wf false) j.(antecedent) /\
  Forall (occurrence_wf true) j.(succedent) /\ NoDup (judgment_tags j).

Lemma occurrence_wfb_spec right o : occurrence_wfb right o = true <-> occurrence_wf right o.
Proof.
  unfold occurrence_wfb, occurrence_wf.
  destruct (occurrence_tag o); rewrite !andb_true_iff, label_wfb_spec, formula_wfb_spec;
    intuition.
Qed.

(** This is the full syntax boundary available to a caller who wants to
    reason propositionally after computing [judgment_wfb]. Nonemptiness is
    related to semantic admissibility separately in Semantics.v. *)
Lemma judgment_wfb_spec j : judgment_wfb j = true <-> judgment_wf j.
Proof.
  unfold judgment_wfb, judgment_wf.
  rewrite !andb_true_iff, unique_tagsb_spec, !forallb_forall, !Forall_forall.
  setoid_rewrite occurrence_wfb_spec; tauto.
Qed.

(** Capture avoidance also preserves arities and the recursive pure-body
    invariant. These lemmas require the replacement term to be well formed;
    generators enforce that premise even for an unused replacement. *)
Lemma subst_term_wfb t : forall x replacement, term_wfb t = true ->
  term_wfb replacement = true -> term_wfb (subst_term x replacement t) = true.
Proof.
  revert t; fix IH 1; intro t; destruct t as [y|f ts]; intros x replacement Ht Hr;
    cbn [subst_term term_wfb] in *.
  - destruct (Nat.eqb x y); assumption.
  - apply andb_true_iff in Ht as [Harity Hargs].
    rewrite length_map, Harity; cbn. clear Harity. revert Hargs.
    induction ts as [|a ts IHts]; cbn; intro Hargs; [reflexivity|].
    apply andb_true_iff in Hargs as [Ha Hts].
    rewrite (IH a x replacement Ha Hr), (IHts Hts); reflexivity.
Qed.

Lemma subst_terms_wfb ts x t : forallb term_wfb ts = true -> term_wfb t = true ->
  forallb term_wfb (map (subst_term x t) ts) = true.
Proof.
  intros Hts Ht; induction ts as [|a ts IH]; cbn in *; [reflexivity|].
  apply andb_true_iff in Hts as [Ha Hts].
  rewrite subst_term_wfb by assumption. rewrite IH by assumption. reflexivity.
Qed.

Lemma raw_subst_wfb a x t : formula_wfb a = true -> term_wfb t = true ->
  formula_wfb (raw_subst_fo x t a) = true.
Proof.
  induction a; cbn [raw_subst_fo formula_wfb]; intros Ha Ht;
    try exact Ha; try (apply IHa; assumption).
  - apply andb_true_iff in Ha as [Harity Hargs].
    rewrite length_map, Harity, subst_terms_wfb by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr].
    rewrite !subst_term_wfb by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite IHa1, IHa2 by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite IHa1, IHa2 by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite IHa1, IHa2 by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hp Ha]. destruct (Nat.eqb x x0); cbn [formula_wfb].
    + now rewrite Hp, Ha.
    + rewrite raw_subst_pure, IHa by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hp Ha]. destruct (Nat.eqb x x0); cbn [formula_wfb].
    + now rewrite Hp, Ha.
    + rewrite raw_subst_pure, IHa by assumption. reflexivity.
Qed.

Lemma subst_fo_fuel_wfb fuel : forall a x t, formula_wfb a = true -> term_wfb t = true ->
  formula_wfb (subst_fo_fuel fuel x t a) = true.
Proof.
  induction fuel as [|fuel IH]; intros a x t Ha Ht; [exact Ha|].
  destruct a; cbn [subst_fo_fuel formula_wfb] in *; try exact Ha.
  - apply andb_true_iff in Ha as [Harity Hargs].
    rewrite length_map, Harity, subst_terms_wfb by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr].
    rewrite !subst_term_wfb by assumption. reflexivity.
  - apply IH; assumption.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite !IH by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite !IH by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite !IH by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hp Ha]. destruct (Nat.eqb x x0); [cbn [formula_wfb]; now rewrite Hp, Ha|].
    destruct (existsb (Nat.eqb x0) (term_vars t)); cbn [formula_wfb];
      rewrite subst_fo_fuel_pure, IH by
        (try apply raw_subst_pure; try apply raw_subst_wfb; cbn [term_wfb]; auto);
      reflexivity.
  - apply andb_true_iff in Ha as [Hp Ha]. destruct (Nat.eqb x x0); [cbn [formula_wfb]; now rewrite Hp, Ha|].
    destruct (existsb (Nat.eqb x0) (term_vars t)); cbn [formula_wfb];
      rewrite subst_fo_fuel_pure, IH by
        (try apply raw_subst_pure; try apply raw_subst_wfb; cbn [term_wfb]; auto);
      reflexivity.
Qed.

Lemma subst_fo_wfb a x t : formula_wfb a = true -> term_wfb t = true ->
  formula_wfb (subst_fo x t a) = true.
Proof. apply subst_fo_fuel_wfb. Qed.

Lemma subst_fo_wf a x t : formula_wf a -> term_wf t -> formula_wf (subst_fo x t a).
Proof.
  intros Ha Ht; apply formula_wfb_spec, subst_fo_wfb;
    [now apply formula_wfb_spec | now apply term_wfb_spec].
Qed.

Lemma subst_fo_pure a x t : pure_formula a -> pure_formula (subst_fo x t a).
Proof. intro Ha; apply pureb_spec, subst_fo_fuel_pure, pureb_spec; exact Ha. Qed.

Lemma subst_world_update_wfb u x replacement : update_wfb u = true ->
  update_wfb replacement = true -> update_wfb (subst_world_update x replacement u) = true.
Proof.
  induction u as [y|y t u IH]; cbn [subst_world_update update_wfb]; intros Hu Hr.
  - destruct (Nat.eqb x y); assumption.
  - apply andb_true_iff in Hu as [Ht Hu]. rewrite Ht, IH by assumption. reflexivity.
Qed.

Lemma subst_world_label_wfb l x replacement : label_wfb l = true ->
  update_wfb replacement = true -> label_wfb (subst_world_label x replacement l) = true.
Proof.
  induction l; cbn [subst_world_label label_wfb]; intros Hl Hr; try reflexivity.
  - apply subst_world_update_wfb; assumption.
  - apply andb_true_iff in Hl as [Ha Hb]. rewrite IHl1, IHl2 by assumption. reflexivity.
Qed.

Lemma subst_trace_label_wfb l x replacement : label_wfb l = true ->
  label_wfb replacement = true -> label_wfb (subst_trace_label x replacement l) = true.
Proof.
  induction l as [|u|y|a IHa b IHb]; cbn [subst_trace_label label_wfb]; intros Hl Hr; try exact Hl.
  - destruct (Nat.eqb x y); assumption.
  - apply andb_true_iff in Hl as [Ha Hb]. rewrite IHa, IHb by assumption. reflexivity.
Qed.

End MakeSyntax.
