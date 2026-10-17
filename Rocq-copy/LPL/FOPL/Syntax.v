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
From CyclistRocq.LPL Require Import Signature Syntax.
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

Fixpoint subst_world_update (x : nat) (replacement u : update) : update :=
  match u with
  | Base y => if Nat.eqb x y then replacement else u
  | AssignUpdate y t u => AssignUpdate y t (subst_world_update x replacement u)
  end.

Fixpoint update_world_names u : list nat := match u with
  | Base x => [x] | AssignUpdate _ _ u => update_world_names u end.
(** First-order structure is private to this language adapter. *)
Inductive atom_payload : Type :=
| Predicate (p : S.predicate_symbol) (args : list term)
| Equality (left right : term).
Inductive assignment : Type := Assignment (variable : nat) (value : term).
Definition atom_payload_eq_dec : forall a b : atom_payload, {a=b}+{a<>b}.
Proof. decide equality; try apply term_eq_dec; try apply S.predicate_eq_dec.
  apply list_eq_dec; apply term_eq_dec. Defined.
Definition assignment_eq_dec : forall a b : assignment, {a=b}+{a<>b}.
Proof. decide equality; [apply term_eq_dec|apply Nat.eq_dec]. Defined.
Module Language <: LANGUAGE.
  Definition atom := atom_payload.
  Definition binder := nat.
  Definition action := assignment.
  Definition world_term := update.
  Definition relation_symbol := Empty_set.
  Definition atom_eq_dec := atom_payload_eq_dec.
  Definition binder_eq_dec := Nat.eq_dec.
  Definition action_eq_dec := assignment_eq_dec.
  Definition world_term_eq_dec := update_eq_dec.
  Definition relation_eq_dec (x y : relation_symbol) : {x=y}+{x<>y} := match x with end.
  Definition atom_wfb a := match a with
    | Predicate p ts => Nat.eqb (length ts) (S.predicate_arity p) && forallb term_wfb ts
    | Equality a b => term_wfb a && term_wfb b end.
  Definition extension_wfb (_ : binder) (pure : bool) := pure.
  Definition action_wfb a := match a with Assignment _ t => term_wfb t end.
  Definition world_term_wfb := update_wfb.
  Definition custom_relation_wfb (x : relation_symbol) (_ : nat) : bool := match x with end.
  Definition world_name := Base.
  Definition world_support := update_world_names.
  Definition subst_world := subst_world_update.
End Language.
Module Export Shared := CyclistRocq.LPL.Syntax.MakeSyntax Language.
Definition Pred p ts := Atom (Predicate p ts).
Definition Equal a b := Atom (Equality a b).
Notation All := Extension.
Notation Ex := Coextension.
Definition Assign x t := Atomic (Assignment x t).
Fixpoint formula_vars (a : formula) : list nat :=
  match a with
  | Truth => []
  | Atom (Predicate _ ts) => flat_map term_vars ts
  | Atom (Equality a b) => term_vars a ++ term_vars b
  | Neg a | First a => formula_vars a
  | Conj a b | Suffix a b =>
      formula_vars a ++ formula_vars b
  | All x a => x :: formula_vars a
  | Box p a => program_vars p ++ formula_vars a
  end
with program_vars (p : program) : list nat :=
  match p with
  | Atomic (Assignment x t) => x :: term_vars t
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

  | Atom (Predicate p ts) => Pred p (map (subst_term x t) ts)
  | Atom (Equality l r) => Equal (subst_term x t l) (subst_term x t r)
  | Neg a => Neg (raw_subst_fo x t a)
  | Conj a b => Conj (raw_subst_fo x t a) (raw_subst_fo x t b)

  | All y a => All y (if Nat.eqb x y then a else raw_subst_fo x t a)
  | _ => a
  end.

Fixpoint free_forb (x : nat) (t : term) (a : formula) : bool :=
  match a with
  | Truth | Atom _ => true
  | Neg a => free_forb x t a
  | Conj a b => free_forb x t a && free_forb x t b
  | All y a =>
      if Nat.eqb x y then true
      else negb (existsb (Nat.eqb y) (term_vars t)) && free_forb x t a
  | _ => false
  end.

Fixpoint fol_size (a : formula) : nat :=
  match a with
  | Neg a | All _ a | First a | Box _ a => Datatypes.S (fol_size a)
  | Conj a b | Suffix a b => Datatypes.S (fol_size a + fol_size b)
  | _ => 1
  end.

Lemma raw_subst_size a x t : fol_size (raw_subst_fo x t a) = fol_size a.
Proof.
  induction a as [|[p args|a b]|a IHa|a1 IHa1 a2 IHa2|x0 a IHa|a IHa|a1 IHa1 a2 IHa2|p a IHa]; cbn [raw_subst_fo fol_size]; try reflexivity; try congruence;
    destruct (Nat.eqb x x0); cbn [fol_size]; congruence.
Qed.

Lemma raw_subst_pure a x t : pureb a = true -> pureb (raw_subst_fo x t a) = true.
Proof.
  induction a as [|[p args|a b]|a IHa|a1 IHa1 a2 IHa2|x0 a IHa|a IHa|a1 IHa1 a2 IHa2|p a IHa]; cbn [pureb raw_subst_fo]; intro H; try discriminate; try reflexivity;
    try (apply andb_true_iff in H; rewrite IHa1, IHa2 by tauto; reflexivity);
    try (apply IHa; exact H);
    destruct (Nat.eqb x x0); cbn [pureb]; auto.
Qed.

Lemma rename_free_for a u v : pureb a = true -> ~ In v (formula_vars a) -> free_forb u (Var v) a = true.
Proof.
  induction a as [|[p args|a b]|a IHa|a1 IHa1 a2 IHa2|x0 a IHa|a IHa|a1 IHa1 a2 IHa2|p a IHa]; cbn [pureb free_forb formula_vars]; intros Hp Hv; try discriminate; try reflexivity;
    try (apply IHa; assumption).
  - apply andb_true_iff in Hp as [Ha Hb]; apply andb_true_iff; split;
      [apply IHa1|apply IHa2]; try assumption; intro H; apply Hv; apply in_app_iff; auto.
  - destruct (Nat.eqb u x0); [reflexivity|]. apply andb_true_iff; split.
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

    | Atom (Predicate p ts) => Pred p (map (subst_term x t) ts)
    | Atom (Equality l r) => Equal (subst_term x t l) (subst_term x t r)
    | Neg a => Neg (subst_fo_fuel fuel x t a)
    | Conj a b => Conj (subst_fo_fuel fuel x t a) (subst_fo_fuel fuel x t b)

    | All y body =>
        if Nat.eqb x y then a
        else if existsb (Nat.eqb y) (term_vars t) then
          let z := fresh_name (x :: y :: (formula_vars body ++ term_vars t)) in
          All z (subst_fo_fuel fuel x t (raw_subst_fo y (Var z) body))
        else All y (subst_fo_fuel fuel x t body)
    | _ => a
    end
  end.

Definition subst_fo x t a := subst_fo_fuel (fol_size a) x t a.

Lemma subst_fo_fuel_pure fuel : forall x t a, pureb a = true -> pureb (subst_fo_fuel fuel x t a) = true.
Proof.
  induction fuel as [|fuel IH]; intros x t a Hp; [exact Hp|].
  destruct a as [|[p args|a b]|a|a1 a2|x0 a|a|a1 a2|p a]; cbn [subst_fo_fuel pureb] in *; try discriminate; try reflexivity;
    try (apply IH; exact Hp);
    try (apply andb_true_iff in Hp; rewrite !IH by tauto; reflexivity);
    destruct (Nat.eqb x x0); [exact Hp|];
    destruct (existsb (Nat.eqb x0) (term_vars t)); cbn [pureb];
    apply IH; try (apply raw_subst_pure); exact Hp.
Qed.

Fixpoint label_vars (l : label) : list nat :=
  match l with
  | Empty | TraceLabel _ => []
  | StateLabel u => update_vars u
  | Join a b => label_vars a ++ label_vars b
  end.

Definition occurrence_vars o := label_vars o.(occurrence_label) ++ formula_vars o.(occurrence_formula).
Definition judgment_vars j := flat_map occurrence_vars (j.(antecedent) ++ j.(succedent)).
Definition eigen_freshb v j l a :=
  negb (existsb (Nat.eqb v) (judgment_vars j ++ label_vars l ++ formula_vars a)).

Lemma eigen_freshb_spec v j l a :
  eigen_freshb v j l a = true <->
  ~ In v (judgment_vars j ++ label_vars l ++ formula_vars a).
Proof.
  unfold eigen_freshb. rewrite negb_true_iff, <- not_true_iff_false, existsb_exists.
  split.
  - intros H Hin. apply H. exists v; split; [exact Hin | apply Nat.eqb_refl].
  - intros H [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst; contradiction.
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
  | Truth => True
  | Atom (Predicate p ts) => length ts = S.predicate_arity p /\ Forall term_wf ts
  | Atom (Equality a b) => term_wf a /\ term_wf b
  | Neg a | First a => formula_wf a
  | Conj a b | Suffix a b =>
      formula_wf a /\ formula_wf b
  | All _ a => pure_formula a /\ formula_wf a
  | Box p a => program_wf p /\ formula_wf a
  end
with program_wf (p : program) : Prop :=
  match p with
  | Atomic (Assignment _ t) => term_wf t
  | Test a => formula_wf a
  | Seq a b | Choice a b => program_wf a /\ program_wf b
  | Star a => program_wf a
  end.

Lemma formula_program_wfb_spec :
  (forall a, formula_wfb a = true <-> formula_wf a) /\
  (forall p, program_wfb p = true <-> program_wf p).
Proof.
  apply formula_program_mutind; intros; try match goal with p : Language.atom |- _ => destruct p end;
    try match goal with p : Language.action |- _ => destruct p end; cbn [formula_wfb program_wfb formula_wf program_wf Language.atom_wfb Language.extension_wfb Language.action_wfb];
    unfold Language.atom_wfb, Language.extension_wfb, Language.action_wfb in *;
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
  Forall (fun r => relation_wfb r = true) j.(relations) /\
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
  induction a as [|[p args|a b]|a IHa|a1 IHa1 a2 IHa2|x0 a IHa|a IHa|a1 IHa1 a2 IHa2|p a IHa]; cbn [Pred Equal raw_subst_fo formula_wfb Language.atom_wfb Language.extension_wfb Language.action_wfb]; intros Ha Ht; unfold Language.atom_wfb, Language.extension_wfb, Language.action_wfb in *;
    try exact Ha; try (apply IHa; assumption).
  - apply andb_true_iff in Ha as [Harity Hargs].
    rewrite length_map, Harity, subst_terms_wfb by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr].
    rewrite !subst_term_wfb by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite IHa1, IHa2 by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hp Ha]. destruct (Nat.eqb x x0); cbn [formula_wfb Language.atom_wfb Language.extension_wfb Language.action_wfb].
    + now rewrite Hp, Ha.
    + rewrite raw_subst_pure, IHa by assumption. reflexivity.
Qed.

Lemma subst_fo_fuel_wfb fuel : forall a x t, formula_wfb a = true -> term_wfb t = true ->
  formula_wfb (subst_fo_fuel fuel x t a) = true.
Proof.
  induction fuel as [|fuel IH]; intros a x t Ha Ht; [exact Ha|].
  destruct a as [|[p args|a b]|a|a1 a2|x0 a|a|a1 a2|p a]; cbn [Pred Equal subst_fo_fuel formula_wfb Language.atom_wfb Language.extension_wfb Language.action_wfb] in *; unfold Language.atom_wfb, Language.extension_wfb, Language.action_wfb in *; try exact Ha.
  - apply andb_true_iff in Ha as [Harity Hargs].
    rewrite length_map, Harity, subst_terms_wfb by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr].
    rewrite !subst_term_wfb by assumption. reflexivity.
  - apply IH; assumption.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite !IH by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hp Ha]. destruct (Nat.eqb x x0); [cbn [formula_wfb Language.atom_wfb Language.extension_wfb Language.action_wfb]; now rewrite Hp, Ha|].
    destruct (existsb (Nat.eqb x0) (term_vars t)); cbn [formula_wfb Language.atom_wfb Language.extension_wfb Language.action_wfb];
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
