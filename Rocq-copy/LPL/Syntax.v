(** * Shared reified syntax, independent of any first-order theory.

    Atom payloads, action payloads, extension tokens, world terms and custom
    relation symbols come from LANGUAGE. Extensions have recursive children;
    they are not opaque semantic atoms. Exact equality includes relations and
    tags. World and trace names occupy different fields, even though their
    default representation is nat. *)
From Stdlib Require Import List Bool Arith Lia.
From CyclistRocq.LPL Require Import Signature.
Import ListNotations.
Module MakeSyntax (L : LANGUAGE).
(** Formulas contain programs in modalities; programs contain formulas in
    tests. The mutual definition permits both kinds of nesting. [Extension]
    receives its meaning from an instance; [Coextension] is defined by duality. *)
Inductive formula : Type :=
| Truth
| Atom (p : L.atom)
| Neg (a : formula)
| Conj (a b : formula)
| Extension (x : L.binder) (body : formula)
| First (a : formula)
| Suffix (a b : formula)
| Box (p : program) (a : formula)
with program : Type :=
| Atomic (x : L.action)
| Test (guard : formula)
| Seq (a b : program)
| Choice (a b : program)
| Star (body : program).

Definition Falsity := Neg Truth.
Definition Disj a b := Neg (Conj (Neg a) (Neg b)).
Definition Impl a b := Neg (Conj a (Neg b)).
Definition Coextension x a := Neg (Extension x (Neg a)).
Definition DualSuffix a b := Neg (Suffix (Neg a) (Neg b)).
Definition Diamond p a := Neg (Box p (Neg a)).

(** Computational views expose every applicable derived encoding. They are
    intentionally independent: for example a disjunction is an implication
    too, and both named rules must remain available. *)
Definition falsity_view a := match a with Neg Truth => true | _ => false end.
Definition disj_view a := match a with Neg (Conj (Neg b) (Neg c)) => Some (b,c) | _ => None end.
Definition impl_view a := match a with Neg (Conj b (Neg c)) => Some (b,c) | _ => None end.
Definition coextension_view a := match a with Neg (Extension x (Neg b)) => Some (x,b) | _ => None end.
Definition dual_suffix_view a := match a with Neg (Suffix (Neg b) (Neg c)) => Some (b,c) | _ => None end.
Definition diamond_view a := match a with Neg (Box p (Neg b)) => Some (p,b) | _ => None end.
Lemma falsity_view_sound a : falsity_view a = true -> a = Falsity.
Proof. destruct a; try discriminate; destruct a; discriminate || reflexivity. Qed.
Lemma disj_view_sound a b c : disj_view a = Some (b,c) -> a = Disj b c.
Proof. destruct a; try discriminate; destruct a; try discriminate; destruct a1; try discriminate; destruct a2; intros H; inversion H; reflexivity. Qed.
Lemma impl_view_sound a b c : impl_view a = Some (b,c) -> a = Impl b c.
Proof. destruct a; try discriminate; destruct a; try discriminate; destruct a2; intros H; inversion H; reflexivity. Qed.
Lemma coextension_view_sound a x b : coextension_view a = Some (x,b) -> a = Coextension x b.
Proof. destruct a; try discriminate; destruct a; try discriminate; destruct a; intros H; inversion H; reflexivity. Qed.
Lemma dual_suffix_view_sound a b c : dual_suffix_view a = Some (b,c) -> a = DualSuffix b c.
Proof. destruct a; try discriminate; destruct a; try discriminate; destruct a1; try discriminate; destruct a2; intros H; inversion H; reflexivity. Qed.
Lemma diamond_view_sound a p b : diamond_view a = Some (p,b) -> a = Diamond p b.
Proof. destruct a; try discriminate; destruct a; try discriminate; destruct a; intros H; inversion H; reflexivity. Qed.

(** A combined induction principle supplies hypotheses for both syntax
    trees. It is needed when a property crosses from a modality into its
    program and then back into a test formula. *)
Scheme formula_mut := Induction for formula Sort Prop
  with program_mut := Induction for program Sort Prop.
Combined Scheme formula_program_mutind from formula_mut, program_mut.

(** [decide equality] handles constructors; recursive calls and LANGUAGE's
    decisions handle their fields. [Defined] keeps these decisions reducible
    so Boolean checkers can compute with them. *)
Fixpoint formula_eq_dec (a b : formula) : {a = b} + {a <> b}
with program_eq_dec (a b : program) : {a = b} + {a <> b}.
Proof.
  - decide equality; try apply formula_eq_dec; try apply program_eq_dec;
      try apply L.binder_eq_dec; try apply L.atom_eq_dec.
  - decide equality; try apply program_eq_dec; try apply formula_eq_dec;
      apply L.action_eq_dec.
Defined.

(** Purity here means membership in a syntactic nonmodal fragment. It does
    not by itself prove that a formula observes only the first state:
    extension interpretations are arbitrary until an instance supplies laws. *)
Fixpoint pureb (a : formula) : bool :=
  match a with
  | Truth | Atom _ => true
  | Neg a | Extension _ a => pureb a
  | Conj a b => pureb a && pureb b
  | _ => false
  end.

(** Extension tokens select their own body policy. The checker supplies
    the nonmodal-fragment bit to that policy; FOPL requires it to be true. *)
Fixpoint formula_wfb (a : formula) : bool :=
  match a with
  | Truth => true
  | Atom p => L.atom_wfb p
  | Neg a | First a => formula_wfb a
  | Conj a b | Suffix a b =>
      formula_wfb a && formula_wfb b
  | Extension x a => L.extension_wfb x (pureb a) && formula_wfb a
  | Box p a => program_wfb p && formula_wfb a
  end
with program_wfb (p : program) : bool :=
  match p with
  | Atomic x => L.action_wfb x
  | Test a => formula_wfb a
  | Seq a b | Choice a b => program_wfb a && program_wfb b
  | Star a => program_wfb a
  end.

(** One greater than the largest used number is fresh, including when the
    list is empty. The same helper serves world names and occurrence tags;
    callers supply the list belonging to the intended namespace. *)
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

(** Derived temporal notation, using the strict suffix semantics. [Next]
    selects the immediate nonempty tail because [Falsity] rules out any
    intermediate suffix. [Eventually] also allows the current trace. *)
Definition Next a := Suffix Falsity a.
Definition Eventually a := Disj a (Suffix Truth a).
Definition Always a := Neg (Eventually (Neg a)).

(** Labels are trees describing state lists. [Join] is plain concatenation:
    [Join (StateLabel u) (StateLabel u)] records two copies of the state.
    [StateLabel] and [TraceLabel] use separate environments, so the same
    numeric name may safely occur in both sorts. *)
Inductive label : Type :=
| Empty
| StateLabel (u : L.world_term)
| TraceLabel (trace_variable : nat)
| Join (a b : label).

Fixpoint label_eq_dec (a b : label) : {a = b} + {a <> b}.
Proof. decide equality; try apply L.world_term_eq_dec; apply Nat.eq_dec. Defined.

Fixpoint label_wfb (l : label) : bool :=
  match l with
  | StateLabel u => L.world_term_wfb u
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

(** World substitution enters only world terms; trace substitution replaces
    only whole trace variables. Neither operation changes formula payloads.
    Relations and contexts are handled later by mapping these operations
    over every label in a judgment. *)
Fixpoint subst_world_label (x : nat) (replacement : L.world_term) (l : label) : label :=
  match l with
  | StateLabel u => StateLabel (L.subst_world x replacement u)
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

(** These are the only formula shapes allowed to carry cyclic trace tags.
    This policy concerns proof progress, separately from formula truth. *)
Definition traceableb (a : formula) : bool :=
  match a with Box _ _ | Suffix _ _ => true | _ => match dual_suffix_view a with Some _ => true | None => false end end.

(** Tags are proof metadata: Semantics.v ignores them when interpreting
    truth, while Progress.v uses them to find the occurrence whose rank is
    followed. Distinct copies of the same labelled formula remain distinct
    occurrences and need distinct tags when both are tagged. *)
Record occurrence : Type := Occ {
  occurrence_label : label;
  occurrence_formula : formula;
  occurrence_tag : option nat
}.

(** Relational assumptions are explicit and untagged. The ordinary Jdg
    abbreviation denotes exactly the relation-free legacy fragment. *)
Inductive relation_atom : Type :=
| ActionRelation (action : L.action) (source target : label)
| CustomRelation (symbol : L.relation_symbol) (arguments : list label).
Definition relation_labels r := match r with
  | ActionRelation _ source target => [source;target]
  | CustomRelation _ arguments => arguments end.
Definition map_relation (f : label -> label) r := match r with
  | ActionRelation a s t => ActionRelation a (f s) (f t)
  | CustomRelation symbol arguments => CustomRelation symbol (map f arguments) end.
Definition relation_wfb r :=
  (match r with ActionRelation a _ _ => L.action_wfb a
   | CustomRelation symbol arguments => L.custom_relation_wfb symbol (length arguments) end) &&
  forallb (fun l => label_wfb l && label_nonemptyb l) (relation_labels r).
Definition relation_eq_dec : forall a b : relation_atom, {a=b}+{a<>b}.
Proof.
  decide equality; try apply L.action_eq_dec;
    try apply label_eq_dec; try apply L.relation_eq_dec.
  apply list_eq_dec; apply label_eq_dec.
Defined.
(** Read [Rdg R Gamma Delta] as [R ; Gamma => Delta]: relational assumptions,
    formula assumptions, and formula alternatives to establish. Lists retain
    their order and multiplicity, which matters to positional rule requests
    and exact graph-label comparisons. *)
Record judgment : Type := Rdg {
  relations : list relation_atom;
  antecedent : list occurrence;
  succedent : list occurrence
}.
Definition Jdg := Rdg [].
Definition map_label_occurrence (f : label -> label) o :=
  Occ (f o.(occurrence_label)) o.(occurrence_formula) o.(occurrence_tag).
(** Map relations as well as assertion labels. Leaving relation labels out
    would make a purported whole-judgment substitution semantically wrong. *)
Definition map_labels (f : label -> label) j :=
  Rdg (map (map_relation f) j.(relations))
    (map (map_label_occurrence f) j.(antecedent)) (map (map_label_occurrence f) j.(succedent)).
Definition rename_occurrence_tag (f : nat -> nat) o :=
  Occ o.(occurrence_label) o.(occurrence_formula) (option_map f o.(occurrence_tag)).
Definition rename_tags (f : nat -> nat) j :=
  Rdg j.(relations) (map (rename_occurrence_tag f) j.(antecedent)) (map (rename_occurrence_tag f) j.(succedent)).
Definition occurrence_eq_dec : forall a b : occurrence, {a=b}+{a<>b}.
Proof. decide equality; [decide equality; apply Nat.eq_dec | apply formula_eq_dec | apply label_eq_dec]. Defined.
Definition judgment_eq_dec : forall a b : judgment, {a=b}+{a<>b}.
Proof. decide equality; apply list_eq_dec; [apply occurrence_eq_dec|apply occurrence_eq_dec|apply relation_eq_dec]. Defined.
Definition judgment_eqb a b := if judgment_eq_dec a b then true else false.
Lemma judgment_eqb_spec a b : judgment_eqb a b = true <-> a=b.
Proof. unfold judgment_eqb; destruct (judgment_eq_dec a b); intuition discriminate. Qed.
(** A backlink compares all logical syntax after erasing tags only. It still
    compares relation contexts, label trees and formula order exactly. Tag
    routing across that backlink needs its own proved rule in Rules.v. *)
Definition erase_tag o := Occ o.(occurrence_label) o.(occurrence_formula) None.
Definition erase_tags j := Rdg j.(relations) (map erase_tag j.(antecedent)) (map erase_tag j.(succedent)).
Definition backlink_eqb a b := judgment_eqb (erase_tags a) (erase_tags b).
(** [right] selects the succedent policy: a tag on the left is rejected,
    and a tag on the right requires a traceable formula. [None] is allowed
    on either side, even for a formula that could otherwise be traced. *)
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
  forallb relation_wfb j.(relations) &&
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

(** This inductive predicate is the proof-facing version of [pureb]. Its
    constructors support induction over primitive pure formulas; [pureb_spec]
    bridges it to the executable test. Derived pure operators follow by
    their expansions. *)
Inductive pure_formula : formula -> Prop :=
| PureTruth : pure_formula Truth
| PurePred p : pure_formula (Atom p)
| PureNeg a : pure_formula a -> pure_formula (Neg a)
| PureConj a b : pure_formula a -> pure_formula b -> pure_formula (Conj a b)
| PureAll x a : pure_formula a -> pure_formula (Extension x a).

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

(** Freshness covers every world term in assertion labels and relational
    arguments. Formula and action payloads have their own language-specific
    sorts; this check is specifically for the world-label namespace. *)
Fixpoint label_world_names l := match l with
  | Empty | TraceLabel _ => [] | StateLabel u => L.world_support u
  | Join a b => label_world_names a ++ label_world_names b end.
Definition judgment_world_names j :=
  flat_map (fun r => flat_map label_world_names (relation_labels r)) j.(relations) ++
  flat_map (fun o => label_world_names o.(occurrence_label)) (j.(antecedent) ++ j.(succedent)).
Definition world_freshb x j := negb (existsb (Nat.eqb x) (judgment_world_names j)).
Lemma world_freshb_spec x j : world_freshb x j = true <-> ~ In x (judgment_world_names j).
Proof. unfold world_freshb; rewrite negb_true_iff; apply occursb_false. Qed.

(** Propositional specifications for the reflected boundary. Payload
    validity belongs to the language; recursive structure belongs here.
    Each [_spec] theorem turns a successful Boolean check into a [Prop]
    usable in proofs, and conversely. Thus generation can compute checks
    while soundness proofs reason with conjunctions, [Forall] and [NoDup]. *)
Fixpoint formula_wf a : Prop := match a with
  | Truth => True
  | Atom p => L.atom_wfb p = true
  | Neg a | First a => formula_wf a
  | Conj a b | Suffix a b => formula_wf a /\ formula_wf b
  | Extension x a => L.extension_wfb x (pureb a) = true /\ formula_wf a
  | Box p a => program_wf p /\ formula_wf a end
with program_wf p : Prop := match p with
  | Atomic action => L.action_wfb action = true
  | Test a => formula_wf a
  | Seq a b | Choice a b => program_wf a /\ program_wf b
  | Star a => program_wf a end.
Lemma formula_program_wfb_spec :
  (forall a, formula_wfb a = true <-> formula_wf a) /\
  (forall p, program_wfb p = true <-> program_wf p).
Proof.
  apply formula_program_mutind; intros; cbn [formula_wfb program_wfb formula_wf program_wf];
    rewrite ?andb_true_iff; intuition.
Qed.
Lemma formula_wfb_spec a : formula_wfb a = true <-> formula_wf a.
Proof. apply formula_program_wfb_spec. Qed.
Lemma program_wfb_spec p : program_wfb p = true <-> program_wf p.
Proof. apply formula_program_wfb_spec. Qed.
Fixpoint label_wf l : Prop := match l with
  | StateLabel u => L.world_term_wfb u = true
  | Join a b => label_wf a /\ label_wf b | _ => True end.
Lemma label_wfb_spec l : label_wfb l = true <-> label_wf l.
Proof. induction l; cbn [label_wfb label_wf]; rewrite ?andb_true_iff; intuition. Qed.
Lemma checked_labels_spec labels :
  forallb (fun l => label_wfb l && label_nonemptyb l) labels = true <->
  Forall (fun l => label_wf l /\ label_nonemptyb l = true) labels.
Proof.
  induction labels as [|l labels IH]; cbn.
  - split; intro H; [constructor|reflexivity].
  - rewrite !andb_true_iff, label_wfb_spec, IH.
    split; [intros [[Hl Hne] Hrest]; constructor; auto|intro H; inversion H; tauto].
Qed.
Definition relation_wf r :=
  (match r with ActionRelation a _ _ => L.action_wfb a
    | CustomRelation symbol args => L.custom_relation_wfb symbol (length args) end) = true /\
  Forall (fun l => label_wf l /\ label_nonemptyb l = true) (relation_labels r).
Lemma relation_wfb_spec r : relation_wfb r = true <-> relation_wf r.
Proof. unfold relation_wfb, relation_wf; rewrite andb_true_iff, checked_labels_spec; reflexivity. Qed.
Definition occurrence_wf right o :=
  label_wf o.(occurrence_label) /\ label_nonemptyb o.(occurrence_label) = true /\
  formula_wf o.(occurrence_formula) /\ match o.(occurrence_tag) with
  | None => True | Some _ => right=true /\ traceableb o.(occurrence_formula)=true end.
Lemma occurrence_wfb_spec right o : occurrence_wfb right o = true <-> occurrence_wf right o.
Proof.
  unfold occurrence_wfb, occurrence_wf; destruct (occurrence_tag o);
    rewrite !andb_true_iff, label_wfb_spec, formula_wfb_spec; intuition.
Qed.
Definition judgment_wf j :=
  Forall relation_wf j.(relations) /\ Forall (occurrence_wf false) j.(antecedent) /\
  Forall (occurrence_wf true) j.(succedent) /\ NoDup (judgment_tags j).
Lemma judgment_wfb_spec j : judgment_wfb j = true <-> judgment_wf j.
Proof.
  unfold judgment_wfb, judgment_wf; rewrite !andb_true_iff, unique_tagsb_spec, !forallb_forall, !Forall_forall.
  setoid_rewrite relation_wfb_spec; setoid_rewrite occurrence_wfb_spec; tauto.
Qed.

End MakeSyntax.

(** Consumers receive this exact syntax module instead of applying the
    inductive functor again. *)
Module Type SYNTAX (L : LANGUAGE).
  Include MakeSyntax L.
End SYNTAX.
