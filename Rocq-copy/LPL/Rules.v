(** * Theorem-backed local rule kernels

    Every rule record must provide two proofs: validity follows from valid
    premises, and a false conclusion yields one false premise/world respecting
    all trace pairs on that selected edge. Ordinary logical soundness alone
    does not establish the second, rank-sensitive obligation.

    Read the common context/local-rule helpers first, then one simple Boolean
    rule. The [_base] modal rules establish semantics; [enhance_right] and
    [redecorate] add proved principal trace pairs. Later sections handle
    changed worlds for substitution/eigenvariables, backlinks, and manual
    pure leaves. RULE_EXPANSIONS.md fixes the ordered premises of each rule.

    Most constructors end with [Defined] so local generation can compute
    their conclusions, premises and edge metadata. Their proof obligations
    are still checked by Rocq, not trusted assertions. *)
From Stdlib Require Import List Bool Arith Lia String Classical_Prop Permutation.
From Stdlib Require Import Logic.ClassicalDescription Logic.ClassicalEpsilon.
From CyclistRocq.LPL Require Import Signature Syntax Semantics Progress.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Module MakeRulesForModel (L : LANGUAGE) (Syn : SYNTAX L) (Sem : SEMANTICS L Syn)
    (Pr : PROGRESS L Syn Sem) (I : Sem.INTERPRETATION).
Import Syn Sem.
Module Export P := Pr.ForModel I.
Definition context_tags (context : list occurrence) := judgment_tags (Jdg [] context).

(** Tag uniqueness allows a list lookup to be replaced by the rank of a known
    tagged member. Many edge proofs use this to reason about formulas rather
    than the mechanics of [rank_in_context]. *)
Lemma rank_context_occ context w o tag :
  NoDup (context_tags context) -> In o context -> occurrence_tag o = Some tag ->
  rank_in_context context w tag = occurrence_rank o w.
Proof.
  induction context as [|head rest IH]; cbn; [contradiction|].
  unfold context_tags in *; cbn in *.
  destruct (occurrence_tag head) as [t|] eqn:Htag; cbn in *.
  - intros Hunique Hin Ho. inversion Hunique as [|? ? Hnot Htail]; subst.
    destruct Hin as [->|Hin].
    + rewrite Ho in Htag; inversion Htag; subst. now rewrite Nat.eqb_refl.
    + destruct (Nat.eqb tag t) eqn:Heq.
      * apply Nat.eqb_eq in Heq; subst tag. exfalso; apply Hnot.
        apply in_flat_map; exists o; split; [exact Hin|]. rewrite Ho; cbn; auto.
      * apply IH; assumption.
  - intros Hunique [->|Hin] Ho; [congruence|]. apply IH; assumption.
Qed.

Definition occurrence_eqb a b := if occurrence_eq_dec a b then true else false.
Lemma occurrence_eqb_spec a b : occurrence_eqb a b = true <-> a = b.
Proof. unfold occurrence_eqb; destruct (occurrence_eq_dec a b); intuition discriminate. Qed.

(** Retain a context pair only for an exactly unchanged occurrence in both
    succedents. The pair contains tags, not list indices, and carries no
    progress: its rank is equal because its formula and label are unchanged. *)
Fixpoint retained_pairs (source target : list occurrence) : list (nat * nat) :=
  match source with
  | [] => []
  | o :: rest =>
      match o.(occurrence_tag) with
      | None => retained_pairs rest target
      | Some t => if existsb (occurrence_eqb o) target
          then (t,t) :: retained_pairs rest target else retained_pairs rest target
      end
  end.

Lemma retained_pairs_spec source target a b : In (a,b) (retained_pairs source target) ->
  a = b /\ exists o, In o source /\ In o target /\ occurrence_tag o = Some a.
Proof.
  induction source as [|o rest IH]; cbn; [contradiction|].
  destruct (occurrence_tag o) as [t|] eqn:Ht.
  - destruct (existsb (occurrence_eqb o) target) eqn:Hmem.
    + intros [Heq|Hin].
      * inversion Heq; subst. split; [reflexivity|]. exists o; split; [now left|].
        apply existsb_exists in Hmem as [x [Hin Hx]].
        apply occurrence_eqb_spec in Hx; subst x; auto.
      * destruct (IH Hin) as [Hab [x [Hs [Htar Htag]]]]. split; [exact Hab|]. exists x; auto.
    + intro Hin; destruct (IH Hin) as [Hab [x [Hs [Htar Htag]]]]. split; [exact Hab|]. exists x; auto.
  - intro Hin; destruct (IH Hin) as [Hab [x [Hs [Htar Htag]]]]. split; [exact Hab|]. exists x; auto.
Qed.

Definition retained_edge source target : Cyclic.edge_info :=
  {| Cyclic.edge_valid := retained_pairs source.(succedent) target.(succedent);
     Cyclic.edge_progress := [] |}.

Lemma wf_unique j : judgment_wfb j = true -> NoDup (context_tags j.(succedent)).
Proof. unfold judgment_wfb, context_tags; rewrite !andb_true_iff; intros [_ H]; now apply unique_tagsb_spec. Qed.

Lemma retained_edge_respects source target w :
  judgment_wfb source = true -> judgment_wfb target = true ->
  Cyclic.respects_edge source target w w (retained_edge source target).
Proof.
  intros Hsource Htarget; split.
  - intros a b Hin; apply retained_pairs_spec in Hin as [-> [o [Hs [Ht Htag]]]].
    unfold LPLTheory.rank.
    rewrite (rank_context_occ _ _ o _ (wf_unique _ Hsource) Hs Htag).
    rewrite (rank_context_occ _ _ o _ (wf_unique _ Htarget) Ht Htag). lia.
  - intros a b H; inversion H.
Qed.

(** Finite semantic selection by classical truth cases. This is used in
    soundness proofs to return a dependent witness (index, judgment, failure
    proof); it is not an executable strategy for proving object-language
    goals or for deciding arbitrary predicate truth. *)
Definition false_premise (targets : list judgment) (w : world M)
    (H : ~ (forall j, In j targets -> denote M j w)) :
    { k : nat & { j : judgment | nth_error targets k = Some j /\ ~ denote M j w }}.
Proof.
  induction targets as [|head rest IH].
  - exfalso; apply H; cbn; tauto.
  - destruct (excluded_middle_informative (denote M head w)) as [Hhead|Hhead].
    + assert (~ (forall j, In j rest -> denote M j w)) as Hrest.
      { intro Hall; apply H; intros j [->|Hin]; auto. }
      destruct (IH Hrest) as [k [j [Hnth Hfalse]]]. exists (Datatypes.S k), j; cbn; auto.
    + exists 0, head; auto.
Defined.

(** A finite local semantic inference, with all retained context pairs proved
    simultaneously. [Hlocal] reasons at one world; the first record field
    lifts it to validity. Its contrapositive supplies a false premise for the
    second field. Source and premise well-formedness ensure that admissibility
    cannot make the required countermodel implication vacuous.
    The world stays unchanged here; substitution and eigenvariable rules use
    other constructors below. This constructor performs no proof search. *)
Definition local_rule (name : string) (source : judgment) (targets : list judgment)
    (Hsource : judgment_wfb source = true)
    (Htargets : Forall (fun j => judgment_wfb j = true) targets)
    (Hlocal : forall w, (forall j, In j targets -> denote M j w) -> denote M source w)
    : Cyclic.rule_instance.
Proof.
  let premise := constr:(fun j => {| Cyclic.premise_judgment := j;
    Cyclic.premise_edge := retained_edge source j |}) in
  refine {| Cyclic.rule_name := name; Cyclic.rule_conclusion := source;
    Cyclic.rule_premises := map premise targets |}.
  - intros Hall w; apply Hlocal; intros j Hin.
    apply (Hall {| Cyclic.premise_judgment := j; Cyclic.premise_edge := retained_edge source j |}).
    apply in_map_iff; exists j; auto.
  - intros w Hfalse.
    assert (~ (forall j, In j targets -> denote M j w)) as Hbad by (intro Hall; apply Hfalse; apply Hlocal; exact Hall).
    destruct (false_premise targets w Hbad) as [k [j [Hnth Hj]]].
    exists k, {| Cyclic.premise_judgment := j; Cyclic.premise_edge := retained_edge source j |}, w.
    split.
    + rewrite nth_error_map.
      exact (f_equal (option_map (fun j : judgment =>
        {| Cyclic.premise_judgment := j; Cyclic.premise_edge := retained_edge source j |})) Hnth).
    + split; [exact Hj|].
      apply retained_edge_respects; [exact Hsource|].
      rewrite Forall_forall in Htargets. apply Htargets; eapply nth_error_In; eauto.
Defined.

Definition counter_world r w H :=
  proj1_sig (projT2 (projT2 (r.(Cyclic.rule_counter_step) w H))).

Lemma local_rule_world name source targets Hs Ht Hlocal w Hfalse :
  counter_world (local_rule name source targets Hs Ht Hlocal) w Hfalse = w.
Proof.
  unfold counter_world, local_rule; cbn.
  match goal with |- context [false_premise ?targets ?w ?proof] =>
    destruct (false_premise targets w proof) as [k [j [Hnth Hbad]]] end.
  reflexivity.
Qed.

Lemma left_app w a b : left_holds M w (a ++ b) <-> left_holds M w a /\ left_holds M w b.
Proof. apply Forall_app. Qed.
Lemma left_cons w o rest : left_holds M w (o :: rest) <-> labelled_holds M w o /\ left_holds M w rest.
Proof. apply Forall_cons_iff. Qed.
Lemma right_app w a b : right_holds M w (a ++ b) <-> right_holds M w a \/ right_holds M w b.
Proof. unfold right_holds; setoid_rewrite in_app_iff; firstorder. Qed.
Lemma right_cons w o rest : right_holds M w (o :: rest) <-> labelled_holds M w o \/ right_holds M w rest.
Proof. unfold right_holds; cbn; firstorder congruence. Qed.

Lemma denote_wf j w : judgment_wfb j = true ->
  (denote M j w <-> (relations_hold M w j.(relations) -> left_holds M w j.(antecedent) -> right_holds M w j.(succedent))).
Proof.
  intro Hwf; unfold denote. pose proof (judgment_wfb_admissible M j w Hwf); tauto.
Qed.

Section RelationContext.
Context (R : list relation_atom).
Local Notation Jdg := (Rdg R).
Definition right_conclusion lhs pre post principal := Jdg lhs (pre ++ principal :: post).
Definition right_targets lhs pre post alternatives :=
  map (fun replacement => Jdg lhs (pre ++ replacement ++ post)) alternatives.
Definition left_conclusion pre post rhs principal := Jdg (pre ++ principal :: post) rhs.
Definition left_targets pre post rhs alternatives :=
  map (fun replacement => Jdg (pre ++ replacement ++ post) rhs) alternatives.

(** For a right rule, if neither surrounding succedent context is already
    true, the premise disjunctions must establish the principal. For a left
    rule, a true principal supplies one true replacement context. These two
    helpers factor out sequent bookkeeping from each logical decomposition. *)
Definition right_many (name : string) (lhs pre post : list occurrence) (principal : occurrence) (alternatives : list (list occurrence))
    (Hs : judgment_wfb (right_conclusion lhs pre post principal) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post alternatives))
    (Hdecompose : forall w, label_admissible M w principal.(occurrence_label) ->
      (forall replacement, In replacement alternatives -> right_holds M w replacement) ->
      labelled_holds M w principal) : Cyclic.rule_instance.
Proof.
  apply (local_rule name _ _ Hs Ht). intros w Hall.
  apply (proj2 (denote_wf _ w Hs)). cbn [right_conclusion antecedent succedent].
  intros Hrelations Hlhs. rewrite right_app, right_cons.
  destruct (classic (right_holds M w pre \/ right_holds M w post)) as [[Hpre|Hpost]|Hnone]; auto.
  right; left. apply Hdecompose.
  - pose proof (judgment_wfb_admissible M _ w Hs) as Ha.
    destruct Ha as [Ha _]; rewrite Forall_forall in Ha.
    apply (Ha principal). cbn; rewrite !in_app_iff; cbn; tauto.
  - intros replacement Hin.
    set (target := Jdg lhs (pre ++ replacement ++ post)).
    assert (In target (right_targets lhs pre post alternatives)) as Hmember.
    { apply in_map_iff; exists replacement; auto. }
    specialize (Hall target Hmember).
    rewrite Forall_forall in Ht.
    pose proof (proj1 (denote_wf target w (Ht target Hmember)) Hall) as Hraw.
    clear Hall; rename Hraw into Hall.
    specialize (Hall Hrelations Hlhs). unfold target in Hall; cbn in Hall.
    rewrite !right_app in Hall. tauto.
Defined.

Definition left_many (name : string) (pre post rhs : list occurrence) (principal : occurrence) (alternatives : list (list occurrence))
    (Hs : judgment_wfb (left_conclusion pre post rhs principal) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (left_targets pre post rhs alternatives))
    (Hdecompose : forall w, labelled_holds M w principal ->
      exists replacement, In replacement alternatives /\ left_holds M w replacement)
    : Cyclic.rule_instance.
Proof.
  apply (local_rule name _ _ Hs Ht). intros w Hall.
  apply (proj2 (denote_wf _ w Hs)). cbn [left_conclusion antecedent succedent].
  intro Hrelations. rewrite left_app, left_cons. intros [Hpre [Hprincipal Hpost]].
  destruct (Hdecompose w Hprincipal) as [replacement [Hin Hreplacement]].
  set (target := Jdg (pre ++ replacement ++ post) rhs).
  assert (In target (left_targets pre post rhs alternatives)) as Hmember.
  { apply in_map_iff; exists replacement; auto. }
  specialize (Hall target Hmember).
  rewrite Forall_forall in Ht.
    pose proof (proj1 (denote_wf target w (Ht target Hmember)) Hall) as Hraw.
    clear Hall; rename Hraw into Hall.
  apply Hall; [exact Hrelations|]. unfold target; cbn. rewrite !left_app; auto.
Defined.

Lemma right_singleton w o : right_holds M w [o] <-> labelled_holds M w o.
Proof. unfold right_holds; cbn; firstorder congruence. Qed.
Lemma left_singleton w o : left_holds M w [o] <-> labelled_holds M w o.
Proof. unfold left_holds; rewrite Forall_cons_iff. split; [tauto|intro H; split; [exact H|constructor]]. Qed.

Lemma formula_conj tr a b : tr <> [] ->
  (formula_holds M (Conj a b) tr <-> formula_holds M a tr /\ formula_holds M b tr).
Proof. destruct tr; cbn; tauto. Qed.
Lemma formula_disj tr a b : tr <> [] ->
  (formula_holds M (Disj a b) tr <-> formula_holds M a tr \/ formula_holds M b tr).
Proof. destruct tr; cbn; tauto. Qed.
Lemma formula_impl tr a b : tr <> [] ->
  (formula_holds M (Impl a b) tr <-> (formula_holds M a tr -> formula_holds M b tr)).
Proof. destruct tr; cbn; tauto. Qed.
Lemma formula_neg tr a : tr <> [] ->
  (formula_holds M (Neg a) tr <-> ~ formula_holds M a tr).
Proof. destruct tr; cbn; tauto. Qed.

Lemma labelled_neg w l a ta tb : label_admissible M w l ->
  (labelled_holds M w (Occ l (Neg a) ta) <-> ~ labelled_holds M w (Occ l a tb)).
Proof.
  intro Hne; unfold labelled_holds; cbn [occurrence_label occurrence_formula].
  rewrite formula_neg by exact Hne; tauto.
Qed.
Lemma labelled_impl w l a b ta tb tc : label_admissible M w l ->
  (labelled_holds M w (Occ l (Impl a b) ta) <->
   (labelled_holds M w (Occ l a tb) -> labelled_holds M w (Occ l b tc))).
Proof.
  intro Hne; unfold labelled_holds; cbn [occurrence_label occurrence_formula].
  rewrite formula_impl by exact Hne; tauto.
Qed.

(** First examples of the helpers: right conjunction has two singleton
    replacement premises, while left conjunction has one two-occurrence
    replacement premise. Compare disjunction below for the opposite pattern.
    Unchanged context tags are already routed by [local_rule]. *)
Definition conjunction_right (lhs pre post : list occurrence) (l : label) (a b : formula) (tag ta tb : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ l (Conj a b) tag)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[Occ l a ta]; [Occ l b tb]])) : Cyclic.rule_instance.
Proof.
  refine (right_many "And.R" lhs pre post (Occ l (Conj a b) tag)
    [[Occ l a ta]; [Occ l b tb]] Hs Ht _).
  intros w Hne H. pose proof (H [Occ l a ta] ltac:(cbn; auto)) as Ha.
  pose proof (H [Occ l b tb] ltac:(cbn; auto)) as Hb.
  rewrite right_singleton in Ha, Hb. unfold labelled_holds in *; cbn [occurrence_label occurrence_formula] in *.
  rewrite formula_conj by exact Hne; tauto.
Defined.

Definition conjunction_left (pre post rhs : list occurrence) (l : label) (a b : formula) (tag ta tb : option nat)
    (Hs : judgment_wfb (left_conclusion pre post rhs (Occ l (Conj a b) tag)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (left_targets pre post rhs [[Occ l a ta; Occ l b tb]])) : Cyclic.rule_instance.
Proof.
  refine (left_many "And.L" pre post rhs (Occ l (Conj a b) tag)
    [[Occ l a ta; Occ l b tb]] Hs Ht _).
  intros w [Hne H]. cbn [occurrence_label occurrence_formula] in Hne, H.
  rewrite formula_conj in H by exact Hne.
  exists [Occ l a ta; Occ l b tb]; split; [cbn; auto|].
  unfold left_holds; repeat constructor; unfold labelled_holds; cbn [occurrence_label occurrence_formula]; tauto.
Defined.

Definition disjunction_right (lhs pre post : list occurrence) (l : label) (a b : formula) (tag ta tb : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ l (Disj a b) tag)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[Occ l a ta; Occ l b tb]])) : Cyclic.rule_instance.
Proof.
  refine (right_many "Or.R" lhs pre post (Occ l (Disj a b) tag)
    [[Occ l a ta; Occ l b tb]] Hs Ht _).
  intros w Hne H. specialize (H [Occ l a ta; Occ l b tb] ltac:(cbn; auto)).
  rewrite right_cons, right_singleton in H.
  unfold labelled_holds in *; cbn [occurrence_label occurrence_formula] in *; rewrite formula_disj by exact Hne; tauto.
Defined.

Definition disjunction_left (pre post rhs : list occurrence) (l : label) (a b : formula) (tag ta tb : option nat)
    (Hs : judgment_wfb (left_conclusion pre post rhs (Occ l (Disj a b) tag)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (left_targets pre post rhs [[Occ l a ta]; [Occ l b tb]])) : Cyclic.rule_instance.
Proof.
  refine (left_many "Or.L" pre post rhs (Occ l (Disj a b) tag)
    [[Occ l a ta]; [Occ l b tb]] Hs Ht _).
  intros w [Hne H]; cbn [occurrence_label occurrence_formula] in Hne, H; rewrite formula_disj in H by exact Hne.
  destruct H as [Ha|Hb]; [exists [Occ l a ta]|exists [Occ l b tb]];
    split; try (cbn; auto); apply left_singleton; split; assumption.
Defined.

(** Explicit one-premise weakening; neither constructor is an axiom. *)
Definition weakening_right (lhs pre post : list occurrence) (principal : occurrence)
    (Hs : judgment_wfb (right_conclusion lhs pre post principal) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[]])) : Cyclic.rule_instance.
Proof.
  refine (right_many "Wk.R" lhs pre post principal [[]] Hs Ht _).
  intros w Hne Hall. specialize (Hall [] ltac:(cbn; auto)).
  destruct Hall as [o [Hin _]]; inversion Hin.
Defined.

Definition weakening_left (pre post rhs : list occurrence) (principal : occurrence)
    (Hs : judgment_wfb (left_conclusion pre post rhs principal) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (left_targets pre post rhs [[]])) : Cyclic.rule_instance.
Proof.
  refine (left_many "Wk.L" pre post rhs principal [[]] Hs Ht _).
  intros w H; exists []; split; [cbn; auto|constructor].
Defined.

(** Specialize context replacement to one occurrence, then to semantic
    equivalence of formulas or labelled assertions. These helpers establish
    ordinary soundness and retained-context routing; they do not yet route
    a changed principal trace occurrence. *)
Definition right_one (name : string) (lhs pre post : list occurrence) (principal replacement : occurrence)
    (Hs : judgment_wfb (right_conclusion lhs pre post principal) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[replacement]]))
    (Hholds : forall w, label_admissible M w principal.(occurrence_label) ->
      labelled_holds M w replacement -> labelled_holds M w principal) : Cyclic.rule_instance.
Proof.
  refine (right_many name lhs pre post principal [[replacement]] Hs Ht _).
  intros w Hne Hall; apply Hholds; [exact Hne|].
  apply right_singleton. apply Hall; cbn; auto.
Defined.

Definition left_one (name : string) (pre post rhs : list occurrence) (principal replacement : occurrence)
    (Hs : judgment_wfb (left_conclusion pre post rhs principal) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (left_targets pre post rhs [[replacement]]))
    (Hholds : forall w, labelled_holds M w principal -> labelled_holds M w replacement) : Cyclic.rule_instance.
Proof.
  refine (left_many name pre post rhs principal [[replacement]] Hs Ht _).
  intros w Hprincipal; exists [replacement]; split; [cbn; auto|].
  apply left_singleton, Hholds; exact Hprincipal.
Defined.

Definition right_equivalent (name : string) (lhs pre post : list occurrence) (l : label)
    (a b : formula) (ta tb : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ l a ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[Occ l b tb]]))
    (Heq : forall tr, tr <> [] -> (formula_holds M a tr <-> formula_holds M b tr)) : Cyclic.rule_instance.
Proof.
  refine (right_one name lhs pre post (Occ l a ta) (Occ l b tb) Hs Ht _).
  intros w Hne [Ha Hb]; split; [exact Hne|]. cbn in Hb |- *.
  apply Heq; assumption.
Defined.

Definition left_equivalent (name : string) (pre post rhs : list occurrence) (l : label)
    (a b : formula) (ta tb : option nat)
    (Hs : judgment_wfb (left_conclusion pre post rhs (Occ l a ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (left_targets pre post rhs [[Occ l b tb]]))
    (Heq : forall tr, tr <> [] -> (formula_holds M a tr <-> formula_holds M b tr)) : Cyclic.rule_instance.
Proof.
  refine (left_one name pre post rhs (Occ l a ta) (Occ l b tb) Hs Ht _).
  intros w [Hne Ha]; split; [exact Hne|]. cbn in Ha |- *.
  apply Heq; assumption.
Defined.

Definition right_label_equivalent (name : string) (lhs pre post : list occurrence) (principal replacement : occurrence)
    (Hs : judgment_wfb (right_conclusion lhs pre post principal) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[replacement]]))
    (Heq : forall w, labelled_holds M w principal <-> labelled_holds M w replacement) : Cyclic.rule_instance :=
  right_one name lhs pre post principal replacement Hs Ht (fun w Hne H => proj2 (Heq w) H).

Definition left_label_equivalent (name : string) (pre post rhs : list occurrence) (principal replacement : occurrence)
    (Hs : judgment_wfb (left_conclusion pre post rhs principal) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (left_targets pre post rhs [[replacement]]))
    (Heq : forall w, labelled_holds M w principal <-> labelled_holds M w replacement) : Cyclic.rule_instance :=
  left_one name pre post rhs principal replacement Hs Ht (fun w H => proj1 (Heq w) H).

(** The [_base] suffix marks a semantically proved rule before principal
    rank metadata is strengthened. Assignment expands a final state update
    into old/new label components; it does not discard the existing prefix. *)
Definition first_right lhs pre post u sigma body ta tb Hs Ht :=
  right_label_equivalent "First.R" lhs pre post
    (Occ (Join (StateLabel u) sigma) (First body) ta) (Occ (StateLabel u) body tb) Hs Ht
    (fun w => first_label M w u sigma body ta tb).
Definition first_left pre post rhs u sigma body ta tb Hs Ht :=
  left_label_equivalent "First.L" pre post rhs
    (Occ (Join (StateLabel u) sigma) (First body) ta) (Occ (StateLabel u) body tb) Hs Ht
    (fun w => first_label M w u sigma body ta tb).

(** The manuscript's At rule only exposes atoms/equalities at the head.
    [First] above is the separate rule for an explicit singleton observation
    of an arbitrary compound formula. *)
Definition atomb a := match a with Atom _ _ | BinaryAtom _ _ => true | _ => false end.
Lemma atomb_pure a : atomb a = true -> pureb a = true.
Proof. destruct a; cbn; congruence. Qed.
Definition atom_head_right lhs pre post u sigma body ta tb Hs Ht (Ha : atomb body = true) :=
  right_label_equivalent "At.R" lhs pre post
    (Occ (Join (StateLabel u) sigma) body ta) (Occ (StateLabel u) body tb) Hs Ht
    (fun w => atom_head_label M w u sigma body ta tb Ha).
Definition atom_head_left pre post rhs u sigma body ta tb Hs Ht (Ha : atomb body = true) :=
  left_label_equivalent "At.L" pre post rhs
    (Occ (Join (StateLabel u) sigma) body ta) (Occ (StateLabel u) body tb) Hs Ht
    (fun w => atom_head_label M w u sigma body ta tb Ha).

(** A changed principal can be followed only if both occurrences carry tags.
    Valid pairs require nonincrease; progressing pairs additionally require
    strict decrease. The edge also includes all unchanged context pairs. *)
Definition continuation_pairs (a b : occurrence) :=
  match a.(occurrence_tag), b.(occurrence_tag) with
  | Some x, Some y => [(x,y)]
  | _, _ => []
  end.

Definition continuation_edge source target a b (progress : bool) : Cyclic.edge_info :=
  {| Cyclic.edge_valid := retained_pairs source.(succedent) target.(succedent) ++ continuation_pairs a b;
     Cyclic.edge_progress := if progress then continuation_pairs a b else [] |}.

Lemma continuation_edge_respects source target a b progress w :
  judgment_wfb source = true -> judgment_wfb target = true ->
  In a source.(succedent) -> In b target.(succedent) ->
  occurrence_rank b w <= occurrence_rank a w ->
  (progress = true -> occurrence_rank b w < occurrence_rank a w) ->
  Cyclic.respects_edge source target w w (continuation_edge source target a b progress).
Proof.
  intros Hs Ht Ha Hb Hle Hlt; split.
  - intros x y Hin; apply in_app_iff in Hin as [Hret|Hcont].
    + exact (proj1 (retained_edge_respects source target w Hs Ht) x y Hret).
    + unfold continuation_pairs in Hcont.
      destruct (occurrence_tag a) as [ta|] eqn:Hta; [|contradiction].
      destruct (occurrence_tag b) as [tb|] eqn:Htb; [|contradiction].
      destruct Hcont as [Heq|Hno]; [inversion Heq; subst|contradiction].
      unfold LPLTheory.rank. rewrite (rank_context_occ _ _ a _ (wf_unique _ Hs) Ha Hta).
      rewrite (rank_context_occ _ _ b _ (wf_unique _ Ht) Hb Htb). exact Hle.
  - intros x y Hin.
    change (In (x,y) (if progress then continuation_pairs a b else [])) in Hin.
    destruct progress; [|contradiction].
    unfold continuation_pairs in Hin.
    destruct (occurrence_tag a) as [ta|] eqn:Hta; [|contradiction].
    destruct (occurrence_tag b) as [tb|] eqn:Htb; [|contradiction].
    destruct Hin as [Heq|Hno]; [inversion Heq; subst|contradiction].
    unfold LPLTheory.rank. rewrite (rank_context_occ _ _ a _ (wf_unique _ Hs) Ha Hta).
    rewrite (rank_context_occ _ _ b _ (wf_unique _ Ht) Hb Htb). apply Hlt; reflexivity.
Qed.

(** A false sequent has true antecedents and no true succedent, including its
    principal. These lemmas preserve that fact when replacing a false right
    principal by a selected false continuation. *)
Lemma false_right_parts lhs pre post principal w :
  ~ denote M (right_conclusion lhs pre post principal) w ->
  left_holds M w lhs /\ ~ right_holds M w pre /\
  ~ labelled_holds M w principal /\ ~ right_holds M w post.
Proof.
  intro Hfalse; destruct (false_sequent M _ _ Hfalse) as [Ha [Hl Hr]].
  split; [exact Hl|]. repeat split.
  - intros [o [Hin Ho]]; apply (Hr o); cbn; [rewrite in_app_iff; auto|exact Ho].
  - apply (Hr principal); cbn; rewrite in_app_iff; cbn; auto.
  - intros [o [Hin Ho]]; apply (Hr o); cbn; [rewrite in_app_iff; cbn; auto|exact Ho].
Qed.

Lemma false_right_replacement lhs pre post principal replacement w :
  judgment_wfb (right_conclusion lhs pre post replacement) = true ->
  ~ denote M (right_conclusion lhs pre post principal) w ->
  ~ labelled_holds M w replacement ->
  ~ denote M (right_conclusion lhs pre post replacement) w.
Proof.
  intros Hwf Hfalse Hreplacement Htarget.
  destruct (false_right_parts _ _ _ _ _ Hfalse) as [Hl [Hpre [_ Hpost]]].
  pose proof (proj1 (denote_wf _ _ Hwf) Htarget (false_relations M _ _ Hfalse) Hl) as Hright.
  cbn [right_conclusion succedent] in Hright. rewrite right_app, right_cons in Hright. tauto.
Qed.

(** Replace only edge metadata after proving a stronger local counterstep.
    Ordinary local soundness is reused without altering any premise judgment. *)
Definition redecorate (r : Cyclic.rule_instance) (edge_for : judgment -> Cyclic.edge_info)
    (Hstep : forall w, ~ denote M r.(Cyclic.rule_conclusion) w ->
      { k : nat & { p : Cyclic.premise & { w' : world M |
        nth_error r.(Cyclic.rule_premises) k = Some p /\
        ~ denote M p.(Cyclic.premise_judgment) w' /\
        Cyclic.respects_edge r.(Cyclic.rule_conclusion) p.(Cyclic.premise_judgment) w w'
          (edge_for p.(Cyclic.premise_judgment)) } } }) : Cyclic.rule_instance.
Proof.
  refine {| Cyclic.rule_name := r.(Cyclic.rule_name);
    Cyclic.rule_conclusion := r.(Cyclic.rule_conclusion);
    Cyclic.rule_premises := map (fun p => {| Cyclic.premise_judgment := p.(Cyclic.premise_judgment);
      Cyclic.premise_edge := edge_for p.(Cyclic.premise_judgment) |}) r.(Cyclic.rule_premises) |}.
  - intros Hall; apply r.(Cyclic.rule_theorem); intros p Hin w.
    apply (Hall {| Cyclic.premise_judgment := p.(Cyclic.premise_judgment);
      Cyclic.premise_edge := edge_for p.(Cyclic.premise_judgment) |}).
    apply in_map_iff; exists p; auto.
  - intros w Hfalse; destruct (Hstep w Hfalse) as [k [p [w' [Hnth [Hbad Hedge]]]]].
    exists k, {| Cyclic.premise_judgment := p.(Cyclic.premise_judgment);
      Cyclic.premise_edge := edge_for p.(Cyclic.premise_judgment) |}, w'.
    split.
    + rewrite nth_error_map. exact (f_equal (option_map (fun p : Cyclic.premise =>
      {| Cyclic.premise_judgment := p.(Cyclic.premise_judgment);
         Cyclic.premise_edge := edge_for p.(Cyclic.premise_judgment) |})) Hnth).
    + auto.
Defined.

Definition redecorate_sameworld r edge_for
    (Hworld : forall w H, counter_world r w H = w)
    (Hedge : forall w p, In p r.(Cyclic.rule_premises) ->
      ~ denote M r.(Cyclic.rule_conclusion) w -> ~ denote M p.(Cyclic.premise_judgment) w ->
      Cyclic.respects_edge r.(Cyclic.rule_conclusion) p.(Cyclic.premise_judgment) w w
        (edge_for p.(Cyclic.premise_judgment))) : Cyclic.rule_instance.
Proof.
  apply (redecorate r edge_for). intros w Hfalse.
  specialize (Hworld w Hfalse); unfold counter_world in Hworld.
  destruct (r.(Cyclic.rule_counter_step) w Hfalse) as [k [p [w' [Hnth [Hp Hold]]]]].
  cbn in Hworld; subst w'. exists k, p, w; split; [exact Hnth|]; split; [exact Hp|].
  apply Hedge; try assumption; eapply nth_error_In; exact Hnth.
Defined.

Definition finite_selection {A : Type} (xs : list A) (Q : A -> Prop)
    (H : exists x, In x xs /\ Q x) :
    { k : nat & { x : A | nth_error xs k = Some x /\ Q x }}.
Proof.
  induction xs as [|x xs IH].
  - exfalso; destruct H as [x [Hin _]]; inversion Hin.
  - destruct (excluded_middle_informative (Q x)) as [Hx|Hx].
    + exists 0, x; auto.
    + assert (exists y, In y xs /\ Q y) as Htail.
      { destruct H as [y [[->|Hin] Hy]]; [contradiction|eauto]. }
      destruct (IH Htail) as [k [y [Hnth Hy]]]. exists (Datatypes.S k), y; cbn; auto.
Defined.

Lemma nth_principal {A : Type} (pre post : list A) (principal default : A) :
  nth (List.length pre) (pre ++ principal :: post) default = principal.
Proof. induction pre; cbn; auto. Qed.

Lemma wellformed_principal lhs pre post principal w :
  judgment_wfb (right_conclusion lhs pre post principal) = true ->
  label_admissible M w principal.(occurrence_label).
Proof.
  intro Hwf; pose proof (judgment_wfb_admissible M _ w Hwf) as Ha.
  unfold admissible in Ha; rewrite Forall_forall in Ha; apply Ha.
  cbn; rewrite !in_app_iff; cbn; tauto.
Qed.

(** Strengthen a proved right rule with its principal rank pair. [Hselect]
    chooses one premise once, so all advertised context and principal pairs
    are respected on that same edge. *)
Definition enhance_right (r : Cyclic.rule_instance) lhs pre post principal replacements progress
    (Hs : judgment_wfb (right_conclusion lhs pre post principal) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      (right_targets lhs pre post (map (fun o => [o]) replacements)))
    (Hsource : r.(Cyclic.rule_conclusion) = right_conclusion lhs pre post principal)
    (Hshape : map Cyclic.premise_judgment r.(Cyclic.rule_premises) =
      right_targets lhs pre post (map (fun o => [o]) replacements))
    (Hselect : forall w, label_admissible M w principal.(occurrence_label) ->
      ~ labelled_holds M w principal -> exists replacement,
        In replacement replacements /\ ~ labelled_holds M w replacement /\
        occurrence_rank replacement w <= occurrence_rank principal w /\
        (progress = true -> occurrence_rank replacement w < occurrence_rank principal w))
    : Cyclic.rule_instance.
Proof.
  (* Select a replacement together with its falsity and rank bounds before
     choosing the premise record. The resulting single edge respects every
     context pair and the principal pair at the same world. *)
  set (edge_for := fun target => continuation_edge r.(Cyclic.rule_conclusion) target principal
    (nth (List.length pre) target.(succedent) principal) progress).
  apply (redecorate r edge_for). intros w Hfalse.
  rewrite Hsource in Hfalse.
  destruct (false_right_parts _ _ _ _ _ Hfalse) as [_ [_ [Hprincipal _]]].
  destruct (finite_selection replacements
    (fun replacement => ~ labelled_holds M w replacement /\
      occurrence_rank replacement w <= occurrence_rank principal w /\
      (progress = true -> occurrence_rank replacement w < occurrence_rank principal w))
    (Hselect w (wellformed_principal _ _ _ _ w Hs) Hprincipal))
    as [replacement_index [replacement [Hreplacement [Hbad [Hle Hlt]]]]].
  assert (In replacement replacements) as Hin by (eapply nth_error_In; exact Hreplacement).
  set (target := right_conclusion lhs pre post replacement).
  assert (In target (right_targets lhs pre post (map (fun o => [o]) replacements))) as Hmember.
  { unfold right_targets, target, right_conclusion. apply in_map_iff.
    exists [replacement]; split; [reflexivity|]. apply in_map_iff; exists replacement; auto. }
  assert (judgment_wfb target = true) as Htarget.
  { rewrite Forall_forall in Ht; apply Ht; exact Hmember. }
  assert (exists p, In p r.(Cyclic.rule_premises) /\
    ~ denote M p.(Cyclic.premise_judgment) w /\
    Cyclic.respects_edge r.(Cyclic.rule_conclusion) p.(Cyclic.premise_judgment) w w
      (edge_for p.(Cyclic.premise_judgment))) as Hex.
  { rewrite <- Hshape in Hmember; apply in_map_iff in Hmember as [p [Hpj Hp]].
    exists p; split; [exact Hp|]. rewrite Hpj; split.
    - apply (false_right_replacement lhs pre post principal replacement w Htarget Hfalse Hbad).
    - unfold edge_for; rewrite Hsource. unfold target; cbn [right_conclusion succedent].
      rewrite nth_principal. apply continuation_edge_respects; try assumption;
        cbn [right_conclusion succedent]; rewrite in_app_iff; cbn; auto. }
  destruct (finite_selection r.(Cyclic.rule_premises)
    (fun p => ~ denote M p.(Cyclic.premise_judgment) w /\
      Cyclic.respects_edge r.(Cyclic.rule_conclusion) p.(Cyclic.premise_judgment) w w
        (edge_for p.(Cyclic.premise_judgment))) Hex) as [k [p [Hnth [Hp He]]]].
  exists k, p, w; auto.
Defined.

Definition box_sequence_right_base lhs pre post l a b body ta tb Hs Ht :=
  right_equivalent "B.Seq.R" lhs pre post l (Box (Seq a b) body) (Box a (Box b body)) ta tb Hs Ht
    (fun tr Hne => box_sequence M a b body tr Hne).

Definition box_sequence_left pre post rhs l a b body ta tb Hs Ht :=
  left_equivalent "B.Seq.L" pre post rhs l (Box (Seq a b) body) (Box a (Box b body)) ta tb Hs Ht
    (fun tr Hne => box_sequence M a b body tr Hne).

Definition right_two_equivalent (name : string) (lhs pre post : list occurrence) (l : label)
    (a b c : formula) (ta tb tc : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ l a ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[Occ l b tb];[Occ l c tc]]))
    (Heq : forall tr, tr <> [] -> (formula_holds M a tr <-> formula_holds M b tr /\ formula_holds M c tr))
    : Cyclic.rule_instance.
Proof.
  refine (right_many name lhs pre post (Occ l a ta) [[Occ l b tb];[Occ l c tc]] Hs Ht _).
  intros w Hne Hall. split; [exact Hne|]. cbn [occurrence_formula occurrence_label]. apply Heq; [exact Hne|].
  split; [specialize (Hall [Occ l b tb] ltac:(cbn; auto))|specialize (Hall [Occ l c tc] ltac:(cbn; auto))];
    apply right_singleton in Hall; exact (proj2 Hall).
Defined.

(** Preserve the catalog's two-premise left box-choice/star schemes. A true
    conjunctive principal makes either singleton replacement true; choosing
    the first suffices for the local soundness proof because both premises
    are assumed valid. This is the specified rule, not a one-premise rewrite
    that inserts both conjuncts into the antecedent. *)
Definition left_two_conjunctive (name : string) (pre post rhs : list occurrence) (l : label)
    (a b c : formula) (ta tb tc : option nat)
    (Hs : judgment_wfb (left_conclusion pre post rhs (Occ l a ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (left_targets pre post rhs [[Occ l b tb];[Occ l c tc]]))
    (Heq : forall tr, tr <> [] -> (formula_holds M a tr <-> formula_holds M b tr /\ formula_holds M c tr))
    : Cyclic.rule_instance.
Proof.
  refine (left_many name pre post rhs (Occ l a ta) [[Occ l b tb];[Occ l c tc]] Hs Ht _).
  intros w [Hne Ha]. exists [Occ l b tb]; split; [cbn; auto|].
  apply left_singleton; split; [exact Hne|].
  apply (proj1 (Heq _ Hne)) in Ha; exact (proj1 Ha).
Defined.

Definition box_choice_right_base lhs pre post l a b body ta tb tc Hs Ht :=
  right_two_equivalent "B.Choice.R" lhs pre post l (Box (Choice a b) body) (Box a body) (Box b body)
    ta tb tc Hs Ht (fun tr Hne => box_choice M a b body tr Hne).
Definition box_choice_left pre post rhs l a b body ta tb tc Hs Ht :=
  left_two_conjunctive "B.Choice.L" pre post rhs l (Box (Choice a b) body) (Box a body) (Box b body)
    ta tb tc Hs Ht (fun tr Hne => box_choice M a b body tr Hne).
Definition box_star_right_base lhs pre post l a body ta tb tc Hs Ht :=
  right_two_equivalent "B.Star.R" lhs pre post l (Box (Star a) body) (Box (Test Truth) body) (Box a (Box (Star a) body))
    ta tb tc Hs Ht (fun tr Hne => box_star M a body tr Hne).
Definition box_star_left pre post rhs l a body ta tb tc Hs Ht :=
  left_two_conjunctive "B.Star.L" pre post rhs l (Box (Star a) body) (Box (Test Truth) body) (Box a (Box (Star a) body))
    ta tb tc Hs Ht (fun tr Hne => box_star M a body tr Hne).

(** Public traced box rules. Sequence, choice and star only preserve or
    decrease rank weakly; assignment proves strict decrease. In each call
    to [enhance_right], its final Boolean records this distinction. A missing
    continuation tag still produces no principal pair. *)
Definition box_sequence_right (lhs pre post : list occurrence) (l : label) (a b : program) (body : formula)
    (ta tb : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ l (Box (Seq a b) body) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      (right_targets lhs pre post [[Occ l (Box a (Box b body)) tb]])) : Cyclic.rule_instance.
Proof.
  refine (enhance_right (box_sequence_right_base lhs pre post l a b body ta tb Hs Ht)
    lhs pre post (Occ l (Box (Seq a b) body) ta) [Occ l (Box a (Box b body)) tb] false
    Hs Ht eq_refl eq_refl _).
  intros w Hne Hbad.
  assert (~ formula_holds M (Box (Seq a b) body) (eval_label M w l)) as Hfalse.
  { intro H; apply Hbad; split; assumption. }
  destruct (sequence_nonincrease _ _ _ _ Hne Hfalse) as [Hbad' Hrank].
  exists (Occ l (Box a (Box b body)) tb); split; [cbn; auto|].
  split; [intros [_ H]; exact (Hbad' H)|]. split; [exact Hrank|discriminate].
Defined.

Definition box_choice_right (lhs pre post : list occurrence) (l : label) (a b : program) (body : formula)
    (ta tb tc : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ l (Box (Choice a b) body) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      (right_targets lhs pre post [[Occ l (Box a body) tb];[Occ l (Box b body) tc]])) : Cyclic.rule_instance.
Proof.
  refine (enhance_right (box_choice_right_base lhs pre post l a b body ta tb tc Hs Ht)
    lhs pre post (Occ l (Box (Choice a b) body) ta) [Occ l (Box a body) tb;Occ l (Box b body) tc] false
    Hs Ht eq_refl eq_refl _).
  intros w Hne Hbad.
  assert (~ formula_holds M (Box (Choice a b) body) (eval_label M w l)) as Hfalse.
  { intro H; apply Hbad; split; assumption. }
  destruct (choice_nonincrease (eval_label M w l) a b body Hne Hfalse) as [[Hbad' Hrank]|[Hbad' Hrank]];
    [exists (Occ l (Box a body) tb)|exists (Occ l (Box b body) tc)];
    split; try (cbn; auto); split; try (intros [_ H]; exact (Hbad' H));
    split; [exact Hrank|discriminate|exact Hrank|discriminate].
Defined.

Definition box_star_right (lhs pre post : list occurrence) (l : label) (a : program) (body : formula)
    (ta tb tc : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ l (Box (Star a) body) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      (right_targets lhs pre post [[Occ l (Box (Test Truth) body) tb];[Occ l (Box a (Box (Star a) body)) tc]])) : Cyclic.rule_instance.
Proof.
  refine (enhance_right (box_star_right_base lhs pre post l a body ta tb tc Hs Ht)
    lhs pre post (Occ l (Box (Star a) body) ta) [Occ l (Box (Test Truth) body) tb;Occ l (Box a (Box (Star a) body)) tc] false
    Hs Ht eq_refl eq_refl _).
  intros w Hne Hbad.
  assert (~ formula_holds M (Box (Star a) body) (eval_label M w l)) as Hfalse.
  { intro H; apply Hbad; split; assumption. }
  destruct (star_nonincrease (eval_label M w l) a body Hne Hfalse) as [[Hbad' Hrank]|[Hbad' Hrank]];
    [exists (Occ l (Box (Test Truth) body) tb)|exists (Occ l (Box a (Box (Star a) body)) tc)];
    split; try (cbn; auto); split; try (intros [_ H]; exact (Hbad' H));
    split; [exact Hrank|discriminate|exact Hrank|discriminate].
Defined.

(** Negation/implication can move an assertion across the sequent. Only
    unchanged succedent context occurrences retain trace pairs; truth
    equivalence by itself does not justify tracing through a side change. *)
Definition negation_right lhs pre post l a ta tb Hs Ht :=
  local_rule "Not.R" (right_conclusion lhs pre post (Occ l (Neg a) ta))
    [Jdg (lhs ++ [Occ l a tb]) (pre ++ post)] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall _ (or_introl eq_refl)) as H;
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) H) as Hraw;
      apply (proj2 (denote_wf _ w Hs)); cbn [right_conclusion antecedent succedent] in *;
      rewrite left_app, left_singleton, right_app in Hraw;
      rewrite right_app, right_cons;
      rewrite (labelled_neg w l a ta tb (wellformed_principal _ _ _ _ w Hs)); tauto)).

Lemma wellformed_left_principal pre post rhs principal w :
  judgment_wfb (left_conclusion pre post rhs principal) = true ->
  label_admissible M w principal.(occurrence_label).
Proof.
  intro Hwf; pose proof (judgment_wfb_admissible M _ w Hwf) as Ha.
  unfold admissible in Ha; rewrite Forall_forall in Ha; apply Ha.
  cbn; rewrite !in_app_iff; cbn; tauto.
Qed.

Definition negation_left pre post rhs l a ta tb Hs Ht :=
  local_rule "Not.L" (left_conclusion pre post rhs (Occ l (Neg a) ta))
    [Jdg (pre ++ post) (Occ l a tb :: rhs)] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall _ (or_introl eq_refl)) as H;
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) H) as Hraw;
      apply (proj2 (denote_wf _ w Hs)); cbn [left_conclusion antecedent succedent] in *;
      rewrite left_app, right_cons in Hraw;
      rewrite left_app, left_cons;
      rewrite (labelled_neg w l a ta tb (wellformed_left_principal _ _ _ _ w Hs)); tauto)).

Definition implication_right lhs pre post l a b ta tb tc Hs Ht :=
  local_rule "Impl.R" (right_conclusion lhs pre post (Occ l (Impl a b) ta))
    [Jdg (lhs ++ [Occ l a tb]) (pre ++ Occ l b tc :: post)] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall _ (or_introl eq_refl)) as H;
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) H) as Hraw;
      apply (proj2 (denote_wf _ w Hs)); cbn [right_conclusion antecedent succedent] in *;
      rewrite left_app, left_singleton, right_app, right_cons in Hraw;
      rewrite right_app, right_cons;
      rewrite (labelled_impl w l a b ta tb tc (wellformed_principal _ _ _ _ w Hs)); tauto)).

Definition implication_left pre post rhs l a b ta tb tc Hs Ht :=
  local_rule "Impl.L" (left_conclusion pre post rhs (Occ l (Impl a b) ta))
    [Jdg (pre ++ post) (Occ l a tb :: rhs); Jdg (pre ++ Occ l b tc :: post) rhs] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall _ (or_introl eq_refl)) as H1;
      pose proof (Hall _ (or_intror (or_introl eq_refl))) as H2;
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) H1) as R1;
      pose proof (proj1 (denote_wf _ w (Forall_inv (Forall_inv_tail Ht))) H2) as R2;
      apply (proj2 (denote_wf _ w Hs)); cbn [left_conclusion antecedent succedent] in *;
      rewrite left_app, right_cons in R1;
      rewrite left_app, left_cons in R2;
      rewrite left_app, left_cons;
      rewrite (labelled_impl w l a b ta tb tc (wellformed_left_principal _ _ _ _ w Hs)); tauto)).

(** A successful test observes its guard on the two-state stutter at [u].
    For box-right that guard is an antecedent assumption; the specified
    box-left and diamond schemes place/remove guard occurrences explicitly.
    The accumulated body label gains the second copy of the test state. *)
Definition box_test_right_base lhs pre post sigma u guard body ta tb Hs Ht :=
  local_rule "B.Test.R"
    (right_conclusion lhs pre post (Occ (Join sigma (StateLabel u)) (Box (Test guard) body) ta))
    [Jdg (lhs ++ [Occ (Join (StateLabel u) (StateLabel u)) guard None])
      (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb :: post)] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall _ (or_introl eq_refl)) as H;
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) H) as Hraw;
      apply (proj2 (denote_wf _ w Hs)); cbn [right_conclusion antecedent succedent] in *;
      rewrite left_app, left_singleton, right_app, right_cons in Hraw;
      rewrite right_app, right_cons, (box_test_label M w sigma u guard body ta tb None); tauto)).

Definition box_test_left pre post rhs sigma u guard body ta tb Hs Ht :=
  local_rule "B.Test.L"
    (Jdg (pre ++ Occ (Join sigma (StateLabel u)) (Box (Test guard) body) ta ::
      Occ (Join (StateLabel u) (StateLabel u)) guard None :: post) rhs)
    [Jdg (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb :: post) rhs] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall _ (or_introl eq_refl)) as H;
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) H) as Hraw;
      apply (proj2 (denote_wf _ w Hs)); cbn [antecedent succedent] in *;
      rewrite left_app, left_cons in Hraw;
      rewrite left_app, !left_cons, (box_test_label M w sigma u guard body ta tb None); tauto)).

Definition diamond_test_right lhs pre post sigma u guard body ta tb Hs Ht :=
  local_rule "D.Test.R"
    (right_conclusion (lhs ++ [Occ (Join (StateLabel u) (StateLabel u)) guard None]) pre post
      (Occ (Join sigma (StateLabel u)) (Diamond (Test guard) body) ta))
    [Jdg lhs (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb :: post)] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall _ (or_introl eq_refl)) as H;
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) H) as Hraw;
      apply (proj2 (denote_wf _ w Hs)); cbn [right_conclusion antecedent succedent] in *;
      rewrite right_app, right_cons in Hraw;
      rewrite left_app, left_singleton, right_app, right_cons,
        (diamond_test_label M w sigma u guard body ta tb None); tauto)).

Definition diamond_test_left pre post rhs sigma u guard body ta tb Hs Ht :=
  local_rule "D.Test.L"
    (left_conclusion pre post rhs (Occ (Join sigma (StateLabel u)) (Diamond (Test guard) body) ta))
    [Jdg (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb ::
      Occ (Join (StateLabel u) (StateLabel u)) guard None :: post) rhs] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall _ (or_introl eq_refl)) as H;
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) H) as Hraw;
      apply (proj2 (denote_wf _ w Hs)); cbn [left_conclusion antecedent succedent] in *;
      rewrite left_app, !left_cons in Hraw;
      rewrite left_app, left_cons, (diamond_test_label M w sigma u guard body ta tb None); tauto)).

(** Diamonds use the existential program equations. They are public formula
    constructors and have their own rules, but are not traceable principals
    under this logic's tag policy; only unchanged context traces are routed. *)
Definition diamond_sequence_right lhs pre post l a b body ta tb Hs Ht :=
  right_equivalent "D.Seq.R" lhs pre post l (Diamond (Seq a b) body) (Diamond a (Diamond b body)) ta tb Hs Ht
    (fun tr Hne => diamond_sequence M a b body tr Hne).
Definition diamond_sequence_left pre post rhs l a b body ta tb Hs Ht :=
  left_equivalent "D.Seq.L" pre post rhs l (Diamond (Seq a b) body) (Diamond a (Diamond b body)) ta tb Hs Ht
    (fun tr Hne => diamond_sequence M a b body tr Hne).

Definition right_two_disjunctive (name : string) (lhs pre post : list occurrence) (l : label)
    (a b c : formula) (ta tb tc : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ l a ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[Occ l b tb; Occ l c tc]]))
    (Heq : forall tr, tr <> [] -> (formula_holds M a tr <-> formula_holds M b tr \/ formula_holds M c tr))
    : Cyclic.rule_instance.
Proof.
  refine (right_many name lhs pre post (Occ l a ta) [[Occ l b tb; Occ l c tc]] Hs Ht _).
  intros w Hne Hall. specialize (Hall _ (or_introl eq_refl)); rewrite right_cons, right_singleton in Hall.
  split; [exact Hne|]. cbn [occurrence_formula occurrence_label].
  apply Heq; [exact Hne|]. destruct Hall as [[_ H]|[_ H]]; auto.
Defined.

Definition left_two_disjunctive (name : string) (pre post rhs : list occurrence) (l : label)
    (a b c : formula) (ta tb tc : option nat)
    (Hs : judgment_wfb (left_conclusion pre post rhs (Occ l a ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (left_targets pre post rhs [[Occ l b tb];[Occ l c tc]]))
    (Heq : forall tr, tr <> [] -> (formula_holds M a tr <-> formula_holds M b tr \/ formula_holds M c tr))
    : Cyclic.rule_instance.
Proof.
  refine (left_many name pre post rhs (Occ l a ta) [[Occ l b tb];[Occ l c tc]] Hs Ht _).
  intros w [Hne Ha]. apply (proj1 (Heq _ Hne)) in Ha.
  destruct Ha as [Hb|Hc]; [exists [Occ l b tb]|exists [Occ l c tc]];
    split; try (cbn; auto); apply left_singleton; split; assumption.
Defined.

Definition diamond_choice_right lhs pre post l a b body ta tb tc Hs Ht :=
  right_two_disjunctive "D.Choice.R" lhs pre post l (Diamond (Choice a b) body) (Diamond a body) (Diamond b body)
    ta tb tc Hs Ht (fun tr Hne => diamond_choice M a b body tr Hne).
Definition diamond_choice_left pre post rhs l a b body ta tb tc Hs Ht :=
  left_two_disjunctive "D.Choice.L" pre post rhs l (Diamond (Choice a b) body) (Diamond a body) (Diamond b body)
    ta tb tc Hs Ht (fun tr Hne => diamond_choice M a b body tr Hne).
Definition diamond_star_right lhs pre post l a body ta tb tc Hs Ht :=
  right_two_disjunctive "D.Star.R" lhs pre post l (Diamond (Star a) body) (Diamond (Test Truth) body)
    (Diamond a (Diamond (Star a) body)) ta tb tc Hs Ht (fun tr Hne => diamond_star M a body tr Hne).
Definition diamond_star_left pre post rhs l a body ta tb tc Hs Ht :=
  left_two_disjunctive "D.Star.L" pre post rhs l (Diamond (Star a) body) (Diamond (Test Truth) body)
    (Diamond a (Diamond (Star a) body)) ta tb tc Hs Ht (fun tr Hne => diamond_star M a body tr Hne).

(** The one-step suffix laws apply after exposing an initial state and a
    nonempty tail. Keep the exact two ordered premises from the catalog;
    the right rules' first premises contain no recursive principal. *)
Definition suffix_right_base (lhs pre post : list occurrence) (u : L.world_term) (sigma : label) (a b : formula)
    (ta tb tc td : option nat) (Htail : label_nonemptyb sigma = true)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) (Suffix a b) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      (right_targets lhs pre post [[Occ sigma b tb; Occ sigma a tc];[Occ sigma b tb; Occ sigma (Suffix a b) td]]))
    : Cyclic.rule_instance.
Proof.
  refine (right_many "Suffix.R" lhs pre post (Occ (Join (StateLabel u) sigma) (Suffix a b) ta)
    [[Occ sigma b tb; Occ sigma a tc];[Occ sigma b tb; Occ sigma (Suffix a b) td]] Hs Ht _).
  intros w Hne Hall.
  pose proof (Hall _ (or_introl eq_refl)) as H1.
  pose proof (Hall _ (or_intror (or_introl eq_refl))) as H2.
  rewrite right_cons, right_singleton in H1, H2.
  apply (proj2 (suffix_label M w u sigma a b ta tb tc td Htail)); tauto.
Defined.

Definition suffix_left (pre post rhs : list occurrence) (u : L.world_term) (sigma : label) (a b : formula)
    (ta tb tc td : option nat) (Htail : label_nonemptyb sigma = true)
    (Hs : judgment_wfb (left_conclusion pre post rhs (Occ (Join (StateLabel u) sigma) (Suffix a b) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      (left_targets pre post rhs [[Occ sigma b tb];[Occ sigma a tc; Occ sigma (Suffix a b) td]]))
    : Cyclic.rule_instance.
Proof.
  refine (left_many "Suffix.L" pre post rhs (Occ (Join (StateLabel u) sigma) (Suffix a b) ta)
    [[Occ sigma b tb];[Occ sigma a tc; Occ sigma (Suffix a b) td]] Hs Ht _).
  intros w H. apply (proj1 (suffix_label M w u sigma a b ta tb tc td Htail)) in H.
  destruct H as [Hb|[Ha Hsuf]].
  - exists [Occ sigma b tb]; split; [cbn; auto|]. apply left_singleton; exact Hb.
  - exists [Occ sigma a tc; Occ sigma (Suffix a b) td]; split; [cbn; auto|].
    rewrite left_cons, left_singleton; auto.
Defined.

Definition dual_suffix_right_base (lhs pre post : list occurrence) (u : L.world_term) (sigma : label) (a b : formula)
    (ta tb tc td : option nat) (Htail : label_nonemptyb sigma = true)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      (right_targets lhs pre post [[Occ sigma b tb];[Occ sigma a tc; Occ sigma (DualSuffix a b) td]]))
    : Cyclic.rule_instance.
Proof.
  refine (right_many "DualSuffix.R" lhs pre post (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta)
    [[Occ sigma b tb];[Occ sigma a tc; Occ sigma (DualSuffix a b) td]] Hs Ht _).
  intros w Hne Hall.
  pose proof (Hall _ (or_introl eq_refl)) as H1.
  pose proof (Hall _ (or_intror (or_introl eq_refl))) as H2.
  rewrite right_singleton in H1. rewrite right_cons, right_singleton in H2.
  apply (proj2 (dual_suffix_label M w u sigma a b ta tb tc td Htail)); tauto.
Defined.

Definition dual_suffix_left (pre post rhs : list occurrence) (u : L.world_term) (sigma : label) (a b : formula)
    (ta tb tc td : option nat) (Htail : label_nonemptyb sigma = true)
    (Hs : judgment_wfb (left_conclusion pre post rhs (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      (left_targets pre post rhs [[Occ sigma b tb; Occ sigma a tc];[Occ sigma b tb; Occ sigma (DualSuffix a b) td]]))
    : Cyclic.rule_instance.
Proof.
  refine (left_many "DualSuffix.L" pre post rhs (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta)
    [[Occ sigma b tb; Occ sigma a tc];[Occ sigma b tb; Occ sigma (DualSuffix a b) td]] Hs Ht _).
  intros w H. apply (proj1 (dual_suffix_label M w u sigma a b ta tb tc td Htail)) in H.
  destruct H as [Hb [Ha|Hsuf]].
  - exists [Occ sigma b tb; Occ sigma a tc]; split; [cbn; auto|].
    rewrite left_cons, left_singleton; auto.
  - exists [Occ sigma b tb; Occ sigma (DualSuffix a b) td]; split; [cbn; auto|].
    rewrite left_cons, left_singleton; auto.
Defined.

(** A proper suffix cannot exist on a singleton label. Such an antecedent
    makes the sequent valid directly, so this is an axiom rather than a rule
    with an invented successor or trace continuation. *)
Definition suffix_singleton_axiom j (Hwf : judgment_wfb j = true) o u a b
    (Hin : In o j.(antecedent)) (Hl : o.(occurrence_label) = StateLabel u)
    (Hf : o.(occurrence_formula) = Suffix a b) : Cyclic.axiom_instance.
Proof.
  refine {| Cyclic.axiom_name := "Suffix.singleton"; Cyclic.axiom_conclusion := j |}.
  intros w Hadm Hrelations Hleft. unfold left_holds in Hleft; rewrite Forall_forall in Hleft.
  specialize (Hleft o Hin). destruct Hleft as [_ Hfalse]. rewrite Hl, Hf in Hfalse.
  exfalso; exact (suffix_singleton M a b (eval_update M w u) Hfalse).
Defined.

Lemma false_succedent j w o : In o j.(succedent) -> ~ denote M j w -> ~ labelled_holds M w o.
Proof. intros Hin Hfalse; exact (proj2 (proj2 (false_sequent M j w Hfalse)) o Hin). Qed.
Lemma wf_occurrence_admissible j w o : judgment_wfb j = true ->
  In o (j.(antecedent) ++ j.(succedent)) -> label_admissible M w o.(occurrence_label).
Proof.
  intros Hwf Hin; pose proof (judgment_wfb_admissible M j w Hwf) as H;
    unfold admissible in H; rewrite Forall_forall in H; apply H; exact Hin.
Qed.

Lemma continuing_false_edge source target principal replacement w :
  judgment_wfb source = true -> judgment_wfb target = true ->
  In principal source.(succedent) -> In replacement target.(succedent) ->
  (forall w, label_admissible M w principal.(occurrence_label) ->
    label_admissible M w replacement.(occurrence_label) ->
    ~ labelled_holds M w principal -> ~ labelled_holds M w replacement ->
    occurrence_rank replacement w < occurrence_rank principal w) ->
  ~ denote M source w -> ~ denote M target w ->
  Cyclic.respects_edge source target w w (continuation_edge source target principal replacement true).
Proof.
  intros Hs Ht Hprincipal Hreplacement Hrank Hfalse Htargetfalse.
  assert (occurrence_rank replacement w < occurrence_rank principal w) as Hstrict.
  { apply Hrank.
    - eapply wf_occurrence_admissible; [exact Hs|apply in_app_iff; now right].
    - eapply wf_occurrence_admissible; [exact Ht|apply in_app_iff; now right].
    - eapply false_succedent; eauto.
    - eapply false_succedent; eauto. }
  apply continuation_edge_respects; try assumption; lia.
Qed.

Lemma suffix_pair_strict u sigma a b ta td w :
  label_admissible M w (Join (StateLabel u) sigma) -> label_admissible M w sigma ->
  ~ labelled_holds M w (Occ (Join (StateLabel u) sigma) (Suffix a b) ta) ->
  ~ labelled_holds M w (Occ sigma (Suffix a b) td) ->
  occurrence_rank (Occ sigma (Suffix a b) td) w <
  occurrence_rank (Occ (Join (StateLabel u) sigma) (Suffix a b) ta) w.
Proof.
  intros Hsrc Htail Hbad Hbad'; apply suffix_decrease; [exact Htail| |];
    intro H; first [apply Hbad; split; assumption|apply Hbad'; split; assumption].
Qed.
Lemma dual_suffix_pair_strict u sigma a b ta td w :
  label_admissible M w (Join (StateLabel u) sigma) -> label_admissible M w sigma ->
  ~ labelled_holds M w (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta) ->
  ~ labelled_holds M w (Occ sigma (DualSuffix a b) td) ->
  occurrence_rank (Occ sigma (DualSuffix a b) td) w <
  occurrence_rank (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta) w.
Proof.
  intros Hsrc Htail Hbad Hbad'; apply dual_suffix_decrease; [exact Htail| |];
    intro H; first [apply Hbad; split; assumption|apply Hbad'; split; assumption].
Qed.

(** Upgrade only the continuing right-suffix edge to strict principal
    progress. The other premise receives retained context pairs alone.
    [redecorate_sameworld] reuses the base rule's selected false premise,
    and the local edge proof handles whichever premise it selected. *)
Definition suffix_right (lhs pre post : list occurrence) (u : L.world_term) (sigma : label) (a b : formula)
    (ta tb tc td : option nat) (Htail : label_nonemptyb sigma = true)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) (Suffix a b) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[Occ sigma b tb;Occ sigma a tc];[Occ sigma b tb;Occ sigma (Suffix a b) td]])) : Cyclic.rule_instance.
Proof.
  set (base := suffix_right_base lhs pre post u sigma a b ta tb tc td Htail Hs Ht).
  set (source := right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) (Suffix a b) ta)).
  set (continuing := Jdg lhs (pre ++ [Occ sigma b tb;Occ sigma (Suffix a b) td] ++ post)).
  set (edge_for := fun target => if judgment_eqb target continuing then
    continuation_edge source target (Occ (Join (StateLabel u) sigma) (Suffix a b) ta)
      (Occ sigma (Suffix a b) td) true else retained_edge source target).
  apply (redecorate_sameworld base edge_for).
  - intros w H; apply local_rule_world.
  - intros w p Hin Hfalse Htargetfalse.
    assert (judgment_wfb p.(Cyclic.premise_judgment) = true) as Htargetwf.
    { change (In p [{| Cyclic.premise_judgment := Jdg lhs (pre ++ [Occ sigma b tb;Occ sigma a tc] ++ post);
       Cyclic.premise_edge := retained_edge source (Jdg lhs (pre ++ [Occ sigma b tb;Occ sigma a tc] ++ post)) |};
       {| Cyclic.premise_judgment := continuing; Cyclic.premise_edge := retained_edge source continuing |}]) in Hin.
      destruct Hin as [Heq|[Heq|Hno]]; [subst p; exact (Forall_inv Ht)|subst p; exact (Forall_inv (Forall_inv_tail Ht))|contradiction]. }
    unfold edge_for. destruct (judgment_eqb p.(Cyclic.premise_judgment) continuing) eqn:Heq.
    + apply judgment_eqb_spec in Heq; rewrite Heq in *.
      apply continuing_false_edge; try assumption.
      * unfold source; cbn [right_conclusion succedent]; apply in_app_iff; cbn; auto.
      * unfold continuing; cbn; apply in_app_iff; cbn; auto.
      * exact (suffix_pair_strict u sigma a b ta td).
    + apply retained_edge_respects; assumption.
Defined.

Definition dual_suffix_right (lhs pre post : list occurrence) (u : L.world_term) (sigma : label) (a b : formula)
    (ta tb tc td : option nat) (Htail : label_nonemptyb sigma = true)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true) (right_targets lhs pre post [[Occ sigma b tb];[Occ sigma a tc;Occ sigma (DualSuffix a b) td]])) : Cyclic.rule_instance.
Proof.
  set (base := dual_suffix_right_base lhs pre post u sigma a b ta tb tc td Htail Hs Ht).
  set (source := right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta)).
  set (continuing := Jdg lhs (pre ++ [Occ sigma a tc;Occ sigma (DualSuffix a b) td] ++ post)).
  set (edge_for := fun target => if judgment_eqb target continuing then
    continuation_edge source target (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta)
      (Occ sigma (DualSuffix a b) td) true else retained_edge source target).
  apply (redecorate_sameworld base edge_for).
  - intros w H; apply local_rule_world.
  - intros w p Hin Hfalse Htargetfalse.
    assert (judgment_wfb p.(Cyclic.premise_judgment) = true) as Htargetwf.
    { change (In p [{| Cyclic.premise_judgment := Jdg lhs (pre ++ [Occ sigma b tb] ++ post);
       Cyclic.premise_edge := retained_edge source (Jdg lhs (pre ++ [Occ sigma b tb] ++ post)) |};
       {| Cyclic.premise_judgment := continuing; Cyclic.premise_edge := retained_edge source continuing |}]) in Hin.
      destruct Hin as [Heq|[Heq|Hno]]; [subst p; exact (Forall_inv Ht)|subst p; exact (Forall_inv (Forall_inv_tail Ht))|contradiction]. }
    unfold edge_for. destruct (judgment_eqb p.(Cyclic.premise_judgment) continuing) eqn:Heq.
    + apply judgment_eqb_spec in Heq; rewrite Heq in *.
      apply continuing_false_edge; try assumption.
      * unfold source; cbn [right_conclusion succedent]; apply in_app_iff; cbn; auto.
      * unfold continuing; cbn; apply in_app_iff; cbn; auto.
      * exact (dual_suffix_pair_strict u sigma a b ta td).
    + apply retained_edge_respects; assumption.
Defined.

(** A test also gives strict principal descent, now with a guard added to
    the premise antecedent. This needs the test-specific minimum theorem,
    rather than merely treating a repeated state as unchanged syntax. *)
Definition box_test_right (lhs pre post : list occurrence) (sigma : label) (u : L.world_term) (guard body : formula)
    (ta tb : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ (Join sigma (StateLabel u)) (Box (Test guard) body) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      [Jdg (lhs ++ [Occ (Join (StateLabel u) (StateLabel u)) guard None])
        (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb :: post)]) : Cyclic.rule_instance.
Proof.
  set (base := box_test_right_base lhs pre post sigma u guard body ta tb Hs Ht).
  set (source := right_conclusion lhs pre post (Occ (Join sigma (StateLabel u)) (Box (Test guard) body) ta)).
  set (edge_for := fun target => continuation_edge source target
    (Occ (Join sigma (StateLabel u)) (Box (Test guard) body) ta)
    (Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb) true).
  apply (redecorate_sameworld base edge_for).
  - intros w H; apply local_rule_world.
  - intros w p Hin Hfalse Htargetfalse.
    change (In p [{| Cyclic.premise_judgment := Jdg (lhs ++ [Occ (Join (StateLabel u) (StateLabel u)) guard None])
      (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb :: post);
      Cyclic.premise_edge := retained_edge source (Jdg (lhs ++ [Occ (Join (StateLabel u) (StateLabel u)) guard None])
      (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb :: post)) |}]) in Hin.
    destruct Hin as [Heq|Hno]; [subst p|contradiction].
    apply continuing_false_edge; try assumption.
    + exact (Forall_inv Ht).
    + cbn [source right_conclusion succedent]; apply in_app_iff; cbn; auto.
    + cbn; apply in_app_iff; cbn; auto.
    + intros w' Hsrc Hdst Hbad Hbad'. apply test_decrease.
      intro H; apply Hbad; split; assumption.
Defined.

Definition identity_edge j : Cyclic.edge_info :=
  {| Cyclic.edge_valid := Cyclic.identity_pairs (judgment_tags j); Cyclic.edge_progress := [] |}.

Lemma identity_pair_equal a b tags : In (a,b) (Cyclic.identity_pairs tags) -> a = b.
Proof. unfold Cyclic.identity_pairs; rewrite in_map_iff; intros [t [H _]]; inversion H; reflexivity. Qed.

(** The substituted judgment is the conclusion, and [original] the premise.
    Backward countermodel propagation must therefore change the world using
    [transform]. [Hmap] preserves every interpreted label exactly, giving
    truth equivalence and equality of ranks for all identity tag pairs. *)
Definition label_substitution_rule (name : string) (original : judgment) (f : label -> label)
    (transform : world M -> world M)
    (Hmap : forall w l, eval_label M w (f l) = eval_label M (transform w) l)
    (Horiginal : judgment_wfb original = true) (Hsubstituted : judgment_wfb (map_labels f original) = true)
    : Cyclic.rule_instance.
Proof.
  refine {| Cyclic.rule_name := name; Cyclic.rule_conclusion := map_labels f original;
    Cyclic.rule_premises := [{| Cyclic.premise_judgment := original;
      Cyclic.premise_edge := identity_edge (map_labels f original) |}] |}.
  - intros Hall w. apply (proj2 (denote_mapping M f w (transform w) (Hmap w) original)).
    apply (Hall _ (or_introl eq_refl)).
  - intros w Hfalse.
    exists 0, {| Cyclic.premise_judgment := original;
      Cyclic.premise_edge := identity_edge (map_labels f original) |}, (transform w).
    split; [reflexivity|]. split.
    + intro H; apply Hfalse; apply (denote_mapping M f w (transform w) (Hmap w) original); exact H.
    + split.
      * intros a b Hin; apply identity_pair_equal in Hin; subst b.
        unfold LPLTheory.rank. cbn [map_labels succedent].
        rewrite (rank_label_mapping f w (transform w) (Hmap w)); apply Nat.le_refl.
      * intros a b Hin; inversion Hin.
Defined.

Definition world_substitution_rule original x replacement Hs Ht :=
  label_substitution_rule "Sub.World" original (subst_world_label x replacement)
    (fun w => replace_world M w x (eval_update M w replacement))
    (fun w l => eval_world_label_substitution M w x replacement l) Hs Ht.

Definition label_rotation_rule original path left Hs Ht :=
  label_substitution_rule "Label.Assoc" original (rotate_label path left) (fun w => w)
    (fun w l => eval_rotate_label M w path left l) Hs Ht.

Definition label_unit_rule original path on_left insert Hs Ht :=
  label_substitution_rule "Label.Unit" original (unit_label path on_left insert) (fun w => w)
    (fun w l => eval_unit_label M w path on_left insert l) Hs Ht.

Definition trace_substitution_rule original x replacement (Hne : label_nonemptyb replacement = true) Hs Ht :=
  label_substitution_rule "Sub.Trace" original (subst_trace_label x replacement)
    (fun w => replace_trace M w x (eval_label M w replacement)
      (proj1 (label_nonemptyb_spec M w replacement) Hne))
    (fun w l => eval_trace_label_substitution M w x replacement
      (proj1 (label_nonemptyb_spec M w replacement) Hne) l) Hs Ht.

Definition counter_rule (name : string) (source target : judgment) (edge : Cyclic.edge_info)
    (Hcounter : forall w, ~ denote M source w ->
      { w' : world M | ~ denote M target w' /\ Cyclic.respects_edge source target w w' edge })
    : Cyclic.rule_instance.
Proof.
  refine {| Cyclic.rule_name := name; Cyclic.rule_conclusion := source;
    Cyclic.rule_premises := [{| Cyclic.premise_judgment := target; Cyclic.premise_edge := edge |}] |}.
  - intros Hall w; apply NNPP; intro Hfalse.
    destruct (Hcounter w Hfalse) as [w' [Hbad _]]; apply Hbad; apply (Hall _ (or_introl eq_refl)).
  - intros w Hfalse; destruct (Hcounter w Hfalse) as [w' [Hbad He]].
    exists 0, {| Cyclic.premise_judgment := target; Cyclic.premise_edge := edge |}, w'; auto.
Defined.

Definition exact_backlink j Hwf :=
  local_rule "Backlink.exact" j [j] Hwf (Forall_cons _ Hwf (Forall_nil _))
    (fun w Hall => Hall j (or_introl eq_refl)).

(** Logical content stays exact and only tags change. Well-formedness of
    both judgments rejects collisions introduced by [f]; each advertised
    old/new tag pair follows the same interpreted formula and label. *)
Definition tag_renaming_backlink j f (Hs : judgment_wfb j = true)
    (Ht : judgment_wfb (rename_tags f j) = true) : Cyclic.rule_instance.
Proof.
  set (target := rename_tags f j).
  set (edge := {| Cyclic.edge_valid := map (fun t => (t, f t)) (judgment_tags j);
    Cyclic.edge_progress := [] |}).
  apply (counter_rule "Backlink.tags" j target edge).
  intros w Hfalse; exists w; split.
  - intro Htarget; apply Hfalse; apply (proj1 (denote_tag_renaming M f j w)); exact Htarget.
  - split.
    + intros a b Hin; apply in_map_iff in Hin as [t [Heq Htag]]; inversion Heq; subst a b.
      unfold judgment_tags in Htag; apply in_flat_map in Htag as [o [Ho Htago]].
      destruct (occurrence_tag o) as [tag|] eqn:Htag_o; [|contradiction].
      cbn in Htago; destruct Htago as [Heqtag|Hno]; [subst tag|contradiction].
      unfold LPLTheory.rank.
      rewrite (rank_context_occ _ _ o _ (wf_unique _ Hs) Ho Htag_o).
      assert (In (rename_occurrence_tag f o) target.(succedent)) as Hin_target.
      { unfold target, rename_tags; cbn; apply in_map_iff; exists o; auto. }
      assert ((rename_occurrence_tag f o).(occurrence_tag) = Some (f t)) as Hnewtag by
        (cbn [rename_occurrence_tag occurrence_tag]; now rewrite Htag_o).
      rewrite (rank_context_occ _ _ (rename_occurrence_tag f o) _ (wf_unique _ Ht) Hin_target Hnewtag).
      apply Nat.le_refl.
    + intros a b H; inversion H.
Defined.

(** Lists are not silently quotiented by permutation. Explicit evidence for
    left/right permutations justifies exchange and preserves tagged ranks. *)
Definition exchange_rule source target Hs Ht (Hrelations : relations source = relations target)
    (Hl : Permutation source.(antecedent) target.(antecedent))
    (Hr : Permutation source.(succedent) target.(succedent)) :=
  local_rule "Exchange" source [target] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall target (or_introl eq_refl)) as H;
      pose proof (proj1 (denote_wf target w (Forall_inv Ht)) H) as Hraw;
      apply (proj2 (denote_wf source w Hs)); intros Hrel Hleft;
      assert (left_holds M w (antecedent target)) as Htargetleft by
        (unfold left_holds in *; eapply Permutation_Forall; eauto);
      specialize (Hraw ltac:(rewrite <- Hrelations; exact Hrel) Htargetleft); destruct Hraw as [o [Hin Ho]];
      exists o; split; [apply (Permutation_in o (Permutation_sym Hr)); exact Hin|exact Ho])).

(** Cut combines two context partitions and has two premises. A classical
    case split on the cut assertion proves the semantic implication; the
    newly inserted cut occurrence receives no invented principal trace. *)
Definition cut_rule gamma sigma delta lambda cutformula Hs Ht :=
  local_rule "Cut" (Jdg (gamma ++ sigma) (delta ++ lambda))
    [Jdg gamma (cutformula :: delta); Jdg (sigma ++ [cutformula]) lambda] Hs Ht
    (fun w Hall => ltac:(
      pose proof (Hall _ (or_introl eq_refl)) as H1;
      pose proof (Hall _ (or_intror (or_introl eq_refl))) as H2;
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) H1) as R1;
      pose proof (proj1 (denote_wf _ w (Forall_inv (Forall_inv_tail Ht))) H2) as R2;
      apply (proj2 (denote_wf _ w Hs)); intro Hrel; specialize (R1 Hrel); specialize (R2 Hrel); cbn [antecedent succedent] in *;
      rewrite right_cons in R1; rewrite left_app, left_singleton in R2;
      rewrite left_app, right_app; tauto)).

(** Structural closing shapes. Each constructor still requires a complete
    well-formed judgment, so an invalid or empty assertion label cannot close
    merely because its formula looks like truth, falsehood or identity. *)
Definition truth_right_axiom j (Hwf : judgment_wfb j = true) o (Hin : In o j.(succedent))
    (Hf : o.(occurrence_formula) = Truth) : Cyclic.axiom_instance.
Proof.
  refine {| Cyclic.axiom_name := "True.R"; Cyclic.axiom_conclusion := j |}.
  intros w Hadm Hrelations Hleft.
  assert (label_admissible M w o.(occurrence_label)) as Hlabel.
  { destruct Hadm as [Hadm _]; rewrite Forall_forall in Hadm; apply Hadm; apply in_app_iff; auto. }
  exists o; split; [exact Hin|]. split; [exact Hlabel|]. rewrite Hf.
  unfold label_admissible in Hlabel. destruct (eval_label M w o.(occurrence_label)); [contradiction|exact I].
Defined.

Definition falsity_left_axiom j (Hwf : judgment_wfb j = true) o (Hin : In o j.(antecedent))
    (Hf : o.(occurrence_formula) = Falsity) : Cyclic.axiom_instance.
Proof.
  refine {| Cyclic.axiom_name := "False.L"; Cyclic.axiom_conclusion := j |}.
  intros w Hadm Hrelations Hleft. unfold left_holds in Hleft; rewrite Forall_forall in Hleft.
  destruct (Hleft o Hin) as [Hlabel Hfalse]; rewrite Hf in Hfalse.
  destruct (eval_label M w o.(occurrence_label)); contradiction.
Defined.

Definition identity_axiom j (Hwf : judgment_wfb j = true) l r
    (Hl : In l j.(antecedent)) (Hr : In r j.(succedent))
    (Hlabel : occurrence_label l = occurrence_label r)
    (Hformula : occurrence_formula l = occurrence_formula r) : Cyclic.axiom_instance.
Proof.
  refine {| Cyclic.axiom_name := "Id"; Cyclic.axiom_conclusion := j |}.
  intros w Ha Hrelations Hleft. unfold left_holds in Hleft; rewrite Forall_forall in Hleft.
  specialize (Hleft l Hl). exists r; split; [exact Hr|].
  unfold labelled_holds in *; now rewrite <- Hlabel, <- Hformula.
Defined.

End RelationContext.

(** ** Atomic actions and explicit relational assumptions *)
Lemma occurrence_rank_fresh source o w x value :
  world_freshb x source = true -> In o (source.(antecedent) ++ source.(succedent)) ->
  occurrence_rank o (replace_world M w x value) = occurrence_rank o w.
Proof.
  intros Hfresh Hin; unfold occurrence_rank.
  rewrite eval_label_fresh; [reflexivity|eapply fresh_occurrence; eauto].
Qed.
Lemma retained_edge_fresh source target w x value :
  judgment_wfb source = true -> judgment_wfb target = true -> world_freshb x source = true ->
  Cyclic.respects_edge source target w (replace_world M w x value) (retained_edge source target).
Proof.
  intros Hs Ht Hfresh; split.
  - intros a b Hin; apply retained_pairs_spec in Hin as [-> [o [Hsocc [Htocc Htag]]]].
    unfold LPLTheory.rank.
    rewrite (rank_context_occ _ _ o _ (wf_unique _ Hs) Hsocc Htag).
    rewrite (rank_context_occ _ _ o _ (wf_unique _ Ht) Htocc Htag).
    rewrite (occurrence_rank_fresh source o w x value Hfresh); [lia|apply in_app_iff; auto].
  - intros a b H; inversion H.
Qed.
Lemma fresh_left source context w x value : world_freshb x source = true ->
  (forall o, In o context -> In o (source.(antecedent) ++ source.(succedent))) ->
  (left_holds M (replace_world M w x value) context <-> left_holds M w context).
Proof.
  intros Hfresh Hinclude; unfold left_holds; rewrite !Forall_forall.
  split; intros H o Hin; specialize (H o Hin);
    assert (~ In x (label_world_names o.(occurrence_label))) as Hnames by
      (eapply fresh_occurrence; [exact Hfresh|apply Hinclude; exact Hin]);
    apply (labelled_fresh M w x value o Hnames); exact H.
Qed.
Lemma fresh_right source context w x value : world_freshb x source = true ->
  (forall o, In o context -> In o (source.(antecedent) ++ source.(succedent))) ->
  (right_holds M (replace_world M w x value) context <-> right_holds M w context).
Proof.
  intros Hfresh Hinclude; unfold right_holds; split;
    intros [o [Hin Ho]]; exists o; split; [exact Hin| |exact Hin|];
    assert (~ In x (label_world_names o.(occurrence_label))) as Hnames by
      (eapply fresh_occurrence; [exact Hfresh|apply Hinclude; exact Hin]);
    apply (labelled_fresh M w x value o Hnames); exact Ho.
Qed.

Lemma continuation_edge_worlds source target a b progress w w' :
  judgment_wfb source = true -> judgment_wfb target = true ->
  In a source.(succedent) -> In b target.(succedent) ->
  Cyclic.respects_edge source target w w' (retained_edge source target) ->
  occurrence_rank b w' <= occurrence_rank a w ->
  (progress = true -> occurrence_rank b w' < occurrence_rank a w) ->
  Cyclic.respects_edge source target w w' (continuation_edge source target a b progress).
Proof.
  intros Hs Ht Ha Hb Hretained Hle Hlt; split.
  - intros x y Hin; apply in_app_iff in Hin as [Hret|Hcont].
    + exact (proj1 Hretained x y Hret).
    + unfold continuation_pairs in Hcont.
      destruct (occurrence_tag a) as [ta|] eqn:Hta; [|contradiction].
      destruct (occurrence_tag b) as [tb|] eqn:Htb; [|contradiction].
      destruct Hcont as [Heq|Hno]; [inversion Heq; subst|contradiction].
      unfold LPLTheory.rank.
      rewrite (rank_context_occ _ _ a _ (wf_unique _ Hs) Ha Hta).
      rewrite (rank_context_occ _ _ b _ (wf_unique _ Ht) Hb Htb); exact Hle.
  - intros x y Hin.
    change (In (x,y) (if progress then continuation_pairs a b else [])) in Hin.
    destruct progress; [|contradiction].
    unfold continuation_pairs in Hin.
    destruct (occurrence_tag a) as [ta|] eqn:Hta; [|contradiction].
    destruct (occurrence_tag b) as [tb|] eqn:Htb; [|contradiction].
    destruct Hin as [Heq|Hno]; [inversion Heq; subst|contradiction].
    unfold LPLTheory.rank.
    rewrite (rank_context_occ _ _ a _ (wf_unique _ Hs) Ha Hta).
    rewrite (rank_context_occ _ _ b _ (wf_unique _ Ht) Hb Htb); apply Hlt; reflexivity.
Qed.

Definition action_relation action payload u v :=
  ActionRelation action payload (StateLabel u) (StateLabel v).
Definition action_label sigma u v := Join (Join sigma (StateLabel u)) (StateLabel v).

Lemma action_relation_holds w action payload u v :
  relation_holds M w (action_relation action payload u v) <->
  interpret_action M action payload (eval_update M w u) (eval_update M w v).
Proof.
  unfold action_relation; cbn [relation_holds eval_label]; split.
  - intros [s [t [Hs [Ht Hstep]]]]; inversion Hs; inversion Ht; subst; exact Hstep.
  - intro H; exists (eval_update M w u), (eval_update M w v); auto.
Qed.
Lemma box_action_use w sigma u v action payload body ta tb :
  relation_holds M w (action_relation action payload u v) ->
  labelled_holds M w (Occ (Join sigma (StateLabel u)) (Box (Atomic action payload) body) ta) ->
  labelled_holds M w (Occ (action_label sigma u v) body tb).
Proof.
  intros Hrel [_ Hbox]; apply action_relation_holds in Hrel.
  unfold labelled_holds, label_admissible, action_label; cbn [occurrence_label occurrence_formula eval_label] in *.
  split; [intro H; apply app_eq_nil in H; destruct H; discriminate|].
  apply (proj1 (box_atomic M (eval_label M w sigma) (eval_update M w u) action payload body)); exact Hbox || exact Hrel.
Qed.
Lemma diamond_action_use w sigma u v action payload body ta tb :
  relation_holds M w (action_relation action payload u v) ->
  labelled_holds M w (Occ (action_label sigma u v) body tb) ->
  labelled_holds M w (Occ (Join sigma (StateLabel u)) (Diamond (Atomic action payload) body) ta).
Proof.
  intros Hrel [_ Hbody]; apply action_relation_holds in Hrel.
  unfold labelled_holds, label_admissible, action_label; cbn [occurrence_label occurrence_formula eval_label] in *.
  split; [intro H; apply app_eq_nil in H; destruct H; discriminate|].
  apply (proj2 (diamond_atomic M (eval_label M w sigma) (eval_update M w u) action payload body)); exists (eval_update M w v); auto.
Qed.

Definition box_atomic_right R lhs pre post sigma u action payload body y ta tb
    (Hs : judgment_wfb (right_conclusion R lhs pre post
      (Occ (Join sigma (StateLabel u)) (Box (Atomic action payload) body) ta)) = true)
    (Ht : judgment_wfb (Rdg (R ++ [action_relation action payload u (L.world_name y)]) lhs
      (pre ++ Occ (action_label sigma u (L.world_name y)) body tb :: post)) = true)
    (Hfresh : world_freshb y (right_conclusion R lhs pre post
      (Occ (Join sigma (StateLabel u)) (Box (Atomic action payload) body) ta)) = true)
    : Cyclic.rule_instance.
Proof.
  set (principal := Occ (Join sigma (StateLabel u)) (Box (Atomic action payload) body) ta).
  set (replacement := Occ (action_label sigma u (L.world_name y)) body tb).
  set (source := right_conclusion R lhs pre post principal).
  set (target := Rdg (R ++ [action_relation action payload u (L.world_name y)]) lhs (pre ++ replacement :: post)).
  apply (counter_rule "B.Atomic.R" source target (continuation_edge source target principal replacement true)).
  intros w Hfalse.
  destruct (false_right_parts R lhs pre post principal w Hfalse) as [Hleft [Hpre [Hprincipal Hpost]]].
  assert (~ formula_holds M (Box (Atomic action payload) body)
    (eval_label M w sigma ++ [eval_update M w u])) as Hbad.
  { intro H; apply Hprincipal; split; [unfold label_admissible; cbn [principal occurrence_label eval_label];
      intro Heq; apply app_eq_nil in Heq; destruct Heq; discriminate|exact H]. }
  set (Q := fun next => interpret_action M action payload (eval_update M w u) next /\
    ~ formula_holds M body ((eval_label M w sigma ++ [eval_update M w u]) ++ [next]) /\
    minimum_counterexample body ((eval_label M w sigma ++ [eval_update M w u]) ++ [next]) <
    minimum_counterexample (Box (Atomic action payload) body) (eval_label M w sigma ++ [eval_update M w u])).
  set (next := epsilon (inhabits (carrier_inhabitant M)) Q).
  assert (Q next) as [Hstep [Hbody Hrank]].
  { unfold next; apply epsilon_spec; apply atomic_minimum_successor; exact Hbad. }
  set (w' := replace_world M w y next).
  assert (eval_label M w' (Join sigma (StateLabel u)) = eval_label M w sigma ++ [eval_update M w u]) as Hprefix.
  { unfold w'; rewrite eval_label_fresh; [reflexivity|].
    apply (fresh_occurrence source y principal Hfresh); unfold source; cbn [right_conclusion antecedent succedent];
      rewrite !in_app_iff; cbn; tauto. }
  assert (eval_label M w' (action_label sigma u (L.world_name y)) =
    (eval_label M w sigma ++ [eval_update M w u]) ++ [next]) as Hlabel.
  { change (eval_label M w' (Join sigma (StateLabel u)) ++ [eval_update M w' (L.world_name y)] =
      (eval_label M w sigma ++ [eval_update M w u]) ++ [next]).
    rewrite Hprefix; unfold w'; rewrite eval_fresh_name; reflexivity. }
  assert (eval_update M w' u = eval_update M w u) as Hu.
  { unfold w'; apply eval_update_fresh; intro Hin.
    assert (In principal (source.(antecedent) ++ source.(succedent))) as Hmember.
    { unfold source; cbn [right_conclusion antecedent succedent]; rewrite !in_app_iff; cbn; tauto. }
    pose proof (fresh_occurrence source y principal Hfresh Hmember) as Hnames.
    apply Hnames; cbn [principal occurrence_label label_world_names]; apply in_app_iff; auto. }
  exists w'; split.
  - intro Hden; pose proof (proj1 (denote_wf target w' Ht) Hden) as Hraw.
    assert (relations_hold M w' target.(relations)) as Hrelations.
    { unfold target; cbn [relations]; unfold relations_hold; apply Forall_app; split.
      - apply (proj2 (relations_fresh M source w y next Hfresh)); exact (false_relations M source w Hfalse).
      - constructor; [apply action_relation_holds; rewrite Hu; unfold w'; rewrite eval_fresh_name; exact Hstep|constructor]. }
    assert (left_holds M w' lhs) as Hl'.
    { apply (proj2 (fresh_left source lhs w y next Hfresh ltac:(
        intros o Hin; unfold source; cbn [right_conclusion antecedent succedent]; apply in_app_iff; auto))); exact Hleft. }
    specialize (Hraw Hrelations Hl'); unfold target in Hraw; cbn [succedent] in Hraw;
      rewrite right_app, right_cons in Hraw.
    destruct Hraw as [Hpre'|[Hreplacement|Hpost']].
    + apply Hpre; apply (proj1 (fresh_right source pre w y next Hfresh ltac:(
        intros o Hin; unfold source; cbn [right_conclusion antecedent succedent]; rewrite !in_app_iff; cbn; auto))); exact Hpre'.
    + apply Hbody; destruct Hreplacement as [_ Hholds]; cbn [replacement occurrence_formula occurrence_label] in Hholds; now rewrite Hlabel in Hholds.
    + apply Hpost; apply (proj1 (fresh_right source post w y next Hfresh ltac:(
        intros o Hin; unfold source; cbn [right_conclusion antecedent succedent]; rewrite !in_app_iff; cbn; auto))); exact Hpost'.
  - apply continuation_edge_worlds; try exact Hs; try exact Ht.
    + unfold source; cbn [right_conclusion succedent]; rewrite in_app_iff; cbn; auto.
    + unfold target; cbn [succedent]; rewrite in_app_iff; cbn; auto.
    + apply retained_edge_fresh; assumption.
    + unfold occurrence_rank; cbn [principal replacement occurrence_label occurrence_formula]; rewrite Hlabel; cbn [eval_label]; lia.
    + intros _; unfold occurrence_rank; cbn [principal replacement occurrence_label occurrence_formula]; rewrite Hlabel; exact Hrank.
Defined.

Definition box_atomic_left Rpre Rpost pre post rhs sigma u v action payload body ta tb
    (Hs : judgment_wfb (Rdg (Rpre ++ action_relation action payload u v :: Rpost)
      (pre ++ Occ (Join sigma (StateLabel u)) (Box (Atomic action payload) body) ta :: post) rhs) = true)
    (Ht : judgment_wfb (Rdg (Rpre ++ Rpost)
      (pre ++ Occ (action_label sigma u v) body tb :: post) rhs) = true)
    : Cyclic.rule_instance.
Proof.
  apply (local_rule "B.Atomic.L" _ _ Hs (Forall_cons _ Ht (Forall_nil _))).
  intros w Hall; apply (proj2 (denote_wf _ w Hs)); intros Hrelations Hleft.
  specialize (Hall _ (or_introl eq_refl)).
  pose proof (proj1 (denote_wf _ w Ht) Hall) as Hraw.
  cbn [relations antecedent succedent] in *.
  unfold relations_hold in Hrelations; rewrite Forall_app, Forall_cons_iff in Hrelations.
  destruct Hrelations as [HRpre [Hstep HRpost]].
  apply Hraw.
  - unfold relations_hold; apply Forall_app; auto.
  - rewrite left_app, left_cons in *; destruct Hleft as [Hpre [Hbox Hpost]].
    split; [exact Hpre|]. split; [eapply box_action_use; eauto|exact Hpost].
Defined.

Definition diamond_atomic_right Rpre Rpost lhs pre post sigma u v action payload body ta tb
    (Hs : judgment_wfb (Rdg (Rpre ++ action_relation action payload u v :: Rpost) lhs
      (pre ++ Occ (Join sigma (StateLabel u)) (Diamond (Atomic action payload) body) ta :: post)) = true)
    (Ht : judgment_wfb (Rdg (Rpre ++ Rpost) lhs
      (pre ++ Occ (action_label sigma u v) body tb :: post)) = true)
    : Cyclic.rule_instance.
Proof.
  apply (local_rule "D.Atomic.R" _ _ Hs (Forall_cons _ Ht (Forall_nil _))).
  intros w Hall; apply (proj2 (denote_wf _ w Hs)); intros Hrelations Hleft.
  specialize (Hall _ (or_introl eq_refl)).
  pose proof (proj1 (denote_wf _ w Ht) Hall) as Hraw.
  cbn [relations antecedent succedent] in *.
  unfold relations_hold in Hrelations; rewrite Forall_app, Forall_cons_iff in Hrelations.
  destruct Hrelations as [HRpre [Hstep HRpost]].
  assert (relations_hold M w (Rpre ++ Rpost)) as HR by (unfold relations_hold; apply Forall_app; auto).
  specialize (Hraw HR Hleft); rewrite right_app, right_cons in *.
  destruct Hraw as [Hpre|[Hbody|Hpost]]; [auto| |auto].
  right; left; eapply diamond_action_use; eauto.
Defined.

Definition diamond_atomic_left R pre post rhs sigma u action payload body y ta tb
    (Hs : judgment_wfb (Rdg R
      (pre ++ Occ (Join sigma (StateLabel u)) (Diamond (Atomic action payload) body) ta :: post) rhs) = true)
    (Ht : judgment_wfb (Rdg (R ++ [action_relation action payload u (L.world_name y)])
      (pre ++ Occ (action_label sigma u (L.world_name y)) body tb :: post) rhs) = true)
    (Hfresh : world_freshb y (Rdg R
      (pre ++ Occ (Join sigma (StateLabel u)) (Diamond (Atomic action payload) body) ta :: post) rhs) = true)
    : Cyclic.rule_instance.
Proof.
  set (principal := Occ (Join sigma (StateLabel u)) (Diamond (Atomic action payload) body) ta).
  set (replacement := Occ (action_label sigma u (L.world_name y)) body tb).
  set (source := Rdg R (pre ++ principal :: post) rhs).
  set (target := Rdg (R ++ [action_relation action payload u (L.world_name y)]) (pre ++ replacement :: post) rhs).
  apply (counter_rule "D.Atomic.L" source target (retained_edge source target)).
  intros w Hfalse.
  destruct (false_sequent M source w Hfalse) as [_ [Hleft Hright]].
  change (left_holds M w (pre ++ principal :: post)) in Hleft.
  rewrite left_app, left_cons in Hleft; destruct Hleft as [Hpre [[Hne Hdiamond] Hpost]].
  change (formula_holds M (Diamond (Atomic action payload) body)
    (eval_label M w sigma ++ [eval_update M w u])) in Hdiamond.
  apply diamond_atomic in Hdiamond.
  set (Q := fun next => interpret_action M action payload (eval_update M w u) next /\
    formula_holds M body ((eval_label M w sigma ++ [eval_update M w u]) ++ [next])).
  set (next := epsilon (inhabits (carrier_inhabitant M)) Q).
  assert (Q next) as [Hstep Hbody] by (unfold next; apply epsilon_spec; exact Hdiamond).
  set (w' := replace_world M w y next).
  assert (In principal (source.(antecedent) ++ source.(succedent))) as Hmember.
  { unfold source; cbn [antecedent succedent]; rewrite !in_app_iff; cbn; tauto. }
  pose proof (fresh_occurrence source y principal Hfresh Hmember) as Hnames.
  assert (eval_update M w' u = eval_update M w u) as Hu.
  { unfold w'; apply eval_update_fresh; intro Hin; apply Hnames;
      cbn [principal occurrence_label label_world_names]; apply in_app_iff; auto. }
  assert (eval_label M w' (action_label sigma u (L.world_name y)) =
    (eval_label M w sigma ++ [eval_update M w u]) ++ [next]) as Hlabel.
  { change (eval_label M w' (Join sigma (StateLabel u)) ++ [eval_update M w' (L.world_name y)] =
      (eval_label M w sigma ++ [eval_update M w u]) ++ [next]).
    unfold w'; rewrite eval_label_fresh by exact Hnames; rewrite eval_fresh_name; reflexivity. }
  exists w'; split.
  - intro Hden; pose proof (proj1 (denote_wf target w' Ht) Hden) as Hraw.
    assert (relations_hold M w' target.(relations)) as Hrelations.
    { unfold target; cbn [relations]; unfold relations_hold; apply Forall_app; split.
      - apply (proj2 (relations_fresh M source w y next Hfresh)); exact (false_relations M source w Hfalse).
      - constructor; [apply action_relation_holds; rewrite Hu; unfold w'; rewrite eval_fresh_name; exact Hstep|constructor]. }
    assert (left_holds M w' (pre ++ replacement :: post)) as Hl'.
    { rewrite left_app, left_cons; split.
      - apply (proj2 (fresh_left source pre w y next Hfresh ltac:(
          intros o Hin; unfold source; cbn [antecedent succedent]; rewrite !in_app_iff; cbn; auto))); exact Hpre.
      - split.
        + split; [apply (wellformed_left_principal (R ++ [action_relation action payload u (L.world_name y)]) pre post rhs replacement w' Ht)|].
          cbn [replacement occurrence_formula occurrence_label]; rewrite Hlabel; exact Hbody.
        + apply (proj2 (fresh_left source post w y next Hfresh ltac:(
            intros o Hin; unfold source; cbn [antecedent succedent]; rewrite !in_app_iff; cbn; auto))); exact Hpost. }
    specialize (Hraw Hrelations Hl').
    assert (right_holds M w rhs) as Hr.
    { apply (proj1 (fresh_right source rhs w y next Hfresh ltac:(
        intros o Hin; unfold source; cbn [antecedent succedent]; apply in_app_iff; auto))); exact Hraw. }
    destruct Hr as [o [Hin Ho]]; exact (Hright o Hin Ho).
  - apply retained_edge_fresh; assumption.
Defined.

(** Relations can be explicitly weakened, exchanged, or contracted without
    attaching formula-occurrence tags to them. *)
Definition relation_structural source target Hs Ht
    (Hformula_left : source.(antecedent) = target.(antecedent))
    (Hformula_right : source.(succedent) = target.(succedent))
    (Hrelations : forall w, relations_hold M w source.(relations) -> relations_hold M w target.(relations)) :=
  local_rule "Rel.Structural" source [target] Hs Ht
    (fun w Hall => ltac:(
      pose proof (proj1 (denote_wf target w (Forall_inv Ht)) (Hall target (or_introl eq_refl))) as Hraw;
      apply (proj2 (denote_wf source w Hs)); intros Hrel Hleft;
      rewrite Hformula_left, Hformula_right in *; apply Hraw; [apply Hrelations; exact Hrel|exact Hleft])).
Definition relation_weakening Rpre Rpost relation lhs rhs Hs Ht :=
  relation_structural (Rdg (Rpre ++ relation :: Rpost) lhs rhs) (Rdg (Rpre ++ Rpost) lhs rhs)
    Hs Ht eq_refl eq_refl (fun w H => ltac:(
      cbn [relations] in *; unfold relations_hold in *; rewrite Forall_app, Forall_cons_iff in H;
      apply Forall_app; tauto)).
Definition relation_exchange source target Hs Ht Hl Hr
    (Hrel : Permutation source.(relations) target.(relations)) :=
  relation_structural source target Hs Ht Hl Hr
    (fun w H => ltac:(unfold relations_hold in *; eapply Permutation_Forall; eauto)).
Definition relation_contraction Rpre Rpost relation lhs rhs Hs Ht :=
  relation_structural (Rdg (Rpre ++ relation :: Rpost) lhs rhs)
    (Rdg (Rpre ++ relation :: relation :: Rpost) lhs rhs) Hs Ht eq_refl eq_refl
    (fun w H => ltac:(cbn [relations] in *; unfold relations_hold in *;
      rewrite !Forall_app, !Forall_cons_iff in *; tauto)).

(** The manuscript's cut may split relational assumptions as well as formula
    contexts. The older fixed-context cut remains a compatible specialization. *)
Definition cut_relations Rgamma Rsigma gamma sigma delta lambda cutformula Hs Ht :=
  local_rule "Cut.Relations" (Rdg (Rgamma ++ Rsigma) (gamma ++ sigma) (delta ++ lambda))
    [Rdg Rgamma gamma (cutformula :: delta); Rdg Rsigma (sigma ++ [cutformula]) lambda] Hs Ht
    (fun w Hall => ltac:(
      pose proof (proj1 (denote_wf _ w (Forall_inv Ht)) (Hall _ (or_introl eq_refl))) as R1;
      pose proof (proj1 (denote_wf _ w (Forall_inv (Forall_inv_tail Ht))) (Hall _ (or_intror (or_introl eq_refl)))) as R2;
      apply (proj2 (denote_wf _ w Hs)); cbn [relations antecedent succedent] in *;
      intros Hrel; unfold relations_hold in Hrel; apply Forall_app in Hrel as [Hrel1 Hrel2];
      specialize (R1 Hrel1); specialize (R2 Hrel2);
      rewrite right_cons in R1; rewrite left_app, left_singleton in R2;
      rewrite left_app, right_app; tauto)).

End MakeRulesForModel.

(** Preserve the public two-stage construction while keeping the required
    kernel signature free of an unused, unapplied generative rule factory. *)
Module MakeRules (L : LANGUAGE) (Syn : SYNTAX L) (Sem : SEMANTICS L Syn)
    (Pr : PROGRESS L Syn Sem).
  Export Syn Sem.
  Module ForModel := MakeRulesForModel L Syn Sem Pr.
End MakeRules.

(** One shared rule/progress instance is passed to generation and checking. *)
Module Type KERNEL (L : LANGUAGE) (Syn : SYNTAX L) (Sem : SEMANTICS L Syn)
    (Pr : PROGRESS L Syn Sem).
  Declare Module Model : Sem.INTERPRETATION.
  Include MakeRulesForModel L Syn Sem Pr Model.
End KERNEL.
