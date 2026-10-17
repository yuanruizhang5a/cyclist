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
From CyclistRocq.LPL.FOPL Require Import Signature Syntax Semantics Progress.
From CyclistRocq.LPL Require Import Rules.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Module MakeRules (S : SIGNATURE).
Module Export Pr := MakeProgress S.
Module SharedCore := CyclistRocq.LPL.Rules.MakeRules Pr.Sem.Syn.Language Pr.Sem.Syn.Shared Pr.Sem.Shared Pr.Shared.
Module ForModel (I : Pr.Sem.INTERPRETATION).
Module SharedModel <: Pr.Sem.Shared.INTERPRETATION.
  Definition interpretation := Pr.Sem.general_model I.interpretation.
End SharedModel.
Module SharedRules := SharedCore.ForModel SharedModel.
Module Export Common := SharedRules.
Module Export P := Pr.ForModel I SharedModel Common.P.
Definition atom_head_left := Common.atom_head_left [].
Definition atom_head_right := Common.atom_head_right [].
Definition box_choice_left := Common.box_choice_left [].
Definition box_choice_right := Common.box_choice_right [].
Definition box_choice_right_base := Common.box_choice_right_base [].
Definition box_sequence_left := Common.box_sequence_left [].
Definition box_sequence_right := Common.box_sequence_right [].
Definition box_sequence_right_base := Common.box_sequence_right_base [].
Definition box_star_left := Common.box_star_left [].
Definition box_star_right := Common.box_star_right [].
Definition box_star_right_base := Common.box_star_right_base [].
Definition box_test_left := Common.box_test_left [].
Definition box_test_right := Common.box_test_right [].
Definition box_test_right_base := Common.box_test_right_base [].
Definition conjunction_left := Common.conjunction_left [].
Definition conjunction_right := Common.conjunction_right [].
Definition cut_rule := Common.cut_rule [].
Definition diamond_choice_left := Common.diamond_choice_left [].
Definition diamond_choice_right := Common.diamond_choice_right [].
Definition diamond_sequence_left := Common.diamond_sequence_left [].
Definition diamond_sequence_right := Common.diamond_sequence_right [].
Definition diamond_star_left := Common.diamond_star_left [].
Definition diamond_star_right := Common.diamond_star_right [].
Definition diamond_test_left := Common.diamond_test_left [].
Definition diamond_test_right := Common.diamond_test_right [].
Definition disjunction_left := Common.disjunction_left [].
Definition disjunction_right := Common.disjunction_right [].
Definition dual_suffix_left := Common.dual_suffix_left [].
Definition dual_suffix_right := Common.dual_suffix_right [].
Definition dual_suffix_right_base := Common.dual_suffix_right_base [].
Definition enhance_right := Common.enhance_right [].
Definition false_right_parts := Common.false_right_parts [].
Definition false_right_replacement := Common.false_right_replacement [].
Definition first_left := Common.first_left [].
Definition first_right := Common.first_right [].
Definition implication_left := Common.implication_left [].
Definition implication_right := Common.implication_right [].
Definition left_conclusion := Common.left_conclusion [].
Definition left_equivalent := Common.left_equivalent [].
Definition left_label_equivalent := Common.left_label_equivalent [].
Definition left_many := Common.left_many [].
Definition left_one := Common.left_one [].
Definition left_targets := Common.left_targets [].
Definition left_two_conjunctive := Common.left_two_conjunctive [].
Definition left_two_disjunctive := Common.left_two_disjunctive [].
Definition negation_left := Common.negation_left [].
Definition negation_right := Common.negation_right [].
Definition right_conclusion := Common.right_conclusion [].
Definition right_equivalent := Common.right_equivalent [].
Definition right_label_equivalent := Common.right_label_equivalent [].
Definition right_many := Common.right_many [].
Definition right_one := Common.right_one [].
Definition right_targets := Common.right_targets [].
Definition right_two_disjunctive := Common.right_two_disjunctive [].
Definition right_two_equivalent := Common.right_two_equivalent [].
Definition suffix_left := Common.suffix_left [].
Definition suffix_right := Common.suffix_right [].
Definition suffix_right_base := Common.suffix_right_base [].
Definition weakening_left := Common.weakening_left [].
Definition weakening_right := Common.weakening_right [].
Definition wellformed_left_principal := Common.wellformed_left_principal [].
Definition wellformed_principal := Common.wellformed_principal [].
Definition box_assignment_right_base lhs pre post sigma u x t body ta tb Hs Ht :=
  right_label_equivalent "B.Assign.R" lhs pre post
    (Occ (Join sigma (StateLabel u)) (Box (Assign x t) body) ta)
    (Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb) Hs Ht
    (fun w => assignment_label M w sigma u x t body ta tb).
Definition box_assignment_left pre post rhs sigma u x t body ta tb Hs Ht :=
  left_label_equivalent "B.Assign.L" pre post rhs
    (Occ (Join sigma (StateLabel u)) (Box (Assign x t) body) ta)
    (Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb) Hs Ht
    (fun w => assignment_label M w sigma u x t body ta tb).
Definition diamond_assignment_right lhs pre post sigma u x t body ta tb Hs Ht :=
  right_label_equivalent "D.Assign.R" lhs pre post
    (Occ (Join sigma (StateLabel u)) (Diamond (Assign x t) body) ta)
    (Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb) Hs Ht
    (fun w => diamond_assignment_label M w sigma u x t body ta tb).
Definition diamond_assignment_left pre post rhs sigma u x t body ta tb Hs Ht :=
  left_label_equivalent "D.Assign.L" pre post rhs
    (Occ (Join sigma (StateLabel u)) (Diamond (Assign x t) body) ta)
    (Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb) Hs Ht
    (fun w => diamond_assignment_label M w sigma u x t body ta tb).
Definition box_assignment_right (lhs pre post : list occurrence) (sigma : label) (u : update)
    (x : nat) (t : term) (body : formula) (ta tb : option nat)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ (Join sigma (StateLabel u)) (Box (Assign x t) body) ta)) = true)
    (Ht : Forall (fun j => judgment_wfb j = true)
      (right_targets lhs pre post [[Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb]]))
    : Cyclic.rule_instance.
Proof.
  refine (enhance_right (box_assignment_right_base lhs pre post sigma u x t body ta tb Hs Ht)
    lhs pre post (Occ (Join sigma (StateLabel u)) (Box (Assign x t) body) ta)
    [Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb] true
    Hs Ht eq_refl eq_refl _).
  intros w Hne Hbad.
  assert (~ formula_holds M (Box (Assign x t) body)
    (eval_label M w sigma ++ [eval_update M w u])) as Hfalse.
  { intro H; apply Hbad; split; assumption. }
  pose proof (assignment_decrease (eval_label M w sigma) (eval_update M w u) x t body Hfalse) as Hrank.
  exists (Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb).
  split; [cbn; auto|]. split.
  - intro H; apply Hbad; apply (proj2 (assignment_label M w sigma u x t body ta tb)); exact H.
  - assert (occurrence_rank
      (Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb) w <
      occurrence_rank (Occ (Join sigma (StateLabel u)) (Box (Assign x t) body) ta) w) as Hstrict by exact Hrank.
    split; [lia|intro H; exact Hstrict].
Defined.

Lemma occurrence_rank_switch v f (Hf : forall d, f (f d) = d) o w :
  ~ In v (occurrence_vars o) ->
  occurrence_rank o (switch_world M v f w) = occurrence_rank o w.
Proof.
  intro Hfresh;
  change (minimum_counterexample o.(occurrence_formula) (eval_label M (switch_world M v f w) o.(occurrence_label)) =
    minimum_counterexample o.(occurrence_formula) (eval_label M w o.(occurrence_label))).
  rewrite switch_label.
  - apply (minimum_switch v f Hf); intro H; apply Hfresh; apply in_app_iff; auto.
  - intro H; apply Hfresh; apply in_app_iff; auto.
Qed.

Lemma retained_edge_switch_respects source target v f (Hf : forall d, f (f d) = d) w :
  judgment_wfb source = true -> judgment_wfb target = true ->
  (forall o tag, In o source.(succedent) -> o.(occurrence_tag) = Some tag -> ~ In v (occurrence_vars o)) ->
  Cyclic.respects_edge source target w (switch_world M v f w) (retained_edge source target).
Proof.
  intros Hs Ht Hfresh; split.
  - intros a b Hin; apply retained_pairs_spec in Hin as [-> [o [Hsocc [Htocc Htag]]]].
    unfold LPLTheory.rank.
    rewrite (rank_context_occ _ _ o _ (wf_unique _ Hs) Hsocc Htag).
    rewrite (rank_context_occ _ _ o _ (wf_unique _ Ht) Htocc Htag).
    rewrite occurrence_rank_switch; [apply Nat.le_refl|exact Hf|eapply Hfresh; eauto].
  - intros a b H; inversion H.
Qed.

Lemma context_variable_fresh j v : ~ In v (judgment_vars j) ->
  forall o, In o (j.(antecedent) ++ j.(succedent)) -> ~ In v (occurrence_vars o).
Proof.
  intros Hfresh o Hin Hv; apply Hfresh; apply in_flat_map; exists o; auto.
Qed.

Definition universal_left pre post rhs l u body t Hpure Hs Ht :=
  left_one "All.L" pre post rhs (Occ l (All u body) None) (Occ l (subst_fo u t body) None) Hs Ht
    (fun w H => conj (proj1 H) (all_instantiation M body u t _ Hpure (proj1 H) (proj2 H))).
Definition existential_right lhs pre post l u body t Hpure Hs Ht :=
  right_one "Ex.R" lhs pre post (Occ l (Ex u body) None) (Occ l (subst_fo u t body) None) Hs Ht
    (fun w Hne H => conj Hne (ex_instantiation M body u t _ Hpure Hne (proj2 H))).

(** Eigenvariable rules change the countermodel world. A failing universal
    supplies a value [d]; swap it with the principal head's current [v] value
    in every state. Freshness for contexts, body and principal label makes
    the instance fail while preserving all context truths and trace ranks.
    Existential-left below uses the corresponding satisfying witness. *)
Definition universal_right (lhs pre post : list occurrence) (l : label) (u v : nat) (body : formula)
    (Hpure : pureb body = true)
    (Hfresh : eigen_freshb v (Jdg lhs (pre ++ post)) l body = true)
    (Hs : judgment_wfb (right_conclusion lhs pre post (Occ l (All u body) None)) = true)
    (Ht : judgment_wfb (right_conclusion lhs pre post (Occ l (subst_fo u (Var v) body) None)) = true)
    : Cyclic.rule_instance.
Proof.
  apply (counter_rule "All.R"
    (right_conclusion lhs pre post (Occ l (All u body) None))
    (right_conclusion lhs pre post (Occ l (subst_fo u (Var v) body) None))
    (retained_edge (right_conclusion lhs pre post (Occ l (All u body) None))
    (right_conclusion lhs pre post (Occ l (subst_fo u (Var v) body) None)))).
  intros w Hfalse.
  apply eigen_freshb_spec in Hfresh.
  assert (~ In v (judgment_vars (Jdg lhs (pre ++ post)))) as Hctx by
    (intro H; apply Hfresh; apply in_app_iff; auto).
  assert (~ In v (label_vars l)) as Hlabel by
    (intro H; apply Hfresh; apply in_app_iff; right; apply in_app_iff; auto).
  assert (~ In v (formula_vars body)) as Hbody by
    (intro H; apply Hfresh; apply in_app_iff; right; apply in_app_iff; auto).
  pose proof (context_variable_fresh _ _ Hctx) as Hocc.
  destruct (false_right_parts _ _ _ _ _ Hfalse) as [Hleft [Hpre [Hprincipal Hpost]]].
  pose proof (wellformed_principal _ _ _ _ w Hs) as Hne.
  change (eval_label M w l <> []) in Hne.
  destruct (eval_label M w l) as [|s tail] eqn:Hlabel_eval; [contradiction|].
  assert (~ (forall d, fol_holds M body (write M s u d))) as Hnotall.
  { intro Hall; apply Hprincipal; split; [change (eval_label M w l <> []); rewrite Hlabel_eval; discriminate|].
    change (formula_holds M (All u body) (eval_label M w l)); rewrite Hlabel_eval.
    apply (pure_head M (All u body) Hpure); exact Hall. }
  (* This choice is mathematical countermodel evidence, not a generator
     choosing a quantifier term. The model's inhabitant makes [epsilon] total. *)
  set (d := epsilon (inhabits (domain_inhabitant M)) (fun d => ~ fol_holds M body (write M s u d))).
  assert (~ fol_holds M body (write M s u d)) as Hbad.
  { unfold d; apply epsilon_spec; now apply not_all_ex_not. }
  set (f := swap_values M (s v) d).
  set (w' := switch_world M v f w).
  assert (forall o, In o lhs -> ~ In v (occurrence_vars o)) as Hl_fresh by
    (intros o Hin; apply Hocc; cbn; apply in_app_iff; auto).
  assert (forall o, In o pre -> ~ In v (occurrence_vars o)) as Hpre_fresh by
    (intros o Hin; apply Hocc; cbn; rewrite !in_app_iff; auto).
  assert (forall o, In o post -> ~ In v (occurrence_vars o)) as Hpost_fresh by
    (intros o Hin; apply Hocc; cbn; rewrite !in_app_iff; auto).
  exists w'; split.
  - intro Hden; pose proof (proj1 (denote_wf _ w' Ht) Hden (Forall_nil _)) as Hraw.
    assert (left_holds M w' lhs) as Hl'.
    { unfold w'; apply (proj2 (switch_left_context M v f (swap_values_involutive M _ _) w lhs Hl_fresh)); exact Hleft. }
    specialize (Hraw Hl'); cbn [right_conclusion succedent Common.right_conclusion] in Hraw; rewrite right_app, right_cons in Hraw.
    destruct Hraw as [Hpre'|[Hinst|Hpost']].
    + apply Hpre; apply (proj1 (switch_right_context M v f (swap_values_involutive M _ _) w pre Hpre_fresh)); exact Hpre'.
    + destruct Hinst as [_ Hinst]; apply Hbad.
      apply (proj1 (eigen_instance M w l u v body d s tail Hlabel_eval Hlabel Hpure Hbody)); exact Hinst.
    + apply Hpost; apply (proj1 (switch_right_context M v f (swap_values_involutive M _ _) w post Hpost_fresh)); exact Hpost'.
  - unfold w'; apply retained_edge_switch_respects; try assumption; [apply swap_values_involutive|].
    intros o tag Hin Htag; cbn [right_conclusion succedent Common.right_conclusion] in Hin.
    apply in_app_iff in Hin as [Hin|[Heq|Hin]].
    + apply Hpre_fresh; exact Hin.
    + subst o; discriminate.
    + apply Hpost_fresh; exact Hin.
Defined.

Definition existential_left (pre post rhs : list occurrence) (l : label) (u v : nat) (body : formula)
    (Hpure : pureb body = true)
    (Hfresh : eigen_freshb v (Jdg (pre ++ post) rhs) l body = true)
    (Hs : judgment_wfb (left_conclusion pre post rhs (Occ l (Ex u body) None)) = true)
    (Ht : judgment_wfb (left_conclusion pre post rhs (Occ l (subst_fo u (Var v) body) None)) = true)
    : Cyclic.rule_instance.
Proof.
  apply (counter_rule "Ex.L"
    (left_conclusion pre post rhs (Occ l (Ex u body) None))
    (left_conclusion pre post rhs (Occ l (subst_fo u (Var v) body) None))
    (retained_edge (left_conclusion pre post rhs (Occ l (Ex u body) None))
    (left_conclusion pre post rhs (Occ l (subst_fo u (Var v) body) None)))).
  intros w Hfalse; apply eigen_freshb_spec in Hfresh.
  assert (~ In v (judgment_vars (Jdg (pre ++ post) rhs))) as Hctx by
    (intro H; apply Hfresh; apply in_app_iff; auto).
  assert (~ In v (label_vars l)) as Hlabel by
    (intro H; apply Hfresh; apply in_app_iff; right; apply in_app_iff; auto).
  assert (~ In v (formula_vars body)) as Hbody by
    (intro H; apply Hfresh; apply in_app_iff; right; apply in_app_iff; auto).
  pose proof (context_variable_fresh _ _ Hctx) as Hocc.
  destruct (false_sequent M _ _ Hfalse) as [Hadm [Hleft Hright]].
  cbn [left_conclusion antecedent Common.left_conclusion] in Hleft; rewrite left_app, left_cons in Hleft.
  destruct Hleft as [Hpre [Hprincipal Hpost]].
  destruct Hprincipal as [Hne Hprincipal]; change (eval_label M w l <> []) in Hne.
  destruct (eval_label M w l) as [|s tail] eqn:Hlabel_eval; [contradiction|].
  change (formula_holds M (Ex u body) (eval_label M w l)) in Hprincipal.
  rewrite Hlabel_eval, (pure_head M (Ex u body) Hpure) in Hprincipal.
  set (d := epsilon (inhabits (domain_inhabitant M)) (fun d => fol_holds M body (write M s u d))).
  assert (fol_holds M body (write M s u d)) as Hgood by (unfold d; apply epsilon_spec; exact Hprincipal).
  set (f := swap_values M (s v) d).
  set (w' := switch_world M v f w).
  assert (forall o, In o pre -> ~ In v (occurrence_vars o)) as Hpre_fresh by
    (intros o Hin; apply Hocc; cbn; rewrite !in_app_iff; auto).
  assert (forall o, In o post -> ~ In v (occurrence_vars o)) as Hpost_fresh by
    (intros o Hin; apply Hocc; cbn; rewrite !in_app_iff; auto).
  assert (forall o, In o rhs -> ~ In v (occurrence_vars o)) as Hr_fresh by
    (intros o Hin; apply Hocc; cbn; rewrite !in_app_iff; auto).
  exists w'; split.
  - intro Hden; pose proof (proj1 (denote_wf _ w' Ht) Hden (Forall_nil _)) as Hraw.
    assert (left_holds M w' (pre ++ Occ l (subst_fo u (Var v) body) None :: post)) as Hl'.
    { unfold left_holds; rewrite left_app, left_cons; split.
      - unfold w'; apply (proj2 (switch_left_context M v f (swap_values_involutive M _ _) w pre Hpre_fresh)); exact Hpre.
      - split.
        + split.
          * apply (wellformed_left_principal _ _ _ _ w' Ht).
          * apply (proj2 (eigen_instance M w l u v body d s tail Hlabel_eval Hlabel Hpure Hbody)); exact Hgood.
        + unfold w'; apply (proj2 (switch_left_context M v f (swap_values_involutive M _ _) w post Hpost_fresh)); exact Hpost. }
    specialize (Hraw Hl').
    apply (proj1 (switch_right_context M v f (swap_values_involutive M _ _) w rhs Hr_fresh)) in Hraw.
    destruct Hraw as [o [Hin Ho]]; apply (Hright o Hin); exact Ho.
  - unfold w'; apply retained_edge_switch_respects; try assumption; [apply swap_values_involutive|].
    intros o tag Hin Htag; apply Hr_fresh; exact Hin.
Defined.

Definition pure_terminalb j :=
  forallb (fun o => match occurrence_label o with
    | StateLabel _ => pureb o.(occurrence_formula)
    | _ => false end) (j.(antecedent) ++ j.(succedent)).

Definition atom_terminalb j :=
  forallb (fun o => match occurrence_label o, occurrence_formula o with
    | StateLabel _, Pred _ _ | StateLabel _, Equal _ _ => true
    | _, _ => false end) (j.(antecedent) ++ j.(succedent)).

(** Here the caller supplies the actual shallow sequent proof in Rocq.
    The shape checks restrict the interface but do not decide pure truth.
    [close_atoms] is the manuscript's narrower atom/equality boundary;
    [close_pure] separately permits compound pure formulas at state updates. *)
Definition close_pure j (_ : judgment_wfb j = true) (_ : pure_terminalb j = true)
    (H : forall w, left_holds M w j.(antecedent) -> right_holds M w j.(succedent))
    : Cyclic.axiom_instance.
Proof.
  refine {| Cyclic.axiom_name := "Pure.manual"; Cyclic.axiom_conclusion := j |}.
  intros w Ha Hrelations; apply H.
Defined.

Definition close_atoms j (_ : judgment_wfb j = true) (_ : atom_terminalb j = true)
    (H : forall w, left_holds M w j.(antecedent) -> right_holds M w j.(succedent))
    : Cyclic.axiom_instance.
Proof.
  refine {| Cyclic.axiom_name := "At.manual"; Cyclic.axiom_conclusion := j |}.
  intros w Ha Hrelations; apply H.
Defined.


Module SharedKernel.
  Module Core := SharedCore.
  Module Model := SharedModel.
  Include SharedRules.
End SharedKernel.
End ForModel.
End MakeRules.
Module Type KERNEL (S : SIGNATURE).
  Module Core := MakeRules S.
  Declare Module Model : Core.Pr.Sem.INTERPRETATION.
  Include Core.ForModel Model.
End KERNEL.
