(** * Quantifier proofs, capture avoidance and eigenvariable freshness

    The first two-node graph proves universal reflexivity using an explicit
    fresh variable and a manual atomic leaf. The remaining examples explain
    why substitution renames binders and why eigenvariable freshness must
    inspect labels as well as formula bodies and surrounding contexts. *)
From Stdlib Require Import List ZArith String.
From CyclistRocq.LPL.FOPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.

Definition quantified := All 0 (Equal x x).
Definition root := Jdg [] [assertion l0 quantified].
(** Choose program variable 1 as the eigenvariable for binder 0. The generator
    checks this concrete choice, then the premise is the familiar [y = y]. *)
Definition rule := requested root (Eigen OnRight 0 1) ltac:(vm_compute; reflexivity).
Definition leaf := Jdg [] [assertion l0 (Equal y y)].
Definition ax : Cyclic.axiom_instance.
Proof.
  refine (close_atoms leaf eq_refl eq_refl _); intros w Hleft.
  exists (assertion l0 (Equal y y)); split; [now left|]; split; [discriminate|reflexivity].
Defined.
Definition build := Cyclic.run_script root [Cyclic.ApplyRule 0 rule;Cyclic.CloseWith 1 ax].
Theorem universal_reflexivity : Cyclic.Valid root.
Proof. apply (raw_check_sound build.(Cyclic.built_graph) empty_trace_witness); vm_compute; reflexivity. Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.

(** Substituting [y] for [x] in [forall y, x = y] must rename the old bound
    [y] first. The result has fresh binder 2, with the replacement [y] still
    free. The semantic examples contrast it with the naively captured tautology.
    Shadowing is different: [forall x] blocks substitution for [x] entirely. *)
Example capture_is_avoided : formula_eq_dec
  (subst_fo 0 y (All 1 (Equal x y))) (All 2 (Equal y (Var 2))) = left eq_refl.
Proof. reflexivity. Qed.
Example shadowed_variable_is_not_substituted :
  pureb (subst_fo 0 one (All 0 (Equal x zero))) = true /\
  fol_size (subst_fo 0 one (All 0 (Equal x zero))) = fol_size (All 0 (Equal x zero)).
Proof. split; reflexivity. Qed.
Example captured_formula_differs_semantically :
  ~ fol_holds M (subst_fo 0 y (All 1 (Equal x y))) (constant_state 0).
Proof. intro H; specialize (H 1%Z); discriminate. Qed.
Example naive_capture_would_be_true : fol_holds M (All 1 (Equal y y)) (constant_state 0).
Proof. intro d; reflexivity. Qed.
Example nested_shadowing : formula_wfb (All 0 (Impl (Pred 0 [x]) (Ex 0 (Equal x x)))) = true.
Proof. reflexivity. Qed.

(** The pre-adoption eigenvariable example is retained as a countermodel,
    without constructing an unsound inference record. The label itself sets
    [y] to zero, so the proposed premise [y = 0] holds regardless of the base
    environment. Its proposed conclusion [forall x, x = 0] is false over
    integers. Rejecting this eigenvariable prevents that invalid inference. *)
Definition bad_label := StateLabel (AssignUpdate 1 zero u0).
Definition bad_conclusion := Jdg [] [assertion bad_label (All 0 (Equal x zero))].
Definition bad_premise := Jdg [] [assertion bad_label (Equal y zero)].
Lemma bad_premise_is_valid : Cyclic.Valid bad_premise.
Proof.
  intros w Ha Hrelations Hl; exists (assertion bad_label (Equal y zero)); split; [now left|];
    split; [discriminate|reflexivity].
Qed.
Lemma bad_conclusion_has_admissible_countermodel :
  admissible M bad_conclusion (constant_world 0) /\ ~ denote M bad_conclusion (constant_world 0).
Proof.
  split; [apply judgment_wfb_admissible; reflexivity|].
  intro H; specialize (H ltac:(apply judgment_wfb_admissible; reflexivity) ltac:(constructor) ltac:(constructor)).
  destruct H as [o [[Heq|[]] [_ Hholds]]]; subst o.
  specialize (Hholds 1%Z); discriminate.
Qed.
Example stale_label_eigenvariable_rejected :
  someb (generate_requested bad_conclusion (Eigen OnRight 0 1)) = false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions universal_reflexivity.
