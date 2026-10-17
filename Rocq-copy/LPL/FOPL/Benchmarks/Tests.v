(** * Stuttering tests and failed-execution modalities

    A test checks its guard on [s;s], so a guard containing [Next] can
    distinguish test execution from evaluating at a singleton state. Failed
    tests have no runs: their boxes are vacuous and their diamonds false.
    The last proof constructs a two-node generated certificate for that box. *)
From Stdlib Require Import List ZArith String.
From CyclistRocq.LPL.FOPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Definition s := constant_state 0.
Example successful_test : program_holds M (Test nonnegative) [s;s].
Proof. exists s; split; [reflexivity|change (0<=0)%Z; reflexivity]. Qed.
Example failed_test : ~ program_holds M (Test Falsity) [s;s].
Proof. intros [start [_ H]]; exact (H I). Qed.
(** This guard is intentionally temporal rather than pure arithmetic. Its
    success on a stutter checks that tests use the full formula semantics. *)
Example singleton_sensitive_guard : ~ formula_holds M (Next Truth) [s].
Proof. apply next_singleton. Qed.
Example stutter_sensitive_guard : formula_holds M (Next Truth) [s;s].
Proof. apply (proj2 (suffix_step M s [s] Falsity Truth ltac:(discriminate))); now left. Qed.
Example sensitive_test_uses_stutter : program_holds M (Test (Next Truth)) [s;s].
Proof. exists s; split; [reflexivity|exact stutter_sensitive_guard]. Qed.
Example failed_box_is_vacuous : formula_holds M (Box (Test Falsity) Falsity) [s].
Proof. apply (proj2 (box_test M [] s Falsity Falsity)); cbn; tauto. Qed.
Example failed_diamond_is_false : ~ formula_holds M (Diamond (Test Falsity) Truth) [s].
Proof. rewrite (diamond_test M [] s Falsity Truth); cbn; tauto. Qed.
(** Box-test-right adds the false guard to the premise antecedent. That
    premise closes by false-left; no proof of the postcondition is needed
    because there is no successful execution of the test. *)
Definition root := Jdg [] [traced (Join Empty l0) (Box (Test Falsity) Falsity) 0].
Definition rule := requested root (Local OnRight 0 "B.Test.R") ltac:(vm_compute; reflexivity).
Definition leaf := premise_at rule 0.
Definition ax := generated_axiom leaf ltac:(vm_compute; reflexivity).
Definition build := Cyclic.run_script root [Cyclic.ApplyRule 0 rule;Cyclic.CloseWith 1 ax].
Theorem failed_test_box_valid : Cyclic.Valid root.
Proof. apply (raw_check_sound build.(Cyclic.built_graph) empty_trace_witness); vm_compute; reflexivity. Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.

Print Assumptions failed_test_box_valid.
