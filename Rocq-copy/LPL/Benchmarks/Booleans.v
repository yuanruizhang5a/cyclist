From Stdlib Require Import List String.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Definition modal := Box (Test Truth) Truth.
Definition root := Jdg [] [assertion l0 (Impl modal (Disj modal (Neg modal)))].
Definition impl_rule := requested root (Local OnRight 0 "Impl.R") ltac:(vm_compute; reflexivity).
Definition disj_goal := premise_at impl_rule 0.
Definition disj_rule := requested disj_goal (Local OnRight 0 "Or.R") ltac:(vm_compute; reflexivity).
Definition leaf := premise_at disj_rule 0.
Definition ax := generated_axiom leaf ltac:(vm_compute; reflexivity).
Definition build := Cyclic.run_script root [Cyclic.ApplyRule 0 impl_rule;Cyclic.ApplyRule 1 disj_rule;Cyclic.CloseWith 2 ax].
Theorem mixed_boolean_valid : Cyclic.Valid root.
Proof. apply (raw_check_sound build.(Cyclic.built_graph) empty_trace_witness); vm_compute; reflexivity. Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.
Print Assumptions mixed_boolean_valid.
