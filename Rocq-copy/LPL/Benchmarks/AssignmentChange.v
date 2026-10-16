From Stdlib Require Import List Bool Arith ZArith String.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Open Scope list_scope.

Definition postcondition := Equal x one.
Definition updated := AssignUpdate 0 one u0.
Definition root := Jdg [] [traced (Join Empty l0) (Box (Assign 0 one) (Next postcondition)) 0].
Definition assign_rule := requested root (Local OnRight 0 "B.Assign.R") ltac:(vm_compute; reflexivity).
Definition with_unit := premise_at assign_rule 0.
Definition suffix_goal := Jdg [] [traced (Join l0 (StateLabel updated)) (Next postcondition) 0].
Definition unit_rule := requested with_unit (UnitLabels suffix_goal [false] true true) ltac:(vm_compute; reflexivity).
Definition suffix_rule := requested suffix_goal (Local OnRight 0 "Suffix.R") ltac:(vm_compute; reflexivity).
Definition first_leaf := Jdg [] [assertion (StateLabel updated) postcondition; assertion (StateLabel updated) Falsity].
Definition second_goal := premise_at suffix_rule 1.
Definition weakening := requested second_goal (Weaken OnRight 1) ltac:(vm_compute; reflexivity).
Definition final_leaf := Jdg [] [assertion (StateLabel updated) postcondition].

Definition close_first : Cyclic.axiom_instance.
Proof.
  refine (close_pure first_leaf eq_refl eq_refl _).
  intros w H; exists (assertion (StateLabel updated) postcondition); split; [now left|].
  split; [discriminate|reflexivity].
Defined.
Definition close_final : Cyclic.axiom_instance.
Proof.
  refine (close_atoms final_leaf eq_refl eq_refl _).
  intros w H; exists (assertion (StateLabel updated) postcondition); split; [now left|].
  split; [discriminate|reflexivity].
Defined.
Definition build := Cyclic.run_script root [Cyclic.ApplyRule 0 assign_rule; Cyclic.ApplyRule 1 unit_rule;
  Cyclic.ApplyRule 2 suffix_rule; Cyclic.CloseWith 3 close_first; Cyclic.ApplyRule 4 weakening;
  Cyclic.CloseWith 5 close_final].
Definition graph := build.(Cyclic.built_graph).
Example builder_ok : build.(Cyclic.build_ok) = true. Proof. vm_compute; reflexivity. Qed.
Example first_suffix_edge_has_no_progress :
  match nth_error suffix_rule.(Cyclic.rule_premises) 0 with
  | Some p => p.(Cyclic.premise_edge).(Cyclic.edge_progress) | None => [(42,42)] end = [].
Proof. vm_compute; reflexivity. Qed.
Example continuing_suffix_edge_progresses :
  match nth_error suffix_rule.(Cyclic.rule_premises) 1 with
  | Some p => p.(Cyclic.premise_edge).(Cyclic.edge_progress) | None => [] end = [(0,0)].
Proof. vm_compute; reflexivity. Qed.
Example accepted : Cyclic.raw_check graph empty_trace_witness = true.
Proof. vm_compute; reflexivity. Qed.
Theorem assignment_changes_next_value : Cyclic.Valid root.
Proof. exact (raw_check_sound graph empty_trace_witness accepted). Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.
Print Assumptions assignment_changes_next_value.
