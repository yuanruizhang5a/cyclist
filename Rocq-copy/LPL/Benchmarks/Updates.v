From Stdlib Require Import List ZArith.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Definition w := constant_world 0.
Definition first_update := AssignUpdate 0 (inc x) u0.
Definition second_update := AssignUpdate 0 (inc x) first_update.
Definition dependent_update := AssignUpdate 1 (plus x one) first_update.
Example identity_assignment : eval_update M w (AssignUpdate 0 x u0) 0 = 0%Z.
Proof. reflexivity. Qed.
Example assignment_changes_value : eval_update M w first_update 0 = 1%Z.
Proof. reflexivity. Qed.
Example reads_previous_update : eval_update M w second_update 0 = 2%Z.
Proof. reflexivity. Qed.
Example dependent_assignments : eval_update M w dependent_update 1 = 2%Z.
Proof. reflexivity. Qed.
Example other_variable_unchanged : eval_update M w dependent_update 0 = 1%Z.
Proof. reflexivity. Qed.
Example every_intermediate_state_retained :
  map (fun s : state M => s 0) (eval_label M w (Join (Join l0 (StateLabel first_update)) (StateLabel second_update))) = [0%Z;1%Z;2%Z].
Proof. reflexivity. Qed.
Definition grounded := Jdg [] [assertion (StateLabel (AssignUpdate 0 one (AssignUpdate 0 zero u0))) (Equal x one)].
Definition grounded_ax : Cyclic.axiom_instance.
Proof.
  refine (close_atoms grounded eq_refl eq_refl _); intros world Hleft.
  exists (assertion (StateLabel (AssignUpdate 0 one (AssignUpdate 0 zero u0))) (Equal x one));
    split; [now left|]; split; [discriminate|reflexivity].
Defined.
Theorem dependent_update_terminal_valid : Cyclic.Valid grounded.
Proof. exact (raw_check_sound (axiom_graph grounded_ax) empty_trace_witness (axiom_graph_raw_check grounded_ax)). Qed.
Example nonvacuity : exists world, admissible M grounded world.
Proof. apply root_nonvacuous; reflexivity. Qed.

Print Assumptions dependent_update_terminal_valid.
