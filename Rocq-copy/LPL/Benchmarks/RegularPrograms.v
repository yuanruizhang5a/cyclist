From Stdlib Require Import List ZArith.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Definition s0 := constant_state 0.
Definition s1 := write M s0 0 1%Z.
Definition s2 := write M s1 1 1%Z.
Definition p := Assign 0 one.
Definition q := Assign 1 x.
Example two_assignment_sequence : program_holds M (Seq p q) [s0;s1;s2].
Proof.
  exists [s0;s1], [s1;s2]; split; [exists s0; reflexivity|].
  split; [exists s1; reflexivity|]. exists [s0], s1, [s2]; auto.
Qed.
Example nondeterministic_left : program_holds M (Choice p (Assign 0 zero)) [s0;s1].
Proof. left; exists s0; reflexivity. Qed.
Example nondeterministic_right : program_holds M (Choice p (Assign 0 zero)) [s0;s0].
Proof. right; exists s0; change ([s0;s0] = [s0;write M s0 0 (s0 0)]); now rewrite write_current. Qed.
Example star_zero : program_holds M (Star p) [s0;s0].
Proof. exists 0, s0; reflexivity. Qed.
Example star_one_has_final_stutter : program_holds M (Star p) [s0;s1;s1].
Proof.
  exists 1, [s0;s1], [s1;s1]; split; [exists s0; reflexivity|].
  split; [exists s1; reflexivity|]. exists [s0], s1, [s1]; auto.
Qed.
Example nested_iteration : program_holds M (Star (Star p)) [s0;s0;s0].
Proof.
  exists 1, [s0;s0], [s0;s0]; split; [exists 0, s0; reflexivity|].
  split; [exists s0; reflexivity|]. exists [s0], s0, [s0]; auto.
Qed.
Definition root := Jdg [assertion l0 nonnegative]
  [assertion l0 (Box (Choice (Seq p q) (Star p)) (First nonnegative))].
Theorem regular_program_preserves_first_observation : Cyclic.Valid root.
Proof.
  intros w Ha Hleft; pose proof (proj1 (left_singleton w _) Hleft) as [_ Hinitial].
  exists (assertion l0 (Box (Choice (Seq p q) (Star p)) (First nonnegative))); split; [now left|].
  split; [discriminate|]. intros execution result Hprogram Ho.
  apply overlap_list_singleton in Ho as [tail [Heq ->]]; subst execution.
  exact Hinitial.
Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.

Print Assumptions regular_program_preserves_first_observation.
