(** * Concrete executions of regular programs

    Construct assignment, sequence, choice and finite-star traces directly
    from their semantic witnesses. Star includes its zero-power final
    stutter, which explains the extra endpoint in positive-iteration traces.
    The final validity is a first-state observation, not an all-state safety
    claim; CounterLoop.v and NestedProgram.v prove the latter kind. *)
From Stdlib Require Import List ZArith.
From CyclistRocq.LPL.FOPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Definition s0 := constant_state 0.
Definition s1 := write M s0 0 1%Z.
Definition s2 := write M s1 1 1%Z.
Definition p := Assign 0 one.
Definition q := Assign 1 x.
(** The second assignment reads the state after the first. The sequence
    witness gives each two-state execution and their shared middle endpoint. *)
Example two_assignment_sequence : program_holds M (Seq p q) [s0;s1;s2].
Proof.
  exists [s0;s1], [s1;s2]; split; [exists s0; reflexivity|].
  split; [exists s1; reflexivity|]. exists [s0], s1, [s2]; auto.
Qed.
Example nondeterministic_left : program_holds M (Choice p (Assign 0 zero)) [s0;s1].
Proof. left; exists s0; reflexivity. Qed.
Example nondeterministic_right : program_holds M (Choice p (Assign 0 zero)) [s0;s0].
Proof. right; exists s0; change ([s0;s0] = [s0;write M s0 0 (s0 0)]); now rewrite write_current. Qed.
(** Existential witnesses choose the finite iteration count explicitly.
    For nested star, one outer iteration may itself use zero inner iterations. *)
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
(** Extending a trace never changes its first state. The proof therefore
    uses only the overlap endpoint/head equation, independent of which
    nondeterministic branch or finite iteration count was chosen. *)
Theorem regular_program_preserves_first_observation : Cyclic.Valid root.
Proof.
  intros w Ha Hrelations Hleft; pose proof (proj1 (left_singleton w _) Hleft) as [_ Hinitial].
  exists (assertion l0 (Box (Choice (Seq p q) (Star p)) (First nonnegative))); split; [now left|].
  split; [discriminate|]. intros execution result Hprogram Ho.
  apply overlap_list_singleton in Ho as [tail [Heq ->]]; subst execution.
  exact Hinitial.
Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.

Print Assumptions regular_program_preserves_first_observation.
