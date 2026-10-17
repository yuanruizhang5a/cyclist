(** * Regular programs retain finite traces and the zero-iteration stutter. *)
From Stdlib Require Import List.
From CyclistRocq.LPL.Benchmarks.PPL Require Import Support Nondeterminism.
Import ListNotations.
Definition p := act Acquire.
Definition q := act Release.
Example sequence_run : program_holds M (Seq p q) [Idle;Held;Released].
Proof.
  exists [Idle;Held], [Held;Released]; split; [exact acquire_held|].
  split; [exists Held, Released; split; [reflexivity|split; reflexivity]|].
  exists [Idle], Held, [Released]; auto.
Qed.
Example both_choice_branches : program_holds M (Choice p (act Stutter)) [Idle;Held] /\
  program_holds M (Choice p (act Stutter)) [Idle;Idle].
Proof. split; [left; exact acquire_held|right; exists Idle, Idle; repeat split; discriminate]. Qed.
Example star_zero_stutters : program_holds M (Star p) [Idle;Idle].
Proof. exists 0; exists Idle; reflexivity. Qed.
Example star_zero_is_not_singleton : ~ finite_power M (program_holds M p) 0 [Idle].
Proof. intros [s H]; discriminate. Qed.
Example star_one_has_final_stutter : program_holds M (Star p) [Idle;Held;Held].
Proof.
  exists 1; exists [Idle;Held], [Held;Held]; split; [exact acquire_held|].
  split; [exists Held; reflexivity|]. exists [Idle], Held, [Held]; auto.
Qed.
Example nested_star_zero : program_holds M (Star (Star p)) [Idle;Idle].
Proof. exists 0; exists Idle; reflexivity. Qed.
Definition root := Jdg [assertion l0 safe]
  [assertion l0 (Box (Choice (Seq p q) (Star (Choice p (act Stutter)))) (First safe))].
Theorem regular_program_preserves_first_observation : Cyclic.Valid root.
Proof.
  intros w Ha Hrelations Hleft; pose proof (proj1 (left_singleton w _) Hleft) as [_ Hinitial].
  exists (assertion l0 (Box (Choice (Seq p q) (Star (Choice p (act Stutter)))) (First safe))); split; [now left|].
  split; [discriminate|]. intros execution result Hprogram Ho.
  apply overlap_list_singleton in Ho as [tail [Heq ->]]; subst execution; exact Hinitial.
Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.
Print Assumptions regular_program_preserves_first_observation.
