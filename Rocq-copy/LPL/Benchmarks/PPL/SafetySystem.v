(** * All visited states of every finite protocol execution stay safe.
    This is a direct semantic proof, separate from the cyclic certificates. *)
From Stdlib Require Import List.
From CyclistRocq.LPL Require Import TraceSafety.
From CyclistRocq.LPL.Benchmarks.PPL Require Import Support.
Import ListNotations.
Module Safety := MakeSafety Machine.Language Machine.Syn Machine.Sem.
Definition Inv (s : machine_state) := s<>Bad.
Lemma actions_preserve action s t : interpret_action M action s t -> Inv s -> Inv t.
Proof. intros Hstep Hsafe; exact (action_safe action s t Hsafe Hstep). Qed.
Lemma every_program_safe p : trace_safe Inv (program_holds M p).
Proof. exact (Safety.program_safe M Inv actions_preserve p). Qed.
Lemma always_safe tr : tr<>[] -> (formula_holds M (Always safe) tr <-> Forall Inv tr).
Proof. intro Hne; exact (Safety.always_head_forall M safe ltac:(intros s tail; reflexivity) tr Hne). Qed.
Definition protocol := Choice (act Acquire) (Choice (act Release) (Choice (act Reset) (act Stutter))).
Definition root := Jdg [assertion l0 safe] [assertion l0 (Box (Star protocol) (Always safe))].
Theorem every_visited_state_safe : Cyclic.Valid root.
Proof.
  intros w Ha Hrelations Hleft; pose proof (proj1 (left_singleton w _) Hleft) as [_ Hinitial].
  exists (assertion l0 (Box (Star protocol) (Always safe))); split; [now left|].
  split; [discriminate|]. intros execution result Hprogram Ho.
  apply overlap_list_singleton in Ho as [tail [Heq ->]]; subst execution.
  apply (proj2 (always_safe (eval_update M w 0 :: tail) ltac:(discriminate))); eapply every_program_safe; eauto.
Qed.
Example may_stop_immediately : program_holds M (Star protocol) [Idle;Idle].
Proof. exists 0; exists Idle; reflexivity. Qed.
Example may_stop_while_held : program_holds M (Star protocol) [Idle;Held;Held].
Proof.
  exists 1; exists [Idle;Held], [Held;Held]; split.
  - left; exists Idle, Held; repeat split; auto.
  - split; [exists Held; reflexivity|]. exists [Idle], Held, [Held]; auto.
Qed.
Example root_is_admissible : admissible M root (constant_world Idle).
Proof. apply judgment_wfb_admissible; reflexivity. Qed.
Example root_antecedent_holds : left_holds M (constant_world Idle) root.(antecedent).
Proof. repeat constructor; discriminate. Qed.
Print Assumptions every_visited_state_safe.
