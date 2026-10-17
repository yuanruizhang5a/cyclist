(** * Two possible successors, a false box, and a genuine dead end. *)
From Stdlib Require Import List.
From CyclistRocq.LPL.Benchmarks.PPL Require Import Support.
Import ListNotations.
Example acquire_held : program_holds M (act Acquire) [Idle;Held].
Proof. exists Idle, Held; repeat split; auto. Qed.
Example acquire_released : program_holds M (act Acquire) [Idle;Released].
Proof. exists Idle, Released; repeat split; auto. Qed.
Theorem both_branches_safe : formula_holds M (Box (act Acquire) (Next safe)) [Idle].
Proof.
  apply (proj2 (box_atomic M [] Idle Acquire tt (Next safe))).
  intros next Hstep; apply (proj2 (suffix_step M Idle [next] Falsity safe ltac:(discriminate))); left.
  change (next<>Bad); destruct Hstep as [_ [Hnext | Hnext]]; subst next; discriminate.
Qed.
Theorem one_branch_witnesses_diamond : formula_holds M (Diamond (act Acquire) (Next (atom IsHeld))) [Idle].
Proof.
  apply (proj2 (diamond_atomic M [] Idle Acquire tt (Next (atom IsHeld)))); exists Held; split; [split; auto|].
  apply (proj2 (suffix_step M Idle [Held] Falsity (atom IsHeld) ltac:(discriminate))); left; reflexivity.
Qed.
Theorem not_every_branch_is_held : ~ formula_holds M (Box (act Acquire) (Next (atom IsHeld))) [Idle].
Proof.
  intro Hbox; pose proof ((proj1 (box_atomic M [] Idle Acquire tt (Next (atom IsHeld)))) Hbox Released ltac:(split; auto)) as H.
  apply (proj1 (suffix_step M Idle [Released] Falsity (atom IsHeld) ltac:(discriminate))) in H.
  destruct H as [Heq|[Hfalse _]]; [change (Released=Held) in Heq; discriminate|exact Hfalse].
Qed.
Example dead_end_box_vacuous : formula_holds M (Box (act Acquire) Falsity) [Dead].
Proof. apply (proj2 (box_atomic M [] Dead Acquire tt Falsity)); intros next [H _]; discriminate. Qed.
Example dead_end_diamond_false : ~ formula_holds M (Diamond (act Acquire) Truth) [Dead].
Proof. intro H; apply (proj1 (diamond_atomic M [] Dead Acquire tt Truth)) in H; destruct H as [next [[H _] _]]; discriminate. Qed.
Print Assumptions both_branches_safe.
Print Assumptions one_branch_witnesses_diamond.
Print Assumptions not_every_branch_is_held.

Definition root := Jdg [assertion l0 (atom IsIdle)] [assertion l0 (Box (act Acquire) (Next safe))].
Theorem nondeterministic_box_valid : Cyclic.Valid root.
Proof.
  intros w Ha Hrelations Hleft; pose proof (proj1 (left_singleton w _) Hleft) as [_ Hinitial].
  change (eval_update M w 0 = Idle) in Hinitial.
  exists (assertion l0 (Box (act Acquire) (Next safe))); split; [now left|].
  split; [discriminate|]. change (formula_holds M (Box (act Acquire) (Next safe)) [eval_update M w 0]).
  rewrite Hinitial; exact both_branches_safe.
Qed.
Example actual_initial_condition : left_holds M (constant_world Idle) root.(antecedent).
Proof. repeat constructor; discriminate. Qed.
Example admissible_initial_condition : admissible M root (constant_world Idle).
Proof. apply judgment_wfb_admissible; reflexivity. Qed.
Print Assumptions nondeterministic_box_valid.
