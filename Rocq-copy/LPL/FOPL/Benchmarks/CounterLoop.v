(** * A guarded decrement loop safe at every visited state

    This is a direct semantic invariant proof, separate from the cyclic
    prefix certificate in Cyclic.v. Prove one step safe, lift it to every
    finite iteration count with TraceSafety.v, then translate all-state
    safety into the object-language [Always] postcondition. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.FOPL.Benchmarks Require Import Support.
From CyclistRocq.LPL Require Import TraceSafety.
Import ListNotations Generation Cert.

Definition positive := Pred 2 [zero;x].
Definition loop_step := Seq (Test positive) (Assign 0 (dec x)).
Definition inv (s : state M) := (0 <= s 0%nat)%Z.

(** Unfold the test/assignment executions and their overlap to expose all
    three visited states: the guard stutter and the decremented state.
    The strict guard gives exactly the arithmetic premise needed for [lia]
    to show that subtracting one preserves nonnegativity. *)
Lemma step_safe : trace_safe inv (program_holds M loop_step).
Proof.
  intros s tail [testtrace [assigntrace [Htest [Hassign Ho]]]] Hinitial.
  destruct Htest as [start [Htest Hguard]]; subst testtrace.
  destruct Hassign as [start' Hassign]; subst assigntrace.
  apply (overlap_snoc M [start] start start') in Ho.
  destruct Ho as [Heq Htrace]; subst start'.
  change (s :: tail = [start;start;write M start 0 (eval_term M start (dec x))]) in Htrace.
  injection Htrace as Hs Htail; subst s tail.
  change (0 < start 0%nat)%Z in Hguard.
  repeat constructor; unfold inv in *; try assumption.
  change (0 <= start 0%nat - 1)%Z; lia.
Qed.

(** [n] remains arbitrary. [change] uses definitional equality of the generic
    trace-power helper and the model's finite-power semantics, allowing reuse
    of the proved compositional safety lemma. *)
Lemma every_finite_stop n s tail :
  finite_power M (program_holds M loop_step) n (s :: tail) -> inv s -> Forall inv (s :: tail).
Proof.
  change (trace_power (program_holds M loop_step) n (s :: tail) -> inv s -> Forall inv (s :: tail)).
  apply (power_safe inv (program_holds M loop_step) step_safe n).
Qed.

Definition root := Jdg [assertion l0 nonnegative]
  [assertion l0 (Box (Star loop_step) (Always nonnegative))].
(** The initial singleton label aligns the star execution with its result.
    [always_pure_forall] then reduces the temporal claim to [Forall inv] over
    the complete execution, including intermediate test and assignment states. *)
Theorem guarded_counter_all_visited_nonnegative : Cyclic.Valid root.
Proof.
  intros w Hadm Hrelations Hleft.
  pose proof (proj1 (left_singleton w _) Hleft) as [_ Hinitial].
  exists (assertion l0 (Box (Star loop_step) (Always nonnegative))); split; [now left|].
  split; [discriminate|].
  change (formula_holds M (Box (Star loop_step) (Always nonnegative)) [eval_update M w u0]).
  intros execution result [n Hpower] Ho.
  apply overlap_list_singleton in Ho as [tail [Heq ->]]; subst execution.
  apply (always_pure_forall M nonnegative); [reflexivity|discriminate|].
  exact (every_finite_stop n (eval_update M w u0) tail Hpower Hinitial).
Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.

(** The guard does not force a star execution to reach zero: stopping at the
    zero-iteration stutter is allowed even when the counter starts at seven. *)
Example may_stop_before_exit : program_holds M (Star loop_step) [constant_state 7;constant_state 7].
Proof. exists 0, (constant_state 7); reflexivity. Qed.
Example zero_iterations_stutter s : finite_power M (program_holds M loop_step) 0 [s;s].
Proof. exists s; reflexivity. Qed.
Example zero_iterations_not_identity s : ~ finite_power M (program_holds M loop_step) 0 [s].
Proof. intros [t H]; discriminate. Qed.
Print Assumptions guarded_counter_all_visited_nonnegative.
