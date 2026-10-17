(** * Temporal operators on finite traces

    Immediate and postponed suffix witnesses illustrate the one-step suffix
    equation. Next cannot postpone, and at a singleton it is false. Dual
    suffix has the complementary singleton boundary. These are finite-trace
    facts, not imported laws for infinite temporal streams. *)
From Stdlib Require Import List.
From CyclistRocq.LPL.Benchmarks.PPL Require Import Support.
Import ListNotations Generation Cert.
Definition s0 := Idle.
Definition s1 := Held.
Example suffix_immediate : formula_holds M (Suffix Truth (atom IsIdle)) [s1;s0].
Proof. apply (proj2 (suffix_step M s1 [s0] Truth (atom IsIdle) ltac:(discriminate))); left; reflexivity. Qed.
Example suffix_postponed : formula_holds M (Suffix Truth (atom IsIdle)) [s1;s1;s0].
Proof.
  apply (proj2 (suffix_step M s1 [s1;s0] Truth (atom IsIdle) ltac:(discriminate))).
  right; split; [exact I|exact suffix_immediate].
Qed.
Example next_cannot_postpone : ~ formula_holds M (Next (atom IsIdle)) [s1;s1;s0].
Proof. rewrite (suffix_step M s1 [s1;s0] Falsity (atom IsIdle)) by discriminate; cbn; intuition discriminate. Qed.
Example suffix_singleton_failure : ~ formula_holds M (Suffix Truth (atom IsIdle)) [s0].
Proof. apply suffix_singleton. Qed.
Example next_at_end : ~ formula_holds M (Next Truth) [s0].
Proof. apply next_singleton. Qed.
Example dual_suffix_singleton_success : formula_holds M (DualSuffix Falsity Falsity) [s0].
Proof. apply dual_suffix_singleton. Qed.
Example dual_suffix_success : formula_holds M (DualSuffix Falsity (atom IsIdle)) [s1;s0].
Proof.
  apply (proj2 (dual_suffix_step M s1 [s0] Falsity (atom IsIdle) ltac:(discriminate))).
  split; [reflexivity|right; apply dual_suffix_singleton].
Qed.
(** [First] evaluates its complete body on a singleton, so even an original
    two-state stutter cannot make the nested [Next] true. *)
Example compound_first_state : ~ formula_holds M (First (Conj Truth (Next Truth))) [s0;s0].
Proof. intros [_ H]; exact (next_singleton M Truth s0 H). Qed.
(** The accumulated traces have lengths 1, 2 and 3. Their rank measure is
    1+2+3, not the number of history components. This checks the convention
    underlying Progress.v's minimum-counterexample inequalities. *)
Example sum_of_component_lengths : sequence_measure (execution_history [s0] [s1;s0]) = 6.
Proof. reflexivity. Qed.
Example execution_count_is_different : List.length (execution_history [s0] [s1;s0]) = 3.
Proof. reflexivity. Qed.
(** A suffix assertion at a singleton cannot hold. Used as an antecedent,
    it closes the sequent even with an empty succedent. The generated
    singleton-suffix axiom is certified as a one-node graph. *)
Definition root := Jdg [assertion l0 (Suffix Truth (atom IsIdle))] [].
Definition ax := generated_axiom root ltac:(vm_compute; reflexivity).
Theorem singleton_suffix_closes : Cyclic.Valid root.
Proof. exact (raw_check_sound (axiom_graph ax) empty_trace_witness (axiom_graph_raw_check ax)). Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.

Print Assumptions singleton_suffix_closes.
