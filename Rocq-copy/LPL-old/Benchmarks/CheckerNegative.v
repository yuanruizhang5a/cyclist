(** * Why building a graph is weaker than certifying it

    All local rule records below have genuine semantic proofs. We deliberately
    arrange malformed or nonprogressing graphs around them to show which
    builder/structural/witness checks reject them. No invalid soundness lemma
    is postulated, and a successful [build_ok] is never used as validity. *)
From Stdlib Require Import List Bool Arith String.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Definition root := Jdg [] [traced l0 (Box (Test Truth) Falsity) 0].
Definition exact := requested root (BacklinkExact root) ltac:(vm_compute; reflexivity).
(** Identity followed by a backlink makes a closed, structurally correct
    cycle, but provides no strict semantic decrease. Constant potentials
    cannot justify its nonprogressing loop, so the full raw check rejects it. *)
Definition cyclic_build := Cyclic.run_script root [Cyclic.ApplyRule 0 exact;Cyclic.AddBacklink 1 0 exact].
Definition cyclic_graph := cyclic_build.(Cyclic.built_graph).
Definition witness : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := fun _ => Some 0; Cyclic.witness_potential := fun _ => 0 |}.
Example nonprogressing_cycle_builds : cyclic_build.(Cyclic.build_ok) = true. Proof. vm_compute; reflexivity. Qed.
Example nonprogressing_cycle_is_structural : Cyclic.structural_check cyclic_graph = true. Proof. vm_compute; reflexivity. Qed.
Example nonprogressing_cycle_rejected : Cyclic.raw_check cyclic_graph witness = false. Proof. vm_compute; reflexivity. Qed.
Example open_node_rejected : Cyclic.raw_check (Cyclic.start_graph root) witness = false. Proof. vm_compute; reflexivity. Qed.
Definition dangling : Cyclic.graph := {| Cyclic.graph_root := root;
  Cyclic.graph_nodes := [{| Cyclic.node_judgment := root; Cyclic.node_payload := Cyclic.RuleNode exact [99] |}] |}.
Example dangling_rejected : Cyclic.raw_check dangling witness = false. Proof. vm_compute; reflexivity. Qed.
Definition bad_edge : Cyclic.edge_info := {| Cyclic.edge_valid := [(99,99)]; Cyclic.edge_progress := [] |}.
(** The absent tag 99 has fallback rank zero on both sides, so this identity
    edge satisfies the purely semantic inequalities. Its endpoint metadata is
    nevertheless syntactically invalid: tag 99 occurs in neither judgment.
    This separates semantic record construction from edge well-formedness,
    which both the generator boundary and full checker must enforce. *)
Definition malformed_tag_rule : Cyclic.rule_instance.
Proof.
  apply (counter_rule "Negative.absent-tag" root root bad_edge).
  intros w H; exists w; split; [exact H|]. split.
  - intros a b [Heq|Hno]; [inversion Heq; subst; apply Nat.le_refl|contradiction].
  - intros a b Hno; contradiction.
Defined.
Definition malformed_build := Cyclic.run_script root [Cyclic.ApplyRule 0 malformed_tag_rule;Cyclic.AddBacklink 1 0 exact].
Example malformed_tag_graph_builds : malformed_build.(Cyclic.build_ok) = true. Proof. vm_compute; reflexivity. Qed.
Example malformed_tag_edge_rejected :
  Cyclic.raw_check malformed_build.(Cyclic.built_graph) witness = false.
Proof. vm_compute; reflexivity. Qed.
Example generator_boundary_rejects_absent_tags : someb (ensure_rule root (Some malformed_tag_rule)) = false.
Proof. vm_compute; reflexivity. Qed.
(** Builder failures are more immediate: a closing record must have the
    node's exact conclusion, and a backlink must name an eligible earlier
    companion. Logical truth of some other judgment cannot repair a mismatch. *)
Definition true_root := Jdg [] [assertion l0 Truth].
Definition true_axiom := generated_axiom true_root ltac:(vm_compute; reflexivity).
Example mismatched_axiom_rejected :
  (Cyclic.run_script root [Cyclic.CloseWith 0 true_axiom]).(Cyclic.build_ok) = false.
Proof. vm_compute; reflexivity. Qed.
Example mismatched_rule_rejected :
  (Cyclic.run_script true_root [Cyclic.ApplyRule 0 exact]).(Cyclic.build_ok) = false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_companion_rejected :
  (Cyclic.run_script root [Cyclic.ApplyRule 0 exact;Cyclic.AddBacklink 1 1 exact]).(Cyclic.build_ok) = false.
Proof. vm_compute; reflexivity. Qed.
