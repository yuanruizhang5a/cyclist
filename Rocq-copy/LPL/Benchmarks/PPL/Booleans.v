(** * A first complete generated proof script

    Prove [modal -> modal or not modal] without unfolding the modality.
    Read the successive goal/rule/leaf definitions, then the script: node 0
    uses implication-right, node 1 disjunction-right, and node 2 identity.
    [vm_compute] verifies these fixed choices; it does not search for them. *)
From Stdlib Require Import List String.
From CyclistRocq.LPL.Benchmarks.PPL Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Definition modal := Box (Test Truth) Truth.
Definition root := Jdg [] [assertion l0 (Impl modal (Disj modal (Neg modal)))].
Definition impl_rule := requested root (Local OnRight 0 "Impl.R") ltac:(vm_compute; reflexivity).
Definition disj_goal := premise_at impl_rule 0.
Definition disj_rule := requested disj_goal (Local OnRight 0 "Or.R") ltac:(vm_compute; reflexivity).
Definition leaf := premise_at disj_rule 0.
Definition ax := generated_axiom leaf ltac:(vm_compute; reflexivity).
(** Node indices follow the builder's allocation order. This graph is acyclic,
    so the witness can select no trace tags. [raw_check_sound] still verifies
    both graph consistency and the semantic records stored at its nodes. *)
Definition build := Cyclic.run_script root [Cyclic.ApplyRule 0 impl_rule;Cyclic.ApplyRule 1 disj_rule;Cyclic.CloseWith 2 ax].
Theorem mixed_boolean_valid : Cyclic.Valid root.
Proof. apply (raw_check_sound build.(Cyclic.built_graph) empty_trace_witness); vm_compute; reflexivity. Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.
Print Assumptions mixed_boolean_valid.
