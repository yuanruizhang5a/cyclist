From Stdlib Require Import List String.

From CyclistRocq.SP Require Import
  Syntax Semantics Rules Certification GraphSearch.

Import ListNotations.
Open Scope string_scope.

(** * Small accepted and rejected proof graphs *)

Definition teaching_emp : formula := singleton_formula emp.
Definition teaching_identity : judgment :=
  mk_judgment [] (mk_sequent teaching_emp teaching_emp).

Definition teaching_identity_axiom : Cyclic.axiom_instance :=
  identity_axiom [] teaching_emp.

Definition teaching_acyclic_certificate : Cyclic.certificate :=
  certify_axiom teaching_identity_axiom.

Theorem teaching_acyclic_valid : Cyclic.Valid teaching_identity.
Proof.
  exact (Cyclic.certificate_sound teaching_acyclic_certificate
    (certify_axiom_check teaching_identity_axiom)).
Qed.

(** A two-node cyclic teaching graph.  Its judgment is independently valid,
    while both graph edges carry an explicit strict trace step.  The example
    isolates the framework's global progress and witness checks from the much
    larger inductive-unfolding generator. *)
Definition teaching_tagged_formula : formula :=
  singleton_formula
    (mk_heap [] [] [tagged_pred 0 "TeachingPredicate" [Var (free_var 0)]]).

Definition teaching_cyclic_judgment : judgment :=
  mk_judgment []
    (mk_sequent teaching_tagged_formula teaching_tagged_formula).

Definition teaching_progress_rule : Cyclic.rule_instance :=
  progressing_valid_rule teaching_cyclic_judgment 0
    (identity_valid [] teaching_tagged_formula).

Definition teaching_cyclic_state : Cyclic.build_state :=
  Cyclic.run_script teaching_cyclic_judgment
    [Cyclic.ApplyRule 0 teaching_progress_rule;
     Cyclic.AddBacklink 1 0 teaching_progress_rule].

Definition teaching_cyclic_graph : Cyclic.graph :=
  teaching_cyclic_state.(Cyclic.built_graph).

Definition teaching_cyclic_witness : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := fun _ => Some 0;
     Cyclic.witness_potential := fun _ => 0 |}.

Example teaching_cyclic_script_succeeds :
  teaching_cyclic_state.(Cyclic.build_ok) = true.
Proof. vm_compute. reflexivity. Qed.

Example teaching_cyclic_raw_check :
  Cyclic.raw_check teaching_cyclic_graph teaching_cyclic_witness = true.
Proof. vm_compute. reflexivity. Qed.

Definition teaching_cyclic_certificate : Cyclic.certificate :=
  certify_raw_check teaching_cyclic_graph teaching_cyclic_witness
    teaching_cyclic_raw_check.

Theorem teaching_cyclic_valid : Cyclic.Valid teaching_cyclic_judgment.
Proof.
  apply (Cyclic.certificate_sound teaching_cyclic_certificate).
  exact teaching_cyclic_raw_check.
Qed.

(** Rejection examples exercise independent checker boundaries. *)
Example rejected_open_graph :
  Cyclic.raw_check (Cyclic.start_graph teaching_identity)
    empty_trace_witness = false.
Proof. vm_compute. reflexivity. Qed.

Definition malformed_self_backlink : Cyclic.graph :=
  {| Cyclic.graph_root := teaching_identity;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := teaching_identity;
           Cyclic.node_payload :=
             Cyclic.BacklinkNode (exact_backlink_rule teaching_identity) 0 |}] |}.

Example rejected_malformed_backlink :
  Cyclic.raw_check malformed_self_backlink empty_trace_witness = false.
Proof. vm_compute. reflexivity. Qed.

Definition nonprogress_state : Cyclic.build_state :=
  Cyclic.run_script teaching_cyclic_judgment
    [Cyclic.ApplyRule 0 (exact_backlink_rule teaching_cyclic_judgment);
     Cyclic.AddBacklink 1 0 (exact_backlink_rule teaching_cyclic_judgment)].

Definition nonprogress_graph : Cyclic.graph :=
  nonprogress_state.(Cyclic.built_graph).

Example rejected_nonprogressing_cycle :
  Cyclic.raw_check nonprogress_graph teaching_cyclic_witness = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions teaching_acyclic_valid.
Print Assumptions teaching_cyclic_valid.
