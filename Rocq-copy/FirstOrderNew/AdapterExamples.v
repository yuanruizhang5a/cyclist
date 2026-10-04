From Stdlib Require Import List Bool Arith String.
From CyclistRocq.FirstOrderNew Require Import Adapter.
Import ListNotations.

Module AdapterExampleDefinitions <: DEFINITION_ENV.
  Definition defs : definitions := [].
End AdapterExampleDefinitions.
Module AdapterExampleFO := Make AdapterExampleDefinitions.

Definition adapter_sparse_source := {| antecedent :=
  [[Pred 7 "P" [zero]; Eq zero zero; Deq zero (successor zero);
    Pred 7 "Q" [zero]; Eq zero zero; Eq zero zero; Eq zero zero; Pred 7 "P" [zero]]];
  succedent := [] |}.
Definition adapter_sparse_target := {| antecedent :=
  [[Eq zero zero; Eq zero zero; Pred 7 "P" [zero]; Eq zero zero];
   [Eq zero zero; Pred 7 "Q" [zero]; Eq zero zero; Eq zero zero; Eq zero zero; Pred 7 "P" [zero]]];
  succedent := [] |}.

Example shared_logical_tags_still_have_three_native_occurrences :
  logical_tags adapter_sparse_source = [7] /\ trace_tags adapter_sparse_source = [0;3;7].
Proof. reflexivity || (split; reflexivity). Qed.
Example sparse_native_positions_become_dense_predicate_ordinals :
  AdapterExampleFO.Theory.tags adapter_sparse_source = [0;1;2] /\
  map (fun position => trace_index position (trace_tags adapter_sparse_source)) [0;3;7] = [0;1;2].
Proof. split; reflexivity. Qed.
Example target_dense_ordinals_use_its_own_flattened_positions :
  trace_tags adapter_sparse_target = [2;5;9] /\
  AdapterExampleFO.Theory.tags adapter_sparse_target = [0;1;2].
Proof. split; reflexivity. Qed.
Example unregistered_positions_do_not_alias_a_valid_dense_ordinal :
  trace_index 1 (trace_tags adapter_sparse_source) = 3 /\
  registered_pairb adapter_sparse_source adapter_sparse_target (1,2) = false.
Proof. split; reflexivity. Qed.

Definition adapter_sparse_native_edge :=
  {| continuations := [(0,9); (1,2); (3,2); (7,5); (7,8); (99,2); (0,99); (7,9)];
     progressing := [(3,2); (1,2); (7,8)] |}.
Example sparse_edges_map_and_filter_both_endpoint_lists :
  AdapterExampleFO.Cyclic.edge_valid
    (AdapterExampleFO.edge adapter_sparse_source adapter_sparse_target adapter_sparse_native_edge) =
    [(0,2); (1,0); (2,1); (2,2)] /\
  AdapterExampleFO.Cyclic.edge_progress
    (AdapterExampleFO.edge adapter_sparse_source adapter_sparse_target adapter_sparse_native_edge) = [(1,0)].
Proof. vm_compute; split; reflexivity. Qed.
Example mapped_sparse_edge_passes_the_structural_endpoint_checker :
  AdapterExampleFO.Cyclic.edge_info_wfb adapter_sparse_source adapter_sparse_target
    (AdapterExampleFO.edge adapter_sparse_source adapter_sparse_target adapter_sparse_native_edge) = true.
Proof. vm_compute; reflexivity. Qed.
Example removed_nonpredicate_progress_does_not_create_a_progress_obligation :
  AdapterExampleFO.Cyclic.edge_info_wfb adapter_sparse_source adapter_sparse_target
    (AdapterExampleFO.edge adapter_sparse_source adapter_sparse_target
      {| continuations := []; progressing := [(1,2); (7,8); (99,99)] |}) = true /\
  AdapterExampleFO.Cyclic.edge_progress
    (AdapterExampleFO.edge adapter_sparse_source adapter_sparse_target
      {| continuations := []; progressing := [(1,2); (7,8); (99,99)] |}) = [].
Proof. vm_compute; split; reflexivity. Qed.
Example registered_progress_still_requires_a_valid_pair :
  AdapterExampleFO.Cyclic.edge_info_wfb adapter_sparse_source adapter_sparse_target
    (AdapterExampleFO.edge adapter_sparse_source adapter_sparse_target
      {| continuations := [(0,2)]; progressing := [(3,5)] |}) = false.
Proof. vm_compute; reflexivity. Qed.
Example edge_mapping_preserves_pair_multiplicity :
  AdapterExampleFO.Cyclic.edge_valid
    (AdapterExampleFO.edge adapter_sparse_source adapter_sparse_target
      {| continuations := [(7,5); (7,5)]; progressing := [] |}) = [(2,1); (2,1)].
Proof. vm_compute; reflexivity. Qed.
Example no_antecedent_predicates_means_no_internal_trace_tags :
  AdapterExampleFO.Theory.tags
    {| antecedent := [[Eq zero zero; Eq zero zero]]; succedent := [[Pred 7 "P" [zero]]] |} = [].
Proof. reflexivity. Qed.

Example dense_ranks_read_the_original_sparse_world_bounds (w : world) :
  AdapterExampleFO.Theory.rank adapter_sparse_source w 0 = world_bounds w 0 /\
  AdapterExampleFO.Theory.rank adapter_sparse_source w 1 = world_bounds w 3 /\
  AdapterExampleFO.Theory.rank adapter_sparse_source w 2 = world_bounds w 7.
Proof. split; [reflexivity|split; reflexivity]. Qed.
Example generic_index_lookup_preserves_native_rank (w : world) :
  AdapterExampleFO.Theory.rank adapter_sparse_source w
    (trace_index 7 (trace_tags adapter_sparse_source)) =
  rank [] adapter_sparse_source w 7.
Proof. apply AdapterExampleFO.dense_rank; cbn; auto. Qed.
Example native_semantic_rank_obligations_transfer (w w' : world) :
  respects [] adapter_sparse_source adapter_sparse_target w w' adapter_sparse_native_edge ->
  AdapterExampleFO.Cyclic.respects_edge adapter_sparse_source adapter_sparse_target w w'
    (AdapterExampleFO.edge adapter_sparse_source adapter_sparse_target adapter_sparse_native_edge).
Proof. apply AdapterExampleFO.edge_respects. Qed.
Example every_mapped_endpoint_is_registered source target e :
  (forall a b, In (a,b) (AdapterExampleFO.Cyclic.edge_valid (AdapterExampleFO.edge source target e)) ->
    In a (AdapterExampleFO.Theory.tags source) /\ In b (AdapterExampleFO.Theory.tags target)) /\
  (forall a b, In (a,b) (AdapterExampleFO.Cyclic.edge_progress (AdapterExampleFO.edge source target e)) ->
    In a (AdapterExampleFO.Theory.tags source) /\ In b (AdapterExampleFO.Theory.tags target)).
Proof. apply AdapterExampleFO.edge_registered. Qed.

(** Native local evidence can soundly mention even nonpredicate or absent
    positions in a nonprogressing identity annotation. The adapter must filter
    those positions, independently of the supplied evidence. *)
Definition adapter_annotated_identity j positions :=
  {| application_name := "annotated native identity"%string; conclusion := j;
     premises := [{| premise_label := j;
       premise_trace := {| continuations := map (fun p => (p,p)) positions; progressing := [] |} |}] |}.
Definition adapter_annotated_identity_evidence j positions :
  local_evidence [] (adapter_annotated_identity j positions).
Proof.
  constructor; intros w Hbad; exists 0; eexists; exists w; split; [reflexivity|].
  split; [exact Hbad|]; split; [|intros a b H; contradiction].
  intros a b H; apply in_map_iff in H; destruct H as [p [E _]];
    inversion E; subst; apply Nat.le_refl.
Defined.
Example packing_native_evidence_filters_unregistered_annotations :
  map (fun p => AdapterExampleFO.Cyclic.edge_valid (AdapterExampleFO.Cyclic.premise_edge p))
    (AdapterExampleFO.Cyclic.rule_premises
      (AdapterExampleFO.rule (adapter_annotated_identity adapter_sparse_source [0;1;3;6;7;99])
        (adapter_annotated_identity_evidence adapter_sparse_source [0;1;3;6;7;99]))) =
    [[(0,0); (1,1); (2,2)]].
Proof. vm_compute; reflexivity. Qed.
Example exact_backlink_uses_dense_registered_identity :
  map (fun p => AdapterExampleFO.Cyclic.edge_valid (AdapterExampleFO.Cyclic.premise_edge p))
    (AdapterExampleFO.Cyclic.rule_premises (AdapterExampleFO.exact_backlink adapter_sparse_source)) =
    [[(0,0); (1,1); (2,2)]].
Proof. reflexivity. Qed.
Example exact_backlink_ranks_are_same_world_identities (w : world) :
  AdapterExampleFO.Cyclic.respects_edge adapter_sparse_source adapter_sparse_source w w
    {| AdapterExampleFO.Cyclic.edge_valid :=
         AdapterExampleFO.Cyclic.identity_pairs (AdapterExampleFO.Theory.tags adapter_sparse_source);
       AdapterExampleFO.Cyclic.edge_progress := [] |}.
Proof.
  split; [|intros a b H; contradiction].
  intros a b H; apply in_map_iff in H; destruct H as [t [E _]];
    inversion E; subst; apply Nat.le_refl.
Qed.

Definition adapter_sparse_graph :=
  {| AdapterExampleFO.Cyclic.graph_root := adapter_sparse_source;
     AdapterExampleFO.Cyclic.graph_nodes :=
       [{| AdapterExampleFO.Cyclic.node_judgment := adapter_sparse_source;
           AdapterExampleFO.Cyclic.node_payload := AdapterExampleFO.Cyclic.OpenNode |};
        {| AdapterExampleFO.Cyclic.node_judgment := adapter_sparse_target;
           AdapterExampleFO.Cyclic.node_payload := AdapterExampleFO.Cyclic.OpenNode |}] |}.
Example graph_trace_width_depends_on_predicate_counts_instead_of_atom_positions :
  List.length (nodup Nat.eq_dec (trace_tags adapter_sparse_source ++ trace_tags adapter_sparse_target)) = 6 /\
  AdapterExampleFO.Cyclic.all_graph_tags adapter_sparse_graph = [0;1;2] /\
  AdapterExampleFO.Cyclic.relation_fuel adapter_sparse_graph = S (Nat.pow 3 (3*3)).
Proof. split; [reflexivity|split; reflexivity]. Qed.

Print Assumptions trace_index_nth.
Print Assumptions dense_pairs_spec.
Print Assumptions AdapterExampleFO.dense_rank.
Print Assumptions AdapterExampleFO.edge_respects.
Print Assumptions AdapterExampleFO.rule.
Print Assumptions AdapterExampleFO.exact_backlink.
Print Assumptions AdapterExampleFO.valid_bridge.
