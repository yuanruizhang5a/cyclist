From Stdlib Require Import List Bool Arith String Lia.
From CyclistRocq.FirstOrderNew Require Import Witness.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Module WitnessDefinitions <: Adapter.DEFINITION_ENV.
  Definition defs : definitions := [].
End WitnessDefinitions.
Module W := Witness.Make WitnessDefinitions.
Module FO := W.FO.
Module C := W.C.
(** The parent uses these aliases from the SAME Witness.Make application;
    separately instantiated Framework graph records are generative in Rocq. *)
Definition witness_alias_compatible (g : W.Proof.FO.Cyclic.graph)
    : option W.Proof.FO.Cyclic.trace_witness := W.find_witness g.

(** Every label has an ordinary nil RHS product, so [FO.axiom] supplies a
    genuine validity theorem for the proof payloads. The payloads below are
    sound conditionally on that axiom: countersteps eliminate the impossible
    counterexample to a valid conclusion. They do not assume rank inequalities
    or arbitrary graph soundness. Witness synthesis itself never invokes them.
    Equality separators deliberately make native positions differ from dense
    predicate ordinals; logical predicate tags vary at every graph node. *)
Definition witness_label base width : sequent :=
  {| antecedent := [flat_map (fun tag => [Eq zero zero;Pred tag "VARIED" [zero]])
                        (seq base width)];
     succedent := [[]] |}.
Lemma witness_label_axiom base width : axiom_check (witness_label base width) = true.
Proof.
  unfold axiom_check; replace (identityb (witness_label base width)) with true by reflexivity.
  apply orb_true_r.
Qed.
Definition witness_example_rule j (H : axiom_check j = true) (ps : list C.premise) : C.rule_instance.
Proof.
  refine {| C.rule_name := "ordinary-valid trace example";
            C.rule_conclusion := j; C.rule_premises := ps |}.
  - intros _; exact (C.axiom_theorem (FO.axiom j H)).
  - intros w Hbad; exfalso; apply Hbad; exact (C.axiom_theorem (FO.axiom j H) w).
Defined.
Definition witness_node_label width index := witness_label (37+13*index) width.
Definition witness_node width index (edges : list (nat * C.edge_info)) : C.node :=
  let j := witness_node_label width index in
  let ps := map (fun je => {| C.premise_judgment := witness_node_label width (fst je);
                            C.premise_edge := snd je |}) edges in
  {| C.node_judgment := j;
     C.node_payload := C.RuleNode
       (witness_example_rule j (witness_label_axiom _ _) ps) (map fst edges) |}.
Definition witness_graph width (rows : list (list (nat * C.edge_info))) : C.graph :=
  {| C.graph_root := witness_node_label width 0;
     C.graph_nodes := map (fun ir => witness_node width (fst ir) (snd ir))
       (combine (seq 0 (List.length rows)) rows) |}.
Definition witness_edge valid progress : C.edge_info :=
  {| C.edge_valid := valid; C.edge_progress := progress |}.
Definition empty_witness_edge := witness_edge [] [].
Definition witness_signature g := match W.find_witness g with
  | None => None
  | Some tw => let indices := seq 0 (List.length g.(C.graph_nodes)) in
    Some (map tw.(C.witness_tag) indices,map tw.(C.witness_potential) indices) end.
Definition witness_found g := match W.find_witness g with Some _ => true | None => false end.
Definition witness_result_checked g := match W.find_witness g with
  | Some tw => C.witness_check g tw | None => false end.

Definition progress_forward := witness_edge [(0,1)] [(0,1)].
Definition progress_return := witness_edge [(1,0)] [].
Definition two_node_progress := witness_graph 2
  [[(1,progress_forward)];[(0,progress_return)]].
Example native_atom_positions_are_not_dense_predicate_ordinals :
  (trace_tags (witness_node_label 2 0),FO.Theory.tags (witness_node_label 2 0)) = ([1;3],[0;1]).
Proof. reflexivity. Qed.
Example genuine_two_node_progress_graph_is_structurally_checked :
  C.structural_check two_node_progress = true.
Proof. vm_compute; reflexivity. Qed.
Example genuine_two_node_progress_graph_has_a_checked_dense_witness :
  witness_signature two_node_progress = Some ([Some 0;Some 1],[0;1]) /\
  witness_result_checked two_node_progress = true.
Proof. vm_compute; auto. Qed.
Example genuine_two_node_progress_graph_satisfies_the_relational_check :
  C.relational_check two_node_progress = true.
Proof. vm_compute; reflexivity. Qed.
Example progress_witness_cache_matches_framework_liveness :
  W.cached_liveness two_node_progress = [true;true].
Proof. vm_compute; reflexivity. Qed.
Example progress_cycle_partial_check_accepts : W.partial_check two_node_progress = true.
Proof. vm_compute; reflexivity. Qed.

Definition flat_identity := witness_edge [(0,0);(1,1)] [].
Definition flat_cycle := witness_graph 2 [[(1,flat_identity)];[(0,flat_identity)]].
Example flat_cycle_is_a_genuine_structurally_checked_graph : C.structural_check flat_cycle = true.
Proof. vm_compute; reflexivity. Qed.
Example flat_cycle_is_rejected_by_witness_synthesis : W.find_witness flat_cycle = None.
Proof. vm_compute; reflexivity. Qed.
Example flat_cycle_is_rejected_by_the_relational_check : C.relational_check flat_cycle = false.
Proof. vm_compute; reflexivity. Qed.
Example flat_cycle_partial_check_rejects : W.partial_check flat_cycle = false.
Proof. vm_compute; reflexivity. Qed.

Definition rotating_progress := witness_edge [(0,1);(1,0)] [(0,1);(1,0)].
Definition rotating_cycle := witness_graph 2 [[(1,flat_identity)];[(0,rotating_progress)]].
Example rotation_graph_is_structurally_checked : C.structural_check rotating_cycle = true.
Proof. vm_compute; reflexivity. Qed.
Example rotating_trace_is_relationally_accepted_but_no_fixed_witness_is_found :
  C.relational_check rotating_cycle = true /\ W.find_witness rotating_cycle = None.
Proof. vm_compute; auto. Qed.
Example rotation_really_cannot_have_a_fixed_per_node_witness tw :
  C.witness_check rotating_cycle tw <> true.
Proof.
  intro H.
  assert (C.edge_at rotating_cycle 0 1 flat_identity) as E01.
  { eexists; split; [reflexivity|now left]. }
  assert (C.edge_at rotating_cycle 1 0 rotating_progress) as E10.
  { eexists; split; [reflexivity|now left]. }
  pose proof (W.Proof.witness_transitions rotating_cycle tw H 0 1 flat_identity E01 eq_refl) as H01.
  pose proof (W.Proof.witness_transitions rotating_cycle tw H 1 0 rotating_progress E10 eq_refl) as H10.
  unfold C.trace_transition in H01,H10.
  destruct (C.witness_tag tw 0) as [a|],(C.witness_tag tw 1) as [b|]; try contradiction.
  - destruct H01 as [Hvalid01 _],H10 as [Hvalid10 _].
    cbn in Hvalid01,Hvalid10; intuition congruence.
  - lia.
Qed.

Definition witness_dag := witness_graph 3
  [[(1,empty_witness_edge);(2,empty_witness_edge)];[(2,empty_witness_edge)];[]].
Example dag_labels_have_tags_but_no_node_is_live :
  W.cached_liveness witness_dag = [false;false;false].
Proof. vm_compute; reflexivity. Qed.
Example dag_forces_every_assignment_to_none :
  witness_signature witness_dag = Some ([None;None;None],[0;0;0]) /\
  witness_result_checked witness_dag = true.
Proof. vm_compute; auto. Qed.
Example dag_is_structurally_checked : C.structural_check witness_dag = true.
Proof. vm_compute; reflexivity. Qed.
Example cached_checker_agrees_with_framework_checker_on_a_dag :
  match W.find_witness witness_dag with
  | Some tw => W.memo_witness_check (W.prepare_graph witness_dag) tw = C.witness_check witness_dag tw
  | None => False end.
Proof. apply W.memo_witness_check_correct; apply W.prepare_graph_correct. Qed.

Definition reset_forward := witness_edge [(0,1)] [].
Definition reset_return := witness_edge [(1,0)] [(1,0)].
Definition branch_progress_reset := witness_graph 2
  [[(1,empty_witness_edge);(2,empty_witness_edge)];
   [(3,reset_forward)];[(3,empty_witness_edge)];[(1,reset_return)]].
Example branching_progress_reset_graph_is_structurally_checked :
  C.structural_check branch_progress_reset = true.
Proof. vm_compute; reflexivity. Qed.
Example branching_progress_and_none_to_some_resets_are_synthesized :
  witness_signature branch_progress_reset = Some ([None;Some 0;None;Some 1],[1;1;0;0]) /\
  witness_result_checked branch_progress_reset = true.
Proof. vm_compute; auto. Qed.
Example a_progress_edge_can_reset_the_auxiliary_potential_upward :
  match W.find_witness branch_progress_reset with
  | Some tw => tw.(C.witness_potential) 3 < tw.(C.witness_potential) 1
  | None => False end.
Proof. vm_compute; lia. Qed.
Example every_branch_into_a_live_region_is_checked :
  let forbidden := witness_graph 1
    [[(1,witness_edge [(0,0)] [(0,0)]);(2,empty_witness_edge)];
     [(0,witness_edge [(0,0)] [(0,0)])];[(0,empty_witness_edge)]] in
  W.find_witness forbidden = None.
Proof. vm_compute; reflexivity. Qed.

Example unassigned_and_assigned_none_endpoints_are_distinct :
  let edge := {| W.edge_source := 0; W.edge_target := 1;
                 W.edge_trace := empty_witness_edge |} in
  (W.known_endpoints_ok [Some 0] edge,W.known_endpoints_ok [Some 0;None] edge) = (true,false).
Proof. reflexivity. Qed.
Example incremental_pruning_checks_nonprogress_pair_membership :
  let edge := {| W.edge_source := 0; W.edge_target := 1;
                 W.edge_trace := witness_edge [(0,1)] [] |} in
  (W.known_endpoints_ok [Some 0;Some 0] edge,
   W.known_endpoints_ok [Some 0;Some 1] edge) = (false,true).
Proof. reflexivity. Qed.
Example partial_strict_cycle_is_pruned_before_unassigned_nodes :
  let g := witness_graph 2 [[(0,flat_identity);(1,empty_witness_edge)];[]] in
  W.prefix_ok (W.prepare_graph g) [Some 0] = false.
Proof. vm_compute; reflexivity. Qed.
Example nonprogress_and_unselected_edges_create_strict_constraints :
  let edges := [ {| W.edge_source := 0; W.edge_target := 1; W.edge_trace := reset_forward |};
                 {| W.edge_source := 1; W.edge_target := 2; W.edge_trace := reset_return |};
                 {| W.edge_source := 3; W.edge_target := 4; W.edge_trace := empty_witness_edge |} ] in
  W.strict_pairs [Some 0;Some 1;Some 0;None;None] edges = [(0,1);(3,4)].
Proof. reflexivity. Qed.
Example longest_path_potentials_descend_towards_targets :
  W.potentials_for 4 [(0,1);(1,2);(0,3)] = [2;1;0;0].
Proof. reflexivity. Qed.
Example longest_path_relaxation_does_not_accept_a_strict_cycle :
  W.strict_potentials_ok [(0,1);(1,0)] (W.potentials_for 2 [(0,1);(1,0)]) = false.
Proof. reflexivity. Qed.
Example dangling_targets_are_nonlive_in_the_memoized_topology :
  let g := witness_graph 1 [[(99,empty_witness_edge)]] in
  (W.cached_liveness g,W.path_flags g 0,W.path_flags g 1) = ([false],[true],[false]).
Proof. vm_compute; reflexivity. Qed.
Example an_open_partial_graph_can_have_a_witness_without_being_closed :
  let g := C.start_graph (witness_node_label 3 0) in
  (W.partial_check g,C.structural_check g) = (true,false).
Proof. vm_compute; reflexivity. Qed.
Example empty_stored_graph_has_an_empty_assignment :
  witness_signature (witness_graph 0 []) = Some ([],[]).
Proof. reflexivity. Qed.

(** Performance probes: these graphs would have (width+1)^nodes complete
    assignments in an eager product. Prefix pruning visits only width+1 root
    choices in the impossible case, and width choices per node in the forced
    successful case. Work counts are produced by the actual synthesis DFS. *)
Definition all_flat width := witness_edge (C.identity_pairs (seq 0 width)) [].
Definition all_progress width := witness_edge (C.identity_pairs (seq 0 width))
  (C.identity_pairs (seq 0 width)).
Definition impossible_wide_graph width nodes := witness_graph width
  (map (fun i => if Nat.eqb i 0 then
      (0,all_flat width) :: map (fun j => (j,empty_witness_edge)) (seq 1 (nodes-1))
    else [(i,all_progress width)]) (seq 0 nodes)).
Definition forced_wide_graph width nodes :=
  let last := Nat.pred width in
  let progressing := witness_edge [(last,last)] [(last,last)] in
  let flat := witness_edge [(last,last)] [] in
  witness_graph width (map (fun i =>
    if Nat.eqb i 0 then [(0,progressing);(1,flat)]
    else if Nat.eqb (S i) nodes then [(0,progressing)] else [(S i,flat)]) (seq 0 nodes)).
Example impossible_wide_graph_is_structurally_checked :
  C.structural_check (impossible_wide_graph 16 20) = true.
Proof. vm_compute; reflexivity. Qed.
Example root_cycle_pruning_avoids_seventeen_to_the_twentieth_assignments :
  let '(result,choices) := W.find_witness_stats (impossible_wide_graph 16 20) in
  (match result with Some _ => true | None => false end,choices) = (false,17).
Proof. vm_compute; reflexivity. Qed.
Example forced_wide_graph_is_structurally_checked :
  C.structural_check (forced_wide_graph 16 16) = true.
Proof. vm_compute; reflexivity. Qed.
Example endpoint_pruning_avoids_eager_products_on_a_successful_wide_graph :
  let '(result,choices) := W.find_witness_stats (forced_wide_graph 16 16) in
  (match result with Some tw => map tw.(C.witness_tag) (seq 0 16) | None => [] end,choices)
    = (repeat (Some 15) 16,256).
Proof. vm_compute; reflexivity. Qed.
Example successful_wide_witness_matches_the_original_checker :
  witness_result_checked (forced_wide_graph 16 16) = true.
Proof. vm_compute; reflexivity. Qed.
Time Eval vm_compute in
  let '(result,choices) := W.find_witness_stats (impossible_wide_graph 16 20) in
  (match result with Some _ => true | None => false end,choices).
Time Eval vm_compute in
  let '(result,choices) := W.find_witness_stats (forced_wide_graph 16 16) in
  (match result with Some _ => true | None => false end,choices).

Print Assumptions W.find_witness_sound.
Print Assumptions W.cached_liveness_at.
Print Assumptions W.partial_check_sound.
