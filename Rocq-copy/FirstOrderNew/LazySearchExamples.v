From Stdlib Require Import List Bool Arith String.
From CyclistRocq.FirstOrderNew Require Import LazySearch SearchExamples.
Import ListNotations.
Open Scope list_scope.
Open Scope nat_scope.
Open Scope string_scope.

(** An independent immutable graph API with actual native local certificates.
    A zero-premise application costs 1; transport applications cost 1000.
    Logs are data in the returned states, not global side effects. The traced
    lazy runner observes every actually attempted macro, including rejected
    branches, so it can detect unnecessary later graph operations. *)
Record demand_graph := {
  demand_labels : list sequent;
  demand_open : list nat;
  demand_cost : nat;
  demand_log : list nat
}.
Definition demand_label := {| antecedent := [[Pred 3 "RENAMED" [Var (Free 12)]]];
  succedent := [[Pred 9 "RENAMED" [Var (Free 12)]]] |}.
Definition demand_initial := {| demand_labels := [demand_label]; demand_open := [0];
  demand_cost := 0; demand_log := [] |}.
Definition demand_closed g := Nat.eqb (List.length g.(demand_open)) 0.
Definition demand_apply j g i (c : certified_application [] j) :=
  if existsb (Nat.eqb i) g.(demand_open) then
    let labels := map premise_label (certified_rule [] j c).(premises) in
    let ids := seq (List.length g.(demand_labels)) (List.length labels) in
    let cost := if Nat.eqb (List.length labels) 0 then 1 else 1000 in
    Some (ids,{| demand_labels := g.(demand_labels) ++ labels;
      demand_open := filter (fun n => negb (Nat.eqb n i)) g.(demand_open) ++ ids;
      demand_cost := g.(demand_cost) + cost; demand_log := g.(demand_log) ++ [cost] |})
  else None.
Definition demand_close (g : demand_graph) (i target : nat) (edge : trace_edge) :=
  if existsb (Nat.eqb i) g.(demand_open) then
    Some {| demand_labels := g.(demand_labels);
      demand_open := filter (fun n => negb (Nat.eqb n i)) g.(demand_open);
      demand_cost := S g.(demand_cost); demand_log := g.(demand_log) ++ [1] |}
  else None.
Definition demand_api
    (menus : demand_graph -> nat -> sequent -> rule_menu)
    (partial accept : demand_graph -> bool) : search_api [] demand_graph :=
  {| node_label := fun g i => nth_error g.(demand_labels) i;
     node_indices := fun g => seq 0 (List.length g.(demand_labels));
     generate_rules := menus; compile_descriptor := example_compiler [];
     apply_application := demand_apply; close_exact := demand_close;
     partial_trace_check := partial; final_accept := accept |}.
Definition demand_cheap j := primitive_program (propose RDIdentity j []).
Definition demand_transport j := primitive_program (propose_unary (RDWeaken j) j j).
Definition demand_expensive j := ProgramApply (propose_unary (RDWeaken j) j j) [demand_cheap j].
Definition demand_bad j := primitive_program (propose (RDRightSplit 1) j []).
Definition demand_choice_menu j := {| menu_axioms := []; menu_simplifications := [];
  menu_choices := [demand_cheap j;demand_expensive j] |}.
Definition demand_choices_api := demand_api (fun _ _ j => demand_choice_menu j)
  (fun _ => true) demand_closed.
Definition demand_post_cost (attempt : lazy_attempt demand_graph) :=
  match attempt.(attempt_result) with Some (_,g) => Some g.(demand_cost) | None => None end.
Definition demand_attempt_costs (api : search_api [] demand_graph) depth initial := map demand_post_cost
  (snd (lazy_bounded_dfs_traced api 100 10 depth initial 0)).

Example lazy_first_choice_matches_the_old_first_accepted_result :
  lazy_bounded_dfs demand_choices_api 100 10 1 demand_initial 0 =
    bounded_dfs demand_choices_api 100 10 1 demand_initial 0.
Proof. vm_compute; reflexivity. Qed.
Example later_graph_operation_is_never_attempted_after_first_acceptance :
  demand_attempt_costs demand_choices_api 1 demand_initial = [Some 1].
Proof. vm_compute; reflexivity. Qed.
Example eager_candidate_execution_would_apply_the_unwanted_costly_program :
  map (fun step => (snd step).(demand_cost))
    (executable_programs demand_choices_api 10 demand_initial 0
      [demand_cheap demand_label;demand_expensive demand_label]) = [1;1001].
Proof. vm_compute; reflexivity. Qed.
Example accepted_graph_contains_only_the_needed_operation_cost :
  match lazy_bounded_dfs demand_choices_api 5 10 1 demand_initial 0 with
  | Found g depth => (g.(demand_cost),g.(demand_log),depth)
  | Unknown _ => (0,[],0) end = (1,[1],1).
Proof. vm_compute; reflexivity. Qed.
Example remaining_choices_are_behind_the_new_goal_and_keep_the_original_state :
  let current := {| pending_index := 0; pending_depth := 1 |} in
  match lazy_step demand_choices_api 10 1
    [ChoicesWork demand_initial current [] [demand_cheap demand_label;demand_expensive demand_label]] with
  | LazyExecuted _ [GoalWork g [];ChoicesWork original _ [] tail] =>
      (g.(demand_cost),original.(demand_cost),List.length tail)
  | _ => (0,1,0) end = (1,0,1).
Proof. vm_compute; reflexivity. Qed.

Definition demand_reject_first_api := demand_api (fun _ _ j => demand_choice_menu j)
  (fun _ => true) (fun g => demand_closed g && Nat.eqb g.(demand_cost) 1001).
Example final_rejection_lazily_backtracks_to_the_next_program :
  demand_attempt_costs demand_reject_first_api 1 demand_initial = [Some 1;Some 1001].
Proof. vm_compute; reflexivity. Qed.
Example rejected_branch_does_not_pollute_the_next_choice_snapshot :
  match lazy_bounded_dfs demand_reject_first_api 100 10 1 demand_initial 0 with
  | Found g depth => (g.(demand_cost),g.(demand_log),depth)
  | Unknown _ => (0,[],0) end = (1001,[1000;1],1).
Proof. vm_compute; reflexivity. Qed.
Example backtracking_result_matches_eager_search_with_sufficient_fuel :
  lazy_bounded_dfs demand_reject_first_api 100 10 1 demand_initial 0 =
    bounded_dfs demand_reject_first_api 100 10 1 demand_initial 0.
Proof. vm_compute; reflexivity. Qed.
Example iterative_deepening_preserves_first_successful_depth :
  result_depth (lazy_iddfs demand_reject_first_api 100 10 0 3 demand_initial 0) = Some 1.
Proof. vm_compute; reflexivity. Qed.

Definition demand_axiom_menu j := {| menu_axioms :=
  [demand_bad j;ProgramOpen j;demand_cheap j;demand_expensive j];
  menu_simplifications := [demand_expensive j]; menu_choices := [demand_expensive j] |}.
Definition demand_axioms_api := demand_api (fun _ _ j => demand_axiom_menu j)
  (fun _ => true) demand_closed.
Example axioms_skip_refused_and_nonclosed_programs_before_committing :
  demand_attempt_costs demand_axioms_api 0 demand_initial = [None;Some 0;Some 1].
Proof. vm_compute; reflexivity. Qed.
Example depth_zero_still_runs_axioms_and_matches_old_search :
  lazy_bounded_dfs demand_axioms_api 100 10 0 demand_initial 0 =
    bounded_dfs demand_axioms_api 100 10 0 demand_initial 0.
Proof. vm_compute; reflexivity. Qed.
Example a_successful_axiom_prevents_all_later_families_and_axioms :
  map (fun attempt => attempt.(attempt_family))
    (snd (lazy_bounded_dfs_traced demand_axioms_api 100 10 2 demand_initial 0)) =
  [AxiomFamily;AxiomFamily;AxiomFamily].
Proof. vm_compute; reflexivity. Qed.
Definition demand_rejected_axiom_api := demand_api (fun _ _ j => demand_axiom_menu j)
  (fun _ => true) (fun g => demand_closed g && Nat.eqb g.(demand_cost) 1001).
Example axiom_commit_is_not_undone_by_final_acceptance_rejection :
  (result_depth (lazy_bounded_dfs demand_rejected_axiom_api 100 10 3 demand_initial 0),
   demand_attempt_costs demand_rejected_axiom_api 3 demand_initial) =
  (None,[None;Some 0;Some 1]).
Proof. vm_compute; reflexivity. Qed.

Definition demand_simplification_menu j := {| menu_axioms := [];
  menu_simplifications := [demand_bad j;demand_cheap j;demand_expensive j];
  menu_choices := [demand_expensive j] |}.
Definition demand_simplifications_api := demand_api (fun _ _ j => demand_simplification_menu j)
  (fun _ => true) demand_closed.
Example first_executable_simplification_commits_before_later_programs :
  (demand_attempt_costs demand_simplifications_api 1 demand_initial,
   map (fun attempt => attempt.(attempt_family))
     (snd (lazy_bounded_dfs_traced demand_simplifications_api 100 10 1 demand_initial 0))) =
  ([None;Some 1],[SimplificationFamily;SimplificationFamily]).
Proof. vm_compute; reflexivity. Qed.
Example simplification_priority_matches_the_old_first_accepted_result :
  lazy_bounded_dfs demand_simplifications_api 100 10 1 demand_initial 0 =
    bounded_dfs demand_simplifications_api 100 10 1 demand_initial 0.
Proof. vm_compute; reflexivity. Qed.
Definition demand_rejected_simplification_api :=
  demand_api (fun _ _ j => demand_simplification_menu j) (fun _ => true)
    (fun g => demand_closed g && Nat.eqb g.(demand_cost) 1001).
Example simplification_commit_is_not_undone_by_final_acceptance_rejection :
  (result_depth (lazy_bounded_dfs demand_rejected_simplification_api 100 10 3 demand_initial 0),
   demand_attempt_costs demand_rejected_simplification_api 3 demand_initial) = (None,[None;Some 1]).
Proof. vm_compute; reflexivity. Qed.
Definition demand_transport_menu g j := if Nat.eqb g.(demand_cost) 0 then
  {| menu_axioms := []; menu_simplifications := [demand_transport j]; menu_choices := [demand_cheap j] |}
  else {| menu_axioms := [demand_cheap j]; menu_simplifications := []; menu_choices := [] |}.
Definition demand_transport_api := demand_api (fun g _ j => demand_transport_menu g j)
  (fun _ => true) demand_closed.
Example simplification_subgoals_keep_axioms_eligible_at_the_child_depth_zero :
  match lazy_bounded_dfs demand_transport_api 100 10 1 demand_initial 0 with
  | Found g depth => (g.(demand_cost),List.length g.(demand_labels),depth)
  | Unknown _ => (0,0,0) end = (1001,2,1).
Proof. vm_compute; reflexivity. Qed.

Example depth_zero_does_not_compile_or_execute_costed_choices :
  (result_depth (lazy_bounded_dfs demand_choices_api 20 10 0 demand_initial 0),
   demand_attempt_costs demand_choices_api 0 demand_initial) = (None,[]).
Proof. vm_compute; reflexivity. Qed.
Example depth_zero_does_not_compile_or_execute_simplifications :
  demand_attempt_costs demand_simplifications_api 0 demand_initial = [].
Proof. vm_compute; reflexivity. Qed.
Example an_explicit_depth_zero_choice_job_is_dropped_without_a_program_attempt :
  lazy_step demand_choices_api 10 0
    [ChoicesWork demand_initial {| pending_index := 0; pending_depth := 0 |} []
      [demand_expensive demand_label]] = LazyContinue [].
Proof. reflexivity. Qed.
Example an_explicit_depth_zero_simplification_job_is_dropped_without_a_program_attempt :
  lazy_step demand_simplifications_api 10 0
    [SimplificationsWork demand_initial {| pending_index := 0; pending_depth := 0 |} []
      [demand_expensive demand_label] [demand_expensive demand_label]] = LazyContinue [].
Proof. reflexivity. Qed.
Example zero_work_fuel_is_unknown :
  lazy_bounded_dfs demand_choices_api 0 10 1 demand_initial 0 = Unknown FuelExhausted.
Proof. reflexivity. Qed.
Definition demand_one_axiom_api := demand_api (fun _ _ j =>
  {| menu_axioms := [demand_cheap j]; menu_simplifications := []; menu_choices := [] |})
  (fun _ => true) demand_closed.
Example administrative_work_and_final_acceptance_probes_consume_fuel :
  lazy_bounded_dfs demand_one_axiom_api 2 10 0 demand_initial 0 = Unknown FuelExhausted /\
  result_depth (lazy_bounded_dfs demand_one_axiom_api 3 10 0 demand_initial 0) = Some 0.
Proof. vm_compute; auto. Qed.
Example zero_macro_fuel_cannot_fabricate_acceptance :
  result_depth (lazy_bounded_dfs demand_one_axiom_api 20 0 0 demand_initial 0) = None.
Proof. vm_compute; reflexivity. Qed.
Example reversed_depth_interval_is_unknown :
  lazy_iddfs demand_choices_api 100 10 3 1 demand_initial 0 = Unknown DepthExhausted.
Proof. reflexivity. Qed.

Definition demand_other_root := {| demand_labels := [demand_label;demand_label]; demand_open := [1];
  demand_cost := 0; demand_log := [] |}.
Example existing_target_graph_supports_a_nonzero_requested_root :
  result_depth (lazy_iddfs demand_one_axiom_api 20 10 0 1 demand_other_root 1) = Some 0.
Proof. vm_compute; reflexivity. Qed.
Definition demand_two_pending := {| demand_labels := [demand_label;demand_label]; demand_open := [0;1];
  demand_cost := 0; demand_log := [] |}.
Definition demand_sibling_api := demand_api (fun _ _ j => demand_choice_menu j)
  (fun _ => true) (fun g => demand_closed g && Nat.eqb g.(demand_cost) 1002).
Definition demand_sibling_work := [GoalWork demand_two_pending
  [{| pending_index := 0; pending_depth := 1 |};{| pending_index := 1; pending_depth := 1 |}]].
Example sibling_backtracking_preserves_prior_closed_goals_and_pending_indices :
  let '(result,attempts) := lazy_dfs_stack_traced demand_sibling_api 100 10 1 demand_sibling_work in
  (match result with Found g _ => g.(demand_log) | Unknown _ => [] end,
   map demand_post_cost attempts) = ([1;1000;1],[Some 1;Some 2;Some 1002]).
Proof. vm_compute; reflexivity. Qed.
Example traced_and_production_results_agree :
  fst (lazy_bounded_dfs_traced demand_reject_first_api 100 10 1 demand_initial 0) =
    lazy_bounded_dfs demand_reject_first_api 100 10 1 demand_initial 0.
Proof. apply lazy_trace_preserves_result. Qed.
Definition demand_partial_rejection_api := demand_api (fun _ _ j => demand_choice_menu j)
  (fun _ => false) demand_closed.
Example existing_partial_trace_checks_are_still_enforced :
  (result_depth (lazy_bounded_dfs demand_partial_rejection_api 30 10 1 demand_initial 0),
   demand_attempt_costs demand_partial_rejection_api 1 demand_initial) = (None,[None;None]).
Proof. vm_compute; reflexivity. Qed.
Definition demand_bad_expected_api := demand_api (fun _ _ j =>
  {| menu_axioms := []; menu_simplifications := [];
     menu_choices := [primitive_program (propose RDIdentity j [j])] |}) (fun _ => true) demand_closed.
Example existing_certificate_premise_matching_is_still_enforced :
  result_depth (lazy_bounded_dfs demand_bad_expected_api 20 10 1 demand_initial 0) = None.
Proof. vm_compute; reflexivity. Qed.

(** Reuse additional independent API examples without introducing a Cyclic or
    production graph dependency into this search implementation. *)
Example original_independent_branching_example_has_the_same_lazy_result :
  lazy_iddfs example_split_api 100 10 0 2 example_split_initial 0 =
    iddfs example_split_api 100 10 0 2 example_split_initial 0.
Proof. vm_compute; reflexivity. Qed.
Example original_independent_final_rejection_example_has_the_same_lazy_result :
  lazy_iddfs example_reject_first_api 200 10 0 3 example_initial 0 =
    iddfs example_reject_first_api 200 10 0 3 example_initial 0.
Proof. vm_compute; reflexivity. Qed.
Example original_independent_backlink_example_has_the_same_lazy_result :
  lazy_bounded_dfs example_backlink_api 30 10 1 example_two_nodes 0 =
    bounded_dfs example_backlink_api 30 10 1 example_two_nodes 0.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions lazy_iddfs_accepted.
Print Assumptions lazy_trace_preserves_result.
