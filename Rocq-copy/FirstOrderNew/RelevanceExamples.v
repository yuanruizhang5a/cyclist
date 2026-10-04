From Stdlib Require Import List Bool Arith String.
From CyclistRocq.FirstOrderNew Require Import Relevance.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Definition rel_x := Var (Free 7).
Definition rel_y := Var (Free 11).
Definition rel_z := Var (Free 19).
Definition rel_v := Var (Free 23).
Definition rel_a := Var (Free 0).
Definition rel_b := Var (Free 1).
Definition rel_c := Var (Free 2).
Definition rel_step t := Fun "rise" [t].
Definition rel_clause name args atoms := {| clause_name := name; head := args; body := atoms |}.
Definition rel_unary name :=
  [rel_clause name [zero] [];rel_clause name [rel_step rel_a] [Pred 0 name [rel_a]]].
Definition rel_limits := {| matching_fuel := 8; simplification_steps := 8;
  candidate_limit := 64; combination_limit := 64 |}.
Definition rel_label p rhs := {| antecedent := [p]; succedent := rhs |}.
Definition rel_proposals d j := compiled_left_unfold_proposals rel_limits d j.
Definition rel_ordered_descriptors d j := map proposal_descriptor
  (order_left_proposals d j (rel_proposals d j)).

Example pattern_variables_accept_every_actual_term_without_blockers :
  head_blockers_at 0 (Var (Exist 3)) (Fun "arbitrary" [rel_x;zero]) = Some [].
Proof. reflexivity. Qed.
Example rigid_patterns_record_only_free_blockers :
  (head_blockers_at 0 zero rel_y,head_blockers_at 0 (rel_step rel_a) rel_z,
   head_blockers_at 0 zero (Var (Exist 11))) =
  (Some [(Free 11,0)],Some [(Free 19,0)],Some []).
Proof. reflexivity. Qed.
Example identical_known_constants_have_no_blockers : head_blockers_at 0 zero zero = Some [].
Proof. reflexivity. Qed.
Example recursive_matching_records_the_actual_rigid_depth :
  head_blockers_at 0 (Fun "wrapper" [Fun "wrapper" [zero]])
    (Fun "wrapper" [Fun "wrapper" [rel_v]]) = Some [(Free 23,2)].
Proof. reflexivity. Qed.
Example a_known_function_mismatch_rejects_the_entire_head_comparison :
  head_list_blockers [zero;Fun "first" [rel_a]] [rel_x;Fun "second" [rel_y]] = None.
Proof. reflexivity. Qed.
Example a_known_arity_mismatch_rejects_the_entire_head_comparison :
  head_list_blockers [zero;Fun "first" [rel_a;rel_b]] [rel_x;Fun "first" [rel_y]] = None.
Proof. reflexivity. Qed.
Example a_known_constant_function_mismatch_discards_earlier_blockers :
  atom_rhs_blockers [rel_clause "RENAMED" [zero;zero] []]
    (Pred 0 "RENAMED" [rel_x;rel_step rel_y]) = [].
Proof. reflexivity. Qed.
Example predicate_name_and_arity_are_data_checked :
  atom_rhs_blockers [rel_clause "ONE" [zero] [];rel_clause "TWO" [zero;zero] []]
    (Pred 0 "TWO" [rel_y]) = [].
Proof. reflexivity. Qed.
Example clause_bodies_do_not_affect_head_blockers :
  atom_rhs_blockers [rel_clause "BODYVARIANT" [zero] [Pred 90 "UNKNOWN" [rel_v]]]
    (Pred 0 "BODYVARIANT" [rel_x]) = [(Free 7,0)].
Proof. reflexivity. Qed.
Example all_rhs_products_and_clauses_contribute_occurrences :
  rhs_blockers [rel_clause "ECHO" [zero] [];rel_clause "ECHO" [rel_step rel_a] []]
    (rel_label [] [[Pred 0 "ECHO" [rel_x]];[Pred 5 "ECHO" [rel_y]]]) =
    [(Free 7,0);(Free 7,0);(Free 11,0);(Free 11,0)].
Proof. reflexivity. Qed.
Example existential_arguments_never_drive_left_induction :
  rhs_blockers (rel_unary "TOKEN")
    (rel_label [Pred 1 "TOKEN" [rel_x]] [[Pred 0 "TOKEN" [Var (Exist 7)]]]) = [].
Proof. reflexivity. Qed.

(** A ternary dependency is the only antecedent principal mentioning the RHS
    blocked output variable. Its symbol is never examined by the scheduler. *)
Definition rel_join_defs := rel_unary "TOKEN" ++
  [rel_clause "ASSEMBLE" [zero;rel_b;rel_b] [Pred 0 "TOKEN" [rel_b]];
   rel_clause "ASSEMBLE" [rel_step rel_a;rel_b;rel_step rel_c]
     [Pred 0 "ASSEMBLE" [rel_a;rel_b;rel_c]]].
Definition rel_join_goal := rel_label
  [Pred 2 "TOKEN" [rel_x];Pred 3 "TOKEN" [rel_y];Pred 4 "ASSEMBLE" [rel_x;rel_y;rel_z]]
  [[Pred 9 "TOKEN" [rel_z]]].
Example renamed_ternary_output_dependency_is_prioritized_over_input_guards :
  rel_ordered_descriptors rel_join_defs rel_join_goal =
    [RDLeftUnfoldAt 0 2 5;RDLeftUnfoldAt 0 0 5;RDLeftUnfoldAt 0 1 5].
Proof. vm_compute; reflexivity. Qed.
Example relevance_ordered_native_proposals_still_all_recompile :
  forallb (proposal_compilableb rel_join_defs)
    (order_left_proposals rel_join_defs rel_join_goal (rel_proposals rel_join_defs rel_join_goal)) = true.
Proof. vm_compute; reflexivity. Qed.
Definition rel_switch_defs := rel_unary "TOKEN" ++
  [rel_clause "WRAPPER" [rel_a;rel_b] [Pred 0 "SWITCH" [rel_a;rel_b]];
   rel_clause "SWITCH" [rel_a;zero] [];
   rel_clause "SWITCH" [rel_a;rel_step rel_b] [Pred 0 "SWITCH" [rel_a;rel_b]]].
Definition rel_switch_goal := rel_label
  [Pred 2 "WRAPPER" [rel_x;rel_y];Pred 3 "TOKEN" [rel_x];Pred 4 "TOKEN" [rel_y]]
  [[Pred 9 "SWITCH" [rel_x;rel_y]]].
Example renamed_second_argument_recursion_prefers_the_small_second_guard :
  rel_ordered_descriptors rel_switch_defs rel_switch_goal =
    [RDLeftUnfoldAt 0 2 5;RDLeftUnfoldAt 0 0 5;RDLeftUnfoldAt 0 1 5].
Proof. vm_compute; reflexivity. Qed.
Definition rel_switch_first_defs := rel_unary "TOKEN" ++
  [rel_clause "WRAPPER" [rel_a;rel_b] [Pred 0 "SWITCH" [rel_a;rel_b]];
   rel_clause "SWITCH" [zero;rel_b] [];
   rel_clause "SWITCH" [rel_step rel_a;rel_b] [Pred 0 "SWITCH" [rel_a;rel_b]]].
Example changing_only_definition_heads_changes_the_induction_order :
  rel_ordered_descriptors rel_switch_first_defs rel_switch_goal =
    [RDLeftUnfoldAt 0 1 5;RDLeftUnfoldAt 0 0 5;RDLeftUnfoldAt 0 2 5].
Proof. vm_compute; reflexivity. Qed.

(** Known rigid mismatches on the second argument discard inapplicable heads;
    the compatible heads see the first argument at depth zero and the already
    shaped nested second argument has no blocker. *)
Definition rel_hydra_defs := rel_unary "TOKEN" ++
  [rel_clause "WRAPPER" [rel_a;rel_b] [Pred 0 "MUTANT" [rel_a;rel_b]];
   rel_clause "MUTANT" [zero;zero] [];
   rel_clause "MUTANT" [rel_step zero;zero] [];
   rel_clause "MUTANT" [rel_a;rel_step zero] [];
   rel_clause "MUTANT" [rel_step rel_a;rel_step (rel_step rel_b)]
     [Pred 0 "MUTANT" [rel_a;rel_b]];
   rel_clause "MUTANT" [zero;rel_step (rel_step rel_b)]
     [Pred 0 "MUTANT" [rel_step rel_b;rel_b]];
   rel_clause "MUTANT" [rel_step (rel_step rel_a);zero]
     [Pred 0 "MUTANT" [rel_step rel_a;rel_a]]].
Definition rel_hydra_goal := rel_label
  [Pred 2 "WRAPPER" [rel_y;rel_step (rel_step rel_v)];
   Pred 3 "TOKEN" [rel_v];Pred 4 "TOKEN" [rel_y]]
  [[Pred 9 "MUTANT" [rel_y;rel_step (rel_step rel_v)]]].
Example renamed_nested_family_records_only_compatible_first_argument_blockers :
  rhs_blockers rel_hydra_defs rel_hydra_goal = [(Free 11,0);(Free 11,0)].
Proof. vm_compute; reflexivity. Qed.
Example nested_family_does_not_induct_on_the_already_shaped_second_argument :
  rel_ordered_descriptors rel_hydra_defs rel_hydra_goal =
    [RDLeftUnfoldAt 0 2 5;RDLeftUnfoldAt 0 0 5;RDLeftUnfoldAt 0 1 5].
Proof. vm_compute; reflexivity. Qed.

Definition rel_two_guards := [Pred 2 "TOKEN" [rel_x];Pred 3 "TOKEN" [rel_y]].
Definition rel_depth_defs := rel_unary "TOKEN" ++
  [rel_clause "DEPTH" [rel_step zero;zero] []].
Definition rel_depth_goal := rel_label rel_two_guards [[Pred 9 "DEPTH" [rel_step rel_x;rel_y]]].
Example top_level_rigid_blocker_has_priority_over_a_deeper_blocker :
  (rhs_blockers rel_depth_defs rel_depth_goal,
   rel_ordered_descriptors rel_depth_defs rel_depth_goal) =
    ([(Free 7,1);(Free 11,0)],[RDLeftUnfoldAt 0 1 4;RDLeftUnfoldAt 0 0 4]).
Proof. vm_compute; reflexivity. Qed.
Definition rel_count_defs := rel_unary "TOKEN" ++ [rel_clause "COUNTED" [zero;zero;zero] []].
Definition rel_count_goal := rel_label rel_two_guards [[Pred 9 "COUNTED" [rel_x;rel_y;rel_y]]].
Example more_blocked_rhs_occurrences_break_equal_depth_ties :
  rel_ordered_descriptors rel_count_defs rel_count_goal =
    [RDLeftUnfoldAt 0 1 4;RDLeftUnfoldAt 0 0 4].
Proof. vm_compute; reflexivity. Qed.
Definition rel_copy_goal := rel_label
  [Pred 2 "TOKEN" [rel_step rel_x];Pred 3 "TOKEN" [rel_x];Pred 4 "TOKEN" [rel_y]]
  [[Pred 9 "TOKEN" [rel_x]]].
Example bare_variable_guard_is_preferred_to_a_larger_contract_copy :
  rel_ordered_descriptors (rel_unary "TOKEN") rel_copy_goal =
    [RDLeftUnfoldAt 0 1 5;RDLeftUnfoldAt 0 0 5;RDLeftUnfoldAt 0 2 5].
Proof. vm_compute; reflexivity. Qed.
Example repeated_lhs_variables_do_not_manufacture_rhs_blocker_occurrences :
  let j := rel_label [Pred 2 "WRAPPER" [rel_x;rel_x]] [[Pred 9 "TOKEN" [rel_x]]] in
  let p := propose (RDLeftUnfoldAt 0 0 3) j [] in
  (score_left_proposal (rhs_blockers (rel_unary "TOKEN") j) j p).(blocker_occurrences) = 2.
Proof. vm_compute; reflexivity. Qed.

Definition rel_tie_goal := rel_label [Pred 2 "TOKEN" [rel_x];Pred 3 "TOKEN" [rel_x]]
  [[Pred 9 "TOKEN" [rel_x]]].
Example equal_scores_keep_source_order_even_when_source_order_is_reversed :
  let ps := rev (rel_proposals (rel_unary "TOKEN") rel_tie_goal) in
  order_left_proposals (rel_unary "TOKEN") rel_tie_goal ps = ps.
Proof. vm_compute; reflexivity. Qed.
Example duplicate_proposals_are_retained_with_the_same_multiplicity_and_order :
  let ps := rel_proposals (rel_unary "TOKEN") rel_tie_goal in
  match ps with [p;q] => order_left_proposals (rel_unary "TOKEN") rel_tie_goal [q;p;q] = [q;p;q]
  | _ => False end.
Proof. vm_compute; reflexivity. Qed.
Example no_rhs_blockers_keep_even_different_sized_principals_in_source_order :
  let j := rel_label [Pred 2 "TOKEN" [rel_step rel_x];Pred 3 "TOKEN" [rel_x]]
    [[Pred 9 "TOKEN" [zero]]] in
  let ps := rel_proposals (rel_unary "TOKEN") j in
  order_left_proposals (rel_unary "TOKEN") j ps = ps.
Proof. vm_compute; reflexivity. Qed.
Example unsupported_rhs_symbol_does_not_invent_blockers :
  let j := rel_label rel_two_guards [[Pred 0 "UNDEFINED" [rel_x;rel_y]]] in
  order_left_proposals (rel_unary "TOKEN") j (rel_proposals (rel_unary "TOKEN") j) =
    rel_proposals (rel_unary "TOKEN") j.
Proof. vm_compute; reflexivity. Qed.
Example blockers_not_mentioned_by_any_principal_keep_source_order :
  let j := rel_label [Pred 2 "TOKEN" [rel_step rel_x];Pred 3 "TOKEN" [rel_y]]
    [[Pred 9 "TOKEN" [rel_z]]] in
  let ps := rel_proposals (rel_unary "TOKEN") j in
  order_left_proposals (rel_unary "TOKEN") j ps = ps.
Proof. vm_compute; reflexivity. Qed.

(** The optional detector is evaluated on genuine compiler-generated wrappers.
    The recursive head is impossible at the known base value, leaving only a
    renamed contraction copy as the unique open frontier. *)
Definition rel_base_defs :=
  [rel_clause "GROUNDCHAIN" [zero] [];
   rel_clause "GROUNDCHAIN" [successor rel_a] [Pred 0 "GROUNDCHAIN" [rel_a]]].
Definition rel_base_goal := rel_label [Pred 7 "GROUNDCHAIN" [zero]] [].
Definition rel_base_programs := map (compiled_wrapped_program rel_limits rel_base_defs)
  (rel_proposals rel_base_defs rel_base_goal).
Example renamed_known_base_copy_only_unfold_is_detected :
  map (uninformative_left_program rel_base_goal) rel_base_programs = [true].
Proof. vm_compute; reflexivity. Qed.
Example detected_copy_only_program_still_contains_checked_native_applications :
  forallb (program_compilableb rel_base_defs) rel_base_programs = true.
Proof. vm_compute; reflexivity. Qed.
Example known_base_frontier_is_identical_only_after_logical_tag_erasure :
  match rel_base_programs with [p] => match program_frontier p with [k] =>
    (sequent_eqb rel_base_goal k,
     sequent_eqb (erase_sequent_logical_tags rel_base_goal) (erase_sequent_logical_tags k),
     existsb (Nat.eqb 7) (logical_tags k))
  | _ => (true,false,true) end | _ => (true,false,true) end = (false,true,false).
Proof. vm_compute; reflexivity. Qed.
Example a_recursive_body_open_frontier_is_not_flagged_as_copy_only :
  let j := rel_label [Pred 7 "GROUNDCHAIN" [successor rel_x]] [] in
  forallb (fun p => negb (uninformative_left_program j p))
    (map (compiled_wrapped_program rel_limits rel_base_defs) (rel_proposals rel_base_defs j)) = true.
Proof. vm_compute; reflexivity. Qed.
Example a_fully_closed_left_program_is_not_discarded :
  let j := rel_label [Pred 7 "GROUNDCHAIN" [zero]] [[]] in
  map (uninformative_left_program j)
    (map (compiled_wrapped_program rel_limits rel_base_defs) (rel_proposals rel_base_defs j)) = [false].
Proof. vm_compute; reflexivity. Qed.
Example retaining_the_old_logical_group_prevents_copy_only_detection :
  let j := rel_base_goal in
  uninformative_left_program j (ProgramApply (propose_unary (RDLeftUnfoldAt 0 0 8) j j)
    [ProgramOpen j]) = false.
Proof. vm_compute; reflexivity. Qed.
Example multiple_open_frontiers_are_not_flagged :
  let j := rel_base_goal in
  let k := rel_label [Pred 8 "GROUNDCHAIN" [zero]] [] in
  uninformative_left_program j (ProgramApply (propose (RDLeftUnfoldAt 0 0 8) j [k;k])
    [ProgramOpen k;ProgramOpen k]) = false.
Proof. vm_compute; reflexivity. Qed.
Example unrelated_descriptor_and_root_conclusion_are_not_flagged :
  let j := rel_base_goal in
  let k := rel_label [Pred 8 "GROUNDCHAIN" [zero]] [] in
  (uninformative_left_program j (ProgramApply (propose_unary (RDWeaken k) j k) [ProgramOpen k]),
   uninformative_left_program j (ProgramApply (propose_unary (RDLeftUnfoldAt 0 0 9) k k) [ProgramOpen k]))
    = (false,false).
Proof. vm_compute; reflexivity. Qed.
Example optional_filter_is_separate_from_the_orderer :
  filter_informative_left_programs rel_base_goal rel_base_programs = [] /\
  List.length (order_left_proposals rel_base_defs rel_base_goal
    (rel_proposals rel_base_defs rel_base_goal)) = 1.
Proof. vm_compute; auto. Qed.

Print Assumptions order_left_proposals_permutation.
Print Assumptions filtered_left_programs_included.
