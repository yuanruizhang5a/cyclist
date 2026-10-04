From Stdlib Require Import List Bool Arith String.
From CyclistRocq.FirstOrderNew Require Import Compiler SearchExamples.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Definition compiler_x := Var (Free 0).
Definition compiler_y := Var (Free 1).
Definition compiler_goal_var := Var (Free 7).
Definition compiler_e := Var (Exist 0).
Definition compiler_clause name args atoms :=
  {| clause_name := name; head := args; body := atoms |}.
Definition compiler_base := compiler_clause "MEASURE" [zero] [].
Definition compiler_step := compiler_clause "MEASURE" [successor compiler_x]
  [Pred 0 "MEASURE" [compiler_x]].
Definition compiler_repeat := compiler_clause "RELATE" [compiler_x;compiler_x]
  [Pred 0 "MEASURE" [compiler_x]].
Definition compiler_local := compiler_clause "HIDDEN" [compiler_x]
  [Pred 0 "MEASURE" [compiler_y]].
Definition compiler_prime := compiler_clause "PRIMED" [compiler_x]
  [Pred 0 "MEASURE" [compiler_e]].
Definition compiler_pack := compiler_clause "PACKED" [successor compiler_x]
  [Pred 0 "MEASURE" [compiler_x]].
Definition compiler_definitions := [compiler_base;compiler_step;compiler_repeat;
  compiler_local;compiler_prime;compiler_pack].
Definition compiler_limits := {| matching_fuel := 12; simplification_steps := 12;
  candidate_limit := 64; combination_limit := 64 |}.
Definition compiler_label p g := {| antecedent := [p]; succedent := g |}.
Definition compilation_matches d j rd labels :=
  match compile_rule_descriptor d j rd with
  | Some c => application_matches (propose rd j labels) (certified_rule d j c)
  | None => false end.
Definition compilation_present d j rd :=
  match compiled_proposal d j rd with Some p => proposal_compilableb d p | None => false end.
Definition compilation_labels d j rd :=
  option_map proposal_premises (compiled_proposal d j rd).
Definition all_compiler_programs menu :=
  menu.(menu_axioms) ++ menu.(menu_simplifications) ++ menu.(menu_choices).

Example native_ex_falso_is_an_exact_zero_premise_certificate :
  compilation_matches [] (compiler_label [Deq compiler_x compiler_x] []) RDExFalso [] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_identity_is_an_exact_zero_premise_certificate :
  compilation_matches [] (compiler_label [Pred 3 "RENAMED" [compiler_x]]
    [[Pred 8 "RENAMED" [compiler_x]]]) RDIdentity [] = true.
Proof. vm_compute; reflexivity. Qed.
Example identity_descriptor_does_not_guess_an_axiom :
  compilation_present [] (compiler_label [Pred 3 "A" [compiler_x]]
    [[Pred 8 "B" [compiler_x]]]) RDIdentity = false.
Proof. vm_compute; reflexivity. Qed.
Example ex_falso_descriptor_checks_every_antecedent_disjunct :
  compilation_present [] {| antecedent := [[Deq compiler_x compiler_x];[]]; succedent := [] |}
    RDExFalso = false.
Proof. vm_compute; reflexivity. Qed.
Example corrected_disjunctive_identity_is_not_guessed :
  compilation_present [] {| antecedent := [[Pred 3 "A" []];[Pred 4 "B" []]];
    succedent := [[Pred 0 "A" []]] |} RDIdentity = false.
Proof. vm_compute; reflexivity. Qed.

Example native_trivial_equalities_preserve_duplicate_occurrences :
  let p := Pred 3 "A" [compiler_x] in
  compilation_matches [] (compiler_label [Eq zero zero;p;p] [[Eq compiler_x compiler_x]])
    RDTrivialEqualities [compiler_label [p;p] [[]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_left_substitution_matches_its_actual_premise :
  compilation_matches [] (compiler_label [Eq compiler_x zero;Pred 3 "A" [compiler_x]]
    [[Pred 0 "B" [compiler_x]]]) (RDLeftEquality (Free 0) zero)
    [compiler_label [Eq zero zero;Pred 3 "A" [zero]] [[Pred 0 "B" [zero]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_left_substitution_rejects_wrong_descriptor_binding :
  compilation_present [] (compiler_label [Eq compiler_x zero] [])
    (RDLeftEquality (Free 1) zero) = false.
Proof. vm_compute; reflexivity. Qed.
Definition compiler_rhs_equality_goal := compiler_label []
  [[Pred 0 "KEEP" [compiler_e]];
   [Eq (Var (Exist 5)) zero;Pred 0 "CHANGE" [Var (Exist 5)]];
   [Eq (Var (Exist 5)) zero;Pred 0 "CHANGE" [Var (Exist 5)]]].
Example native_right_equality_uses_replace_product_and_removes_all_selected_copies :
  compilation_matches [] compiler_rhs_equality_goal (RDRightEquality 1 (Exist 5) zero)
    [compiler_label [] [[Eq zero zero;Pred 0 "CHANGE" [zero]];
                       [Pred 0 "KEEP" [compiler_e]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example old_index_replacement_is_not_pretended_to_match_the_native_certificate :
  match right_equality_proposal compiler_rhs_equality_goal,
        compile_rule_descriptor [] compiler_rhs_equality_goal (RDRightEquality 1 (Exist 5) zero) with
  | Some p,Some c => application_matches p (certified_rule [] compiler_rhs_equality_goal c)
  | _,_ => true end = false.
Proof. vm_compute; reflexivity. Qed.
Example native_right_discharge_agrees_with_native_labels :
  compilation_matches [] (compiler_label [Pred 3 "A" [compiler_x]]
    [[Pred 8 "A" [compiler_x];Pred 0 "B" []]]) RDDischargeRight
    [compiler_label [Pred 3 "A" [compiler_x]] [[Pred 0 "B" []]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_injectivity_expands_in_place_and_keeps_prefix_and_duplicates :
  let a := Pred 3 "A" [compiler_x] in
  compilation_matches [] (compiler_label [a;Eq (cons compiler_x zero) (cons compiler_y zero);a] [])
    (RDLeftInjective 0 1)
    [compiler_label [a;Eq compiler_x compiler_y;Eq zero zero;a] []] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_injectivity_rejects_the_wrong_atom_position :
  compilation_present [] (compiler_label
    [Pred 3 "A" [];Eq (successor compiler_x) (successor compiler_y)] [])
    (RDLeftInjective 0 0) = false.
Proof. vm_compute; reflexivity. Qed.
Example native_right_congruence_expands_in_place_and_moves_the_changed_product :
  compilation_matches [] (compiler_label []
    [[Pred 0 "UNCHANGED" []];[Pred 0 "PREFIX" [];Eq (Fun "g" [compiler_x]) (Fun "g" [compiler_y])]])
    (RDRightCongruence 1 1)
    [compiler_label [] [[Pred 0 "PREFIX" [];Eq compiler_x compiler_y];[Pred 0 "UNCHANGED" []]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_left_disjunction_has_exactly_all_native_premises :
  compilation_matches [] {| antecedent := [[Pred 3 "A" []];[Pred 4 "B" []]]; succedent := [] |}
    RDLeftDisjunction [compiler_label [Pred 3 "A" []] [];compiler_label [Pred 4 "B" []] []] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_instantiation_is_product_local_with_prime_scope_preserved :
  compilation_matches [] (compiler_label [Pred 3 "FREE" [compiler_goal_var]]
    [[Pred 0 "KEEP" [compiler_e]];[Pred 0 "CHANGE" [compiler_e]]])
    (RDInstantiateAt 1 (Exist 0) compiler_goal_var)
    [compiler_label [Pred 3 "FREE" [compiler_goal_var]]
      [[Pred 0 "CHANGE" [compiler_goal_var]];[Pred 0 "KEEP" [compiler_e]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_instantiation_rejects_a_free_domain :
  compilation_present [] (compiler_label [] [[Pred 0 "A" [compiler_x]]])
    (RDInstantiateAt 0 (Free 0) compiler_y) = false.
Proof. vm_compute; reflexivity. Qed.
Example native_binary_right_split_matches_its_two_actual_premises :
  compilation_matches [] (compiler_label []
    [[Pred 0 "A" [compiler_e];Pred 0 "B" [Var (Exist 1)];Pred 0 "C" [Var (Exist 2)]]])
    (RDRightSplit 1)
    [compiler_label [] [[Pred 0 "A" [compiler_e]]];
     compiler_label [] [[Pred 0 "B" [Var (Exist 1)];Pred 0 "C" [Var (Exist 2)]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example legacy_right_conjunction_descriptor_compiles_to_binary_not_flat_splitting :
  let j := compiler_label [] [[Pred 0 "A" [];Pred 0 "B" [];Pred 0 "C" []]] in
  match right_split_proposals j,compile_rule_descriptor [] j RDRightConjunction with
  | [p],Some c => application_matches p (certified_rule [] j c)
  | _,_ => true end = false.
Proof. vm_compute; reflexivity. Qed.
Example binary_split_rejects_shared_prime_witnesses :
  compilation_present [] (compiler_label [] [[Pred 0 "A" [compiler_e];Pred 0 "B" [compiler_e]]])
    (RDRightSplit 1) = false.
Proof. vm_compute; reflexivity. Qed.

Definition compiler_right_goal := compiler_label [] [[Pred 0 "MEASURE" [successor compiler_goal_var]]].
Example optimized_right_unfold_retains_all_head_equalities :
  compilation_matches compiler_definitions compiler_right_goal (RDRightUnfoldMatched 12 0 0 1)
    [compiler_label [] [[Eq (successor compiler_goal_var) (successor compiler_goal_var);
                        Pred 0 "MEASURE" [compiler_goal_var]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example plain_native_right_unfold_descriptor_also_recompiles :
  compilation_present compiler_definitions compiler_right_goal (RDRightUnfold 0 0 1) = true.
Proof. vm_compute; reflexivity. Qed.
Example plain_right_unfold_matches_its_class_preserving_native_clause_layout :
  compilation_matches compiler_definitions compiler_right_goal (RDRightUnfold 0 0 1)
    [compiler_label [] [[Eq (successor compiler_goal_var) (successor (Var (Free 8)));
                        Pred 0 "MEASURE" [Var (Free 8)]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example optimized_right_unfold_reconstructs_repeated_head_constraints :
  compilation_matches compiler_definitions
    (compiler_label [] [[Pred 0 "RELATE" [compiler_goal_var;zero]]])
    (RDRightUnfoldMatched 12 0 0 2)
    [compiler_label [] [[Eq compiler_goal_var compiler_goal_var;Eq zero compiler_goal_var;
                        Pred 0 "MEASURE" [compiler_goal_var]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example right_unfold_candidates_respect_matching_fuel :
  compiled_right_unfold_proposals {| matching_fuel := 0; simplification_steps := 3;
    candidate_limit := 10; combination_limit := 10 |} compiler_definitions compiler_right_goal = [].
Proof. vm_compute; reflexivity. Qed.
Example right_unfold_recovers_actual_atom_position_after_a_prefix :
  map proposal_descriptor (compiled_right_unfold_proposals compiler_limits compiler_definitions
    (compiler_label [] [[Pred 0 "UNDEFINED" [];Pred 0 "MEASURE" [successor compiler_goal_var]]])) =
    [RDRightUnfoldMatched 12 0 1 1].
Proof. vm_compute; reflexivity. Qed.
Example checked_right_instance_scope_completes_unmatched_free_clause_locals :
  let j := compiler_label [] [[Pred 0 "HIDDEN" [compiler_goal_var]]] in
  match compiled_right_unfold_proposals compiler_limits compiler_definitions j with
  | [p] => match p.(proposal_descriptor),p.(proposal_premises) with
    | RDRightUnfoldInstance _ _ _ _,[k] =>
      (proposal_compilableb compiler_definitions p,
       filter is_free (formula_vars k.(succedent)))
    | _,_ => (false,[]) end
  | _ => (false,[]) end = (true,[Free 7;Free 7]).
Proof. vm_compute; reflexivity. Qed.
Example right_instance_descriptor_matches_the_completed_prime_witness_layout :
  compilation_matches compiler_definitions (compiler_label [] [[Pred 0 "HIDDEN" [compiler_goal_var]]])
    (RDRightUnfoldInstance 0 0 3 [(Free 8,compiler_goal_var);(Free 9,Var (Exist 10))])
    [compiler_label [] [[Eq compiler_goal_var compiler_goal_var;
                        Pred 0 "MEASURE" [Var (Exist 10)]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example input_prime_clause_locals_stay_prime_and_fresh :
  match compiled_right_unfold_proposals compiler_limits compiler_definitions
    (compiler_label [] [[Pred 0 "PRIMED" [compiler_goal_var]]]) with
  | [p] => match p.(proposal_premises) with
    | [k] => existential_variables (formula_vars k.(succedent)) | _ => [] end
  | _ => [] end = [Exist 8].
Proof. vm_compute; reflexivity. Qed.
Example right_unfold_rejects_a_nonpredicate_atom_descriptor :
  compilation_present compiler_definitions (compiler_label [] [[Eq zero zero]])
    (RDRightUnfoldMatched 12 0 0 0) = false.
Proof. vm_compute; reflexivity. Qed.
Example right_unfold_rejects_a_wrong_definition_member :
  compilation_present compiler_definitions compiler_right_goal
    (RDRightUnfoldMatched 12 0 0 99) = false.
Proof. vm_compute; reflexivity. Qed.

Definition compiler_left_goal := compiler_label
  [Deq compiler_goal_var zero;Pred 3 "MEASURE" [compiler_goal_var];Pred 3 "MEASURE" [compiler_goal_var]] [].
Example native_left_unfold_preserves_all_clause_cases_and_occurrence_positions :
  match compiled_proposal compiler_definitions compiler_left_goal (RDLeftUnfoldAt 0 1 4) with
  | Some p => (List.length p.(proposal_premises),proposal_compilableb compiler_definitions p)
  | None => (0,false) end = (2,true).
Proof. vm_compute; reflexivity. Qed.
Example native_left_unfold_matches_literal_body_equalities_copy_prefix_suffix_layout :
  compilation_matches compiler_definitions compiler_left_goal (RDLeftUnfoldAt 0 1 4)
    [compiler_label [Eq compiler_goal_var zero;Pred 4 "MEASURE" [compiler_goal_var];
                    Deq compiler_goal_var zero;Pred 3 "MEASURE" [compiler_goal_var]] [];
     compiler_label [Pred 3 "MEASURE" [Var (Free 8)];Eq compiler_goal_var (successor (Var (Free 8)));
                    Pred 4 "MEASURE" [compiler_goal_var];Deq compiler_goal_var zero;
                    Pred 3 "MEASURE" [compiler_goal_var]] []] = true.
Proof. vm_compute; reflexivity. Qed.
Example legacy_singleton_left_unfold_uses_the_native_layout :
  compilation_present compiler_definitions compiler_left_goal (RDLeftUnfold 1 4) = true.
Proof. vm_compute; reflexivity. Qed.
Example repeated_left_atoms_have_distinct_recompilable_descriptors :
  map proposal_descriptor (compiled_left_unfold_proposals compiler_limits compiler_definitions compiler_left_goal)
    = [RDLeftUnfoldAt 0 1 4;RDLeftUnfoldAt 0 2 4].
Proof. vm_compute; reflexivity. Qed.
Definition compiler_disjunctive_goal := {| antecedent :=
  [[Pred 3 "MEASURE" [compiler_goal_var]];
   [Deq compiler_x zero;Pred 9 "MEASURE" [compiler_x]]]; succedent := [] |}.
Example native_disjunctive_unfold_keeps_pass_through_premises :
  match compiled_proposal compiler_definitions compiler_disjunctive_goal (RDLeftUnfoldAt 1 1 10) with
  | Some p => (List.length p.(proposal_premises),proposal_compilableb compiler_definitions p)
  | None => (0,false) end = (3,true).
Proof. vm_compute; reflexivity. Qed.
Example left_unfold_rejects_an_incorrect_fresh_tag :
  compilation_present compiler_definitions compiler_left_goal (RDLeftUnfoldAt 0 1 3) = false.
Proof. vm_compute; reflexivity. Qed.

Definition compiler_fold_goal := compiler_label
  [Pred 3 "MEASURE" [compiler_goal_var];Pred 20 "ANCHOR" [zero];Pred 4 "MEASURE" [compiler_goal_var]] [].
Example native_fold_uses_raw_clause_substitution_and_native_remainder_layout :
  compilation_matches compiler_definitions compiler_fold_goal (RDFold 5 [(Free 0,compiler_goal_var)] 21)
    [compiler_label [Pred 21 "PACKED" [successor compiler_goal_var];Pred 20 "ANCHOR" [zero]] []] = true.
Proof. vm_compute; reflexivity. Qed.
Example fold_enumeration_matches_raw_clause_domains_not_freshened_domains :
  existsb (fun p => match p.(proposal_descriptor) with
    | RDFold 5 theta _ => eqb_of_dec native_substitution_eq_dec theta [(Free 0,compiler_goal_var)]
    | _ => false end)
    (compiled_fold_proposals compiler_limits compiler_definitions compiler_fold_goal) = true.
Proof. vm_compute; reflexivity. Qed.
Example empty_fold_cases_are_skipped :
  compilation_present compiler_definitions compiler_fold_goal (RDFold 0 [] 21) = false.
Proof. vm_compute; reflexivity. Qed.
Example folding_rejects_a_body_not_present_in_the_source :
  compilation_present compiler_definitions (compiler_label [Pred 20 "ANCHOR" [zero]] [])
    (RDFold 5 [(Free 0,compiler_goal_var)] 21) = false.
Proof. vm_compute; reflexivity. Qed.

Definition compiler_companion := compiler_label [Pred 4 "KEEP" [compiler_x]]
  [[Pred 0 "OUT" [compiler_x;compiler_e]]].
Definition compiler_link_source := compiler_label [Pred 4 "KEEP" [compiler_goal_var];Eq compiler_goal_var zero]
  [[Pred 0 "OUT" [compiler_goal_var;compiler_e]]].
Example native_weakening_matches_the_exact_expected_target :
  let target := subst_sequent [(Free 0,compiler_goal_var)] compiler_companion in
  compilation_matches [] compiler_link_source (RDWeaken target) [target] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_backward_substitution_matches_the_exact_companion :
  compilation_matches [] (subst_sequent [(Free 0,compiler_goal_var)] compiler_companion)
    (RDSubstitute [(Free 0,compiler_goal_var)] compiler_companion) [compiler_companion] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_backward_substitution_rejects_a_wrong_conclusion :
  compilation_present [] compiler_link_source
    (RDSubstitute [(Free 0,compiler_goal_var)] compiler_companion) = false.
Proof. vm_compute; reflexivity. Qed.
Example compiled_backlinks_strip_identity_prime_bindings_without_changing_scope :
  map backlink_substitution (compiled_backlink_plans compiler_limits [] 0 compiler_link_source
    [(3,compiler_companion)]) = [[(Free 0,compiler_goal_var)]].
Proof. vm_compute; reflexivity. Qed.
Example compiled_backlink_preparation_is_exact_weaken_then_substitution :
  map (fun b => (backlink_compilableb [] b,map proposal_descriptor b.(backlink_preparation)))
    (compiled_backlink_plans compiler_limits [] 0 compiler_link_source [(3,compiler_companion)]) =
  [(true,[RDWeaken (subst_sequent [(Free 0,compiler_goal_var)] compiler_companion);
          RDSubstitute [(Free 0,compiler_goal_var)] compiler_companion])].
Proof. vm_compute; reflexivity. Qed.
Example genuine_prime_renaming_uses_the_scoped_native_certificate :
  let source := compiler_label [Pred 4 "KEEP" [compiler_goal_var]]
    [[Pred 0 "OUT" [compiler_goal_var;Var (Exist 1)]]] in
  map (fun b => (backlink_compilableb [] b,b.(backlink_substitution)))
    (compiled_backlink_plans compiler_limits [] 0 source [(3,compiler_companion)]) =
  [(true,[(Exist 0,Var (Exist 1));(Free 0,compiler_goal_var)])].
Proof. vm_compute; reflexivity. Qed.
Example scoped_native_substitution_rejects_capture_of_an_unmapped_prime :
  let target := compiler_label [Pred 4 "KEEP" [compiler_x]]
    [[Pred 0 "OUT" [Var (Exist 0);Var (Exist 1)]]] in
  let theta := [(Exist 0,Var (Exist 1))] in
  compilation_present [] (subst_sequent theta target) (RDSubstitute theta target) = false.
Proof. vm_compute; reflexivity. Qed.
Example scoped_native_substitution_accepts_an_injective_prime_swap :
  let target := compiler_label [Pred 4 "KEEP" [compiler_x]]
    [[Pred 0 "OUT" [Var (Exist 0);Var (Exist 1)]]] in
  let theta := [(Exist 0,Var (Exist 1));(Exist 1,Var (Exist 0))] in
  compilation_matches [] (subst_sequent theta target) (RDSubstitute theta target) [target] = true.
Proof. vm_compute; reflexivity. Qed.
Example native_substitution_rejects_a_free_to_prime_capture :
  let theta := [(Free 0,compiler_e)] in
  compilation_present [] (subst_sequent theta compiler_companion)
    (RDSubstitute theta compiler_companion) = false.
Proof. vm_compute; reflexivity. Qed.
Example symmetric_raw_weakening_is_not_pretended_to_match_an_exact_native_check :
  let target := compiler_label [Eq compiler_x zero;Pred 4 "KEEP" [compiler_x]] [] in
  let source := compiler_label [Eq zero compiler_goal_var;Pred 4 "KEEP" [compiler_goal_var]] [] in
  (List.length (backlink_plans compiler_limits 0 source [(3,target)]),
   List.length (compiled_backlink_plans compiler_limits [] 0 source [(3,target)])) = (1,0).
Proof. vm_compute; reflexivity. Qed.

Definition compiler_combined_goal := compiler_label [Pred 3 "MEASURE" [compiler_goal_var]]
  [[Pred 0 "RELATE" [compiler_goal_var;zero]]].
Example combined_native_unfold_programs_recompile_every_intermediate_application :
  let ps := compiled_combined_unfold_programs compiler_limits compiler_definitions compiler_combined_goal in
  (negb (Nat.eqb (List.length ps) 0),forallb (program_compilableb compiler_definitions) ps) = (true,true).
Proof. vm_compute; reflexivity. Qed.
Example native_fold_is_available_only_with_an_immediate_compilable_backlink :
  compiled_fold_backlink_programs compiler_limits compiler_definitions compiler_fold_goal [] = [].
Proof. vm_compute; reflexivity. Qed.
Example native_fold_can_link_to_the_pre_fold_conclusion_node :
  let d := [compiler_step] in
  let j := compiler_label [Pred 3 "MEASURE" [compiler_goal_var];Pred 20 "ANCHOR" [zero]] [] in
  map (fun p => (List.length (program_frontier p),program_compilableb d p))
    (compiled_fold_backlink_programs compiler_limits d j [(0,j)]) = [(0,true)].
Proof. vm_compute; reflexivity. Qed.
Example native_normalization_keeps_fuel_exhaustion_as_an_open_frontier :
  List.length (program_frontier (compiled_normalize_program 3 []
    (compiler_label [Eq compiler_x (successor compiler_x)] []))) = 1.
Proof. vm_compute; reflexivity. Qed.
Example native_normalization_refuses_unchanged_rules_and_commits_to_first_changed_priority :
  option_map proposal_descriptor (compiled_simplification_proposal []
    (compiler_label [Eq compiler_x zero;Eq zero zero] [])) = Some RDTrivialEqualities.
Proof. vm_compute; reflexivity. Qed.
Example normalized_right_unfold_uses_only_native_premises :
  match compiled_right_unfold_proposals compiler_limits compiler_definitions compiler_right_goal with
  | [p] => program_frontier (compiled_wrapped_program compiler_limits compiler_definitions p)
  | _ => [] end = [compiler_label [] [[Pred 0 "MEASURE" [compiler_goal_var]]]].
Proof. vm_compute; reflexivity. Qed.

Definition compiler_many_goals := [compiler_right_goal;compiler_left_goal;compiler_disjunctive_goal;
  compiler_rhs_equality_goal;compiler_combined_goal;
  compiler_label [] [[Pred 0 "HIDDEN" [compiler_goal_var]]];
  compiler_label [Eq compiler_x zero] [[Eq compiler_y zero]];
  compiler_label [] [[Pred 0 "A" [compiler_e];Pred 0 "B" [Var (Exist 1)]]]].
Example every_generated_multi_goal_menu_application_matches_its_native_certificate :
  forallb (fun j => forallb (program_compilableb compiler_definitions)
    (all_compiler_programs (compiled_source_menu compiler_limits compiler_definitions 0 j [])))
    compiler_many_goals = true.
Proof. vm_compute; reflexivity. Qed.
Example compiled_menus_are_nonempty_across_modified_unseen_goals :
  forallb (fun j => negb (Nat.eqb (List.length
    (all_compiler_programs (compiled_source_menu compiler_limits compiler_definitions 0 j []))) 0))
    compiler_many_goals = true.
Proof. vm_compute; reflexivity. Qed.
Example compiled_menu_simplification_has_greedy_priority_over_unfolding :
  let j := compiler_label [Eq zero zero] [[Pred 0 "MEASURE" [compiler_goal_var]]] in
  let menu := compiled_source_menu compiler_limits compiler_definitions 0 j [] in
  (List.length menu.(menu_axioms),List.length menu.(menu_simplifications),List.length menu.(menu_choices))
    = (0,1,0).
Proof. vm_compute; reflexivity. Qed.

(** Independent graph API from SearchExamples, now driven by the real native
    compiler/menu. Parent graph certification is not needed for these acyclic
    algorithm checks; final cyclic certification remains the caller contract. *)
Definition compiler_graph_api d limits : search_api d example_graph :=
  {| node_label := example_lookup;
     node_indices := fun g => seq 0 (List.length g.(example_labels));
     generate_rules := fun g i j => compiled_source_menu limits d i j
       (flat_map (fun n => match example_lookup g n with
         | Some k => [(n,k)] | None => [] end)
         (seq 0 (List.length g.(example_labels))));
     compile_descriptor := compile_rule_descriptor d;
     apply_application := example_apply d;
     close_exact := example_close_exact;
     partial_trace_check := fun _ => true;
     final_accept := example_closedb |}.
Definition compiler_graph j := {| example_labels := [j]; example_open := [0]; example_steps := 0 |}.
Definition compiler_structural_goal := compiler_label [Pred 3 "A" [compiler_x];Pred 4 "B" [compiler_y]]
  [[Pred 0 "A" [compiler_x];Pred 0 "B" [compiler_y]]].
Example native_compiler_drives_generic_acyclic_search_on_modified_goals :
  map (fun j => result_depth (iddfs (compiler_graph_api compiler_definitions compiler_limits)
    200 40 0 3 (compiler_graph j) 0))
    [compiler_label [Pred 3 "UNSEEN" [compiler_x]] [[Pred 9 "UNSEEN" [compiler_x]]];
     compiler_label [Deq compiler_x compiler_x] [];
     compiler_label [] [[Pred 0 "MEASURE" [zero]]];
     compiler_label [] [[Pred 0 "RELATE" [zero;zero]]];
     compiler_structural_goal] = [Some 0;Some 0;Some 1;Some 2;Some 0].
Proof. vm_compute; reflexivity. Qed.
Example native_binary_conjunction_search_closes_both_updated_graph_branches :
  let j := compiler_label [] [[Pred 0 "MEASURE" [zero];Pred 0 "MEASURE" [zero]]] in
  match iddfs (compiler_graph_api compiler_definitions compiler_limits) 200 40 0 3
      (compiler_graph j) 0 with
  | Found g depth => (depth,List.length g.(example_labels),g.(example_steps),g.(example_open))
  | Unknown _ => (0,0,0,[0]) end = (2,7,7,[]).
Proof. vm_compute; reflexivity. Qed.
Example native_disjunction_wrapping_normalizes_and_closes_every_case :
  let j := {| antecedent :=
    [[Eq compiler_x zero;Pred 3 "A" [compiler_x]];
     [Eq compiler_x (successor zero);Pred 4 "B" [compiler_x]]];
    succedent := [[Pred 0 "A" [zero]];[Pred 0 "B" [successor zero]]] |} in
  match iddfs (compiler_graph_api compiler_definitions compiler_limits) 200 40 0 2
      (compiler_graph j) 0 with
  | Found g depth => (depth,List.length g.(example_labels),g.(example_steps),g.(example_open))
  | Unknown _ => (0,0,0,[0]) end = (1,9,9,[]).
Proof. vm_compute; reflexivity. Qed.
Example native_equation_fallback_supplies_a_prime_base_case_witness :
  let j := compiler_label [] [[Pred 0 "MEASURE" [compiler_e]]] in
  result_depth (iddfs (compiler_graph_api compiler_definitions compiler_limits) 200 40 0 2
    (compiler_graph j) 0) = Some 1.
Proof. vm_compute; reflexivity. Qed.
Example completed_clause_local_witnesses_are_executable_without_goal_dispatch :
  let j := compiler_label [] [[Pred 0 "HIDDEN" [compiler_goal_var]]] in
  result_depth (iddfs (compiler_graph_api compiler_definitions compiler_limits) 200 40 0 3
    (compiler_graph j) 0) = Some 2.
Proof. vm_compute; reflexivity. Qed.
Example certified_rule_menu_alias_uses_the_new_native_menu :
  certified_rule_menu compiler_limits compiler_definitions 0 compiler_right_goal [] =
    compiled_source_menu compiler_limits compiler_definitions 0 compiler_right_goal [].
Proof. reflexivity. Qed.
