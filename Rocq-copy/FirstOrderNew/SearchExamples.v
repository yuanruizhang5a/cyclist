From Stdlib Require Import List Bool Arith String Lia.
From CyclistRocq.FirstOrderNew Require Import Search.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(** These definitions deliberately use symbols and clauses absent from the
    source benchmarks. All tests call the general enumerator or abstract DFS. *)
Definition test_v := Var (Free 7).
Definition test_clause name args atoms :=
  {| clause_name := name; head := args; body := atoms |}.
Definition test_definitions :=
  [test_clause "TALLY" [zero] [];
   test_clause "TALLY" [successor (Var (Free 0))]
     [Pred 0 "TALLY" [Var (Free 0)]];
   test_clause "PAIR" [Var (Free 0);Var (Free 0)]
     [Pred 0 "TALLY" [Var (Free 0)]];
   test_clause "WITNESS" [Var (Free 0)]
     [Pred 0 "TALLY" [Var (Free 1)]]].
Definition changed_test_definitions :=
  [test_clause "TALLY" [zero] [];
   test_clause "TALLY" [successor (Var (Free 0))]
     [Eq (Var (Free 0)) zero;Pred 0 "TALLY" [Var (Free 0)]]].
Definition test_unfold_goal := {| antecedent := [[]];
  succedent := [[Pred 0 "TALLY" [successor test_v]]] |}.

Example different_predicate_generates_right_unfold :
  map proposal_descriptor (right_unfold_proposals default_generation_limits
    test_definitions test_unfold_goal) = [RDRightUnfold 0 0 1].
Proof. vm_compute; reflexivity. Qed.
Example changed_clause_changes_generated_premise :
  map proposal_premises (right_unfold_proposals default_generation_limits
    changed_test_definitions test_unfold_goal) =
  [[{| antecedent := [[]];
       succedent := [[Eq test_v zero;Pred 0 "TALLY" [test_v]]] |}]].
Proof. vm_compute; reflexivity. Qed.
Example unchanged_clause_has_different_premise :
  map proposal_premises (right_unfold_proposals default_generation_limits
    test_definitions test_unfold_goal) =
  [[{| antecedent := [[]]; succedent := [[Pred 0 "TALLY" [test_v]]] |}]].
Proof. vm_compute; reflexivity. Qed.
Example right_unfold_preserves_prime_local_scope :
  match right_unfold_at default_generation_limits test_definitions
    {| antecedent := [[]]; succedent := [[Pred 0 "WITNESS" [test_v]]] |} 0 0 3 with
  | Some p => map (fun j => forallb (fun v => negb (is_free v))
                      (formula_vars j.(succedent))) p.(proposal_premises)
  | None => [] end = [true].
Proof. vm_compute; reflexivity. Qed.
Example repeated_head_emits_a_real_constraint :
  match right_unfold_at default_generation_limits test_definitions
    {| antecedent := [[]]; succedent := [[Pred 0 "PAIR" [test_v;zero]]] |} 0 0 2 with
  | Some p => p.(proposal_premises) | None => [] end =
  [{| antecedent := [[]];
      succedent := [[Pred 0 "TALLY" [test_v];Eq test_v zero]] |}].
Proof. vm_compute; reflexivity. Qed.
Example generic_left_unfold_has_all_cases_and_contraction :
  match left_unfold_at test_definitions
    {| antecedent := [[Pred 5 "TALLY" [test_v]]]; succedent := [] |} 0 with
  | Some p => (p.(proposal_descriptor),List.length p.(proposal_premises),
      forallb (fun j => existsb (fun q => mem_atom (Pred 6 "TALLY" [test_v]) q)
                     j.(antecedent)) p.(proposal_premises))
  | None => (RDIdentity,0,false) end = (RDLeftUnfold 0 6,2,true).
Proof. vm_compute; reflexivity. Qed.
Example generic_fold_matches_a_non_source_clause :
  existsb (fun p => match p.(proposal_descriptor) with
    | RDFold 1 _ _ => true | _ => false end)
    (fold_proposals default_generation_limits test_definitions
      {| antecedent := [[Pred 3 "TALLY" [test_v]]]; succedent := [] |}) = true.
Proof. vm_compute; reflexivity. Qed.

Example shared_prime_prevents_right_conjunction_split :
  right_split_proposals {| antecedent := [[]]; succedent :=
    [[Pred 0 "A" [Var (Exist 0)];Pred 0 "B" [Var (Exist 0)]]] |} = [].
Proof. reflexivity. Qed.
Example disjoint_primes_allow_right_conjunction_split :
  map proposal_descriptor (right_split_proposals
    {| antecedent := [[]]; succedent :=
      [[Pred 0 "A" [Var (Exist 0)];Pred 0 "B" [Var (Exist 1)]]] |}) =
  [RDRightConjunction].
Proof. reflexivity. Qed.
Example arbitrary_prime_and_free_names_generate_instantiation :
  map proposal_descriptor (instantiate_proposals default_generation_limits
    {| antecedent := [[Pred 2 "A" [test_v]]];
       succedent := [[Pred 0 "B" [Var (Exist 19)]]] |}) =
  [RDInstantiate (Exist 19) test_v].
Proof. vm_compute; reflexivity. Qed.
Example source_left_disjunction_family_is_generic :
  map proposal_descriptor (left_split_proposals
    {| antecedent := [[Pred 1 "A" []];[Pred 2 "B" []]]; succedent := [] |}) =
  [RDLeftDisjunction].
Proof. reflexivity. Qed.

Definition first_simplifier j := option_map proposal_descriptor
  (simplification_proposal j).
Example simplify_trivial_has_source_priority :
  first_simplifier {| antecedent := [[Eq test_v zero;Eq zero zero]];
    succedent := [] |} = Some RDTrivialEqualities.
Proof. vm_compute; reflexivity. Qed.
Example simplify_left_equality_is_generated :
  first_simplifier {| antecedent := [[Eq test_v zero]];
    succedent := [[Pred 0 "B" [test_v]]] |} =
  Some (RDLeftEquality (Free 7) zero).
Proof. vm_compute; reflexivity. Qed.
Example simplify_prime_equality_is_product_local :
  match right_equality_proposal {| antecedent := [[]]; succedent :=
    [[Eq (Var (Exist 3)) zero;Pred 0 "A" [Var (Exist 3)]];
     [Pred 0 "B" [Var (Exist 3)]]] |} with
  | Some p => p.(proposal_premises) | None => [] end =
  [{| antecedent := [[]]; succedent :=
    [[Eq zero zero;Pred 0 "A" [zero]];[Pred 0 "B" [Var (Exist 3)]]] |}].
Proof. vm_compute; reflexivity. Qed.
Example simplify_right_discharge_is_generated :
  first_simplifier {| antecedent := [[Pred 4 "A" [test_v]]];
    succedent := [[Pred 9 "A" [test_v];Pred 0 "B" []]] |} =
  Some RDDischargeRight.
Proof. vm_compute; reflexivity. Qed.
Example simplify_left_injective_is_generated :
  first_simplifier {| antecedent := [[Eq (successor test_v) (successor zero)]];
    succedent := [] |} = Some (RDLeftInjective 0 0).
Proof. vm_compute; reflexivity. Qed.
Example simplify_right_congruence_is_generated :
  first_simplifier {| antecedent := [[]];
    succedent := [[Eq (Fun "arbitrary" [test_v]) (Fun "arbitrary" [zero])]] |} =
  Some (RDRightCongruence 0 0).
Proof. vm_compute; reflexivity. Qed.
Example malformed_constructor_does_not_claim_injectivity :
  expand_proposal true {| antecedent := [[Eq (Fun "s" []) (Fun "s" [])]];
    succedent := [] |} = None.
Proof. reflexivity. Qed.

Definition test_backlink_target := {| antecedent := [[Pred 4 "MOVED" [Var (Free 0)]]];
  succedent := [[Pred 0 "OK" [Var (Free 0)]]] |}.
Definition test_backlink_source := {| antecedent := [[Pred 4 "MOVED" [test_v];
  Eq test_v zero]]; succedent := [[Pred 0 "OK" [test_v]]] |}.
Example backlink_matches_changed_variables_and_context :
  map backlink_substitution (backlink_plans_for default_generation_limits
    test_backlink_source 13 test_backlink_target) = [[(Free 0,test_v)]].
Proof. vm_compute; reflexivity. Qed.
Example backlink_makes_weaken_then_substitution_explicit :
  map (fun b => map proposal_descriptor b.(backlink_preparation))
    (backlink_plans_for default_generation_limits test_backlink_source 13
      test_backlink_target) =
  [[RDWeaken (subst_sequent [(Free 0,test_v)] test_backlink_target);
    RDSubstitute [(Free 0,test_v)] test_backlink_target]].
Proof. vm_compute; reflexivity. Qed.
Example backlink_retains_occurrence_not_just_logical_tag :
  map (fun b => b.(backlink_exact_edge).(continuations))
    (backlink_plans_for default_generation_limits test_backlink_source 13
      test_backlink_target) = [[(0,0)]].
Proof. vm_compute; reflexivity. Qed.
Example all_other_nodes_include_a_sibling_and_exclude_self :
  map backlink_target_index (backlink_plans default_generation_limits 0
    test_backlink_source [(0,test_backlink_source);(13,test_backlink_target)]) = [13].
Proof. vm_compute; reflexivity. Qed.
Example zero_matching_fuel_exits_without_a_backlink :
  backlink_plans_for {| matching_fuel := 0; simplification_steps := 1;
    candidate_limit := 20; combination_limit := 20 |}
    test_backlink_source 13 test_backlink_target = [].
Proof. vm_compute; reflexivity. Qed.
Example zero_candidate_limit_is_safe :
  right_unfold_proposals {| matching_fuel := 10; simplification_steps := 10;
    candidate_limit := 0; combination_limit := 0 |}
    test_definitions test_unfold_goal = [].
Proof. reflexivity. Qed.
Example prime_renaming_cannot_capture_an_unmapped_prime :
  substitution_scopedb [(Exist 0,Var (Exist 1))]
    {| antecedent := [[]]; succedent :=
      [[Pred 0 "A" [Var (Exist 0);Var (Exist 1)]]] |} = false.
Proof. vm_compute; reflexivity. Qed.
Example prime_renaming_can_swap_two_primes :
  substitution_scopedb [(Exist 0,Var (Exist 1));(Exist 1,Var (Exist 0))]
    {| antecedent := [[]]; succedent :=
      [[Pred 0 "A" [Var (Exist 0);Var (Exist 1)]]] |} = true.
Proof. vm_compute; reflexivity. Qed.
Example matching_keeps_both_equality_orientations :
  List.length (match_atom_candidates 10 []
    (Eq (Var (Free 0)) (Var (Free 1))) (Eq test_v zero)) = 2.
Proof. vm_compute; reflexivity. Qed.

Example bounded_normalization_leaves_an_open_frontier :
  List.length (program_frontier (normalize_program 3
    {| antecedent := [[Eq test_v (successor test_v)]]; succedent := [] |})) = 1.
Proof. vm_compute; reflexivity. Qed.
Example combined_left_right_unfold_is_a_real_branching_program :
  negb (Nat.eqb (List.length (combined_unfold_programs default_generation_limits
    test_definitions {| antecedent := [[Pred 3 "TALLY" [test_v]]];
      succedent := [[Pred 0 "PAIR" [test_v;zero]]] |})) 0) = true.
Proof. vm_compute; reflexivity. Qed.
Definition test_fold_definitions := [test_clause "PACKED" [Var (Free 0)]
  [Pred 0 "ATOM" [Var (Free 0)]]].
Definition test_fold_source := {| antecedent :=
  [[Pred 3 "ATOM" [test_v];Pred 20 "ANCHOR" [test_v]]];
  succedent := [[Pred 0 "RESULT" [test_v]]] |}.
Definition test_fold_target := {| antecedent :=
  [[Pred 21 "PACKED" [Var (Free 0)];Pred 20 "ANCHOR" [Var (Free 0)]]];
  succedent := [[Pred 0 "RESULT" [Var (Free 0)]]] |}.
Example source_folds_are_available_only_with_an_immediate_backlink :
  fold_backlink_programs default_generation_limits test_fold_definitions
    test_fold_source [] = [].
Proof. vm_compute; reflexivity. Qed.
Example folded_matching_uses_the_general_backlink_planner :
  map (fun p => List.length (program_frontier p))
    (fold_backlink_programs default_generation_limits test_fold_definitions
      test_fold_source [(7,test_fold_target)]) = [0].
Proof. vm_compute; reflexivity. Qed.
Example fold_can_backlink_to_its_pre_fold_conclusion_node :
  let d := [test_clause "CARRY" [successor (Var (Free 0))]
    [Pred 0 "CARRY" [Var (Free 0)]]] in
  let j := {| antecedent := [[Pred 3 "CARRY" [test_v];Pred 20 "ANCHOR" [zero]]];
             succedent := [] |} in
  List.length (fold_backlink_programs default_generation_limits d j [(0,j)]) = 1.
Proof. vm_compute; reflexivity. Qed.
Example source_menu_commits_to_simplification_before_choices :
  let menu := source_rule_menu default_generation_limits test_definitions 0
    {| antecedent := [[Eq zero zero]]; succedent := [[Pred 0 "TALLY" [test_v]]] |} [] in
  (List.length menu.(menu_axioms),List.length menu.(menu_simplifications),
   List.length menu.(menu_choices)) = (0,1,0).
Proof. vm_compute; reflexivity. Qed.

(** Minimal independent immutable graph used to exercise the DFS API. Local
    certificates below are genuine: identity closes a valid label, and unary
    self-transport is valid for every sequent. No benchmark symbol is inspected. *)
Definition example_axiom_application j := {| application_name := "test_id";
  conclusion := j; premises := [] |}.
Definition example_axiom_certificate d j (H : identityb j = true)
    : certified_application d j.
Proof.
  refine {| certified_rule := example_axiom_application j;
            certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; exfalso; apply Hbad.
  apply (proj1 (valid_iff_worlds d j)); apply identity_sound; exact H.
Defined.
Definition example_transport_certificate d j : certified_application d j.
Proof.
  refine {| certified_rule := {| application_name := "test_transport";
              conclusion := j; premises := [{| premise_label := j; premise_trace := empty_edge |}] |};
            certified_conclusion := eq_refl |}.
  constructor; intros w Hbad.
  exists 0, {| premise_label := j; premise_trace := empty_edge |}, w.
  split; [reflexivity|]. split; [exact Hbad|].
  split; intros a b H; contradiction.
Defined.
Definition example_split_application j := {| application_name := "test_split";
  conclusion := j; premises := map
    (fun k => {| premise_label := k; premise_trace := empty_edge |}) (lhs_split j) |}.
Lemma example_bounded_shift d m rho bs offset start p :
  bounded_product d m rho bs (offset + start) p ->
  bounded_product d m rho (fun n => bs (offset + n)) start p.
Proof.
  revert start; induction p as [|a p IH]; intros start Hb; cbn in *; [exact I|].
  destruct Hb as [Ha Hp]; split; [exact Ha|].
  apply IH. replace (offset + S start) with (S (offset + start)) by lia; exact Hp.
Qed.
Definition example_split_certificate d j : certified_application d j.
Proof.
  refine {| certified_rule := example_split_application j;
            certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; change (~ denote d j w) in Hbad.
  destruct (nth_error j.(antecedent) w.(active_product)) as [p|] eqn:E.
  - exists w.(active_product),
      {| premise_label := {| antecedent := [p]; succedent := j.(succedent) |};
         premise_trace := empty_edge |},
      {| world_model := w.(world_model); world_valuation := w.(world_valuation);
         active_product := 0;
         world_bounds := fun n => w.(world_bounds) (active_offset j w + n) |}.
    split.
    + cbn [example_split_application premises]. unfold lhs_split.
      rewrite !nth_error_map, E; reflexivity.
    + split.
      * intro Hden; apply Hbad; intros [q [Hq Hb]].
        change (nth_error j.(antecedent) w.(active_product) = Some q) in Hq.
        rewrite E in Hq; inversion Hq; subst q.
        apply Hden. exists p; split; [reflexivity|].
        change (bounded_product d w.(world_model) w.(world_valuation)
          (fun n => w.(world_bounds) (active_offset j w + n)) 0 p).
        apply example_bounded_shift; now rewrite Nat.add_0_r.
      * split; intros a b H; contradiction.
  - exfalso; apply Hbad; intros [p [Hp Hb]].
    change (nth_error j.(antecedent) w.(active_product) = Some p) in Hp.
    rewrite E in Hp; discriminate.
Defined.
Definition example_compiler d j rd : option (certified_application d j) :=
  match rd with
  | RDIdentity => match Bool.bool_dec (identityb j) true with
    | left H => Some (example_axiom_certificate d j H) | right _ => None end
  | RDLeftDisjunction => Some (example_split_certificate d j)
  | RDWeaken target => if sequent_eq_dec target j
      then Some (example_transport_certificate d j) else None
  | _ => None end.
Record example_graph := {
  example_labels : list sequent;
  example_open : list nat;
  example_steps : nat
}.
Definition example_lookup g i := nth_error g.(example_labels) i.
Definition example_apply d j g i (a : certified_application d j) :=
  if existsb (Nat.eqb i) g.(example_open) then
    let labels := map premise_label (certified_rule d j a).(premises) in
    let indices := seq (List.length g.(example_labels)) (List.length labels) in
    Some (indices,{| example_labels := g.(example_labels) ++ labels;
      example_open := filter (fun n => negb (Nat.eqb n i)) g.(example_open) ++ indices;
      example_steps := S g.(example_steps) |})
  else None.
Definition example_close_exact (g : example_graph) (i target : nat) (edge : trace_edge) :=
  if existsb (Nat.eqb i) g.(example_open) then
    Some {| example_labels := g.(example_labels);
      example_open := filter (fun n => negb (Nat.eqb n i)) g.(example_open);
      example_steps := S g.(example_steps) |}
  else None.
Definition example_closedb g := Nat.eqb (List.length g.(example_open)) 0.
Definition example_identity_goal := {| antecedent := [[Pred 2 "UNSEEN" [test_v]]];
  succedent := [[Pred 6 "UNSEEN" [test_v]]] |}.
Definition example_initial := {| example_labels := [example_identity_goal];
  example_open := [0]; example_steps := 0 |}.
Definition example_source_api : search_api [] example_graph :=
  {| node_label := example_lookup;
     node_indices := fun g => seq 0 (List.length g.(example_labels));
     generate_rules := fun g i j => source_rule_menu default_generation_limits [] i j
       (flat_map (fun n => match example_lookup g n with
         | Some k => [(n,k)] | None => [] end)
         (seq 0 (List.length g.(example_labels))));
     compile_descriptor := example_compiler [];
     apply_application := example_apply [];
     close_exact := example_close_exact;
     partial_trace_check := fun _ => true;
     final_accept := example_closedb |}.
Definition result_depth {State} (r : search_result State) := match r with
  | Found _ n => Some n | Unknown _ => None end.
Example generic_search_closes_an_unseen_identity_at_depth_zero :
  result_depth (iddfs example_source_api 20 50 0 3 example_initial 0) = Some 0.
Proof. vm_compute; reflexivity. Qed.
Example source_generator_can_be_installed_on_an_abstract_graph_api :
  result_depth (source_iddfs default_generation_limits example_source_api
    20 50 0 3 example_initial 0) = Some 0.
Proof. vm_compute; reflexivity. Qed.
Definition example_split_menu j :=
  if 2 <=? List.length j.(antecedent) then
    {| menu_axioms := []; menu_simplifications := [];
       menu_choices := [primitive_program (propose RDLeftDisjunction j (lhs_split j))] |}
  else {| menu_axioms := map primitive_program (axiom_proposals j);
          menu_simplifications := []; menu_choices := [] |}.
Definition example_split_api : search_api [] example_graph :=
  {| node_label := example_lookup;
     node_indices := fun g => seq 0 (List.length g.(example_labels));
     generate_rules := fun _ _ j => example_split_menu j;
     compile_descriptor := example_compiler [];
     apply_application := example_apply [];
     close_exact := example_close_exact;
     partial_trace_check := fun _ => true;
     final_accept := example_closedb |}.
Definition example_split_initial := {| example_labels :=
  [{| antecedent := [[Pred 1 "ONE" [test_v]];[Pred 2 "TWO" [test_v]]];
      succedent := [[Pred 0 "ONE" [test_v]];[Pred 0 "TWO" [test_v]]] |}];
  example_open := [0]; example_steps := 0 |}.
Example dfs_closes_every_branch_in_the_updated_immutable_graph :
  match iddfs example_split_api 50 10 0 2 example_split_initial 0 with
  | Found g depth => (depth,List.length g.(example_labels),g.(example_steps),g.(example_open))
  | Unknown _ => (0,0,0,[0]) end = (1,3,3,[]).
Proof. vm_compute; reflexivity. Qed.
Example zero_dfs_fuel_is_unknown :
  bounded_dfs example_source_api 0 50 0 example_initial 0 = Unknown FuelExhausted.
Proof. reflexivity. Qed.
Example zero_program_fuel_cannot_fake_a_proof :
  result_depth (bounded_dfs example_source_api 20 0 3 example_initial 0) = None.
Proof. vm_compute; reflexivity. Qed.

Definition example_alternative_menu j := {| menu_axioms := [];
  menu_simplifications := [];
  menu_choices := [primitive_program (propose RDIdentity j []);
    primitive_program (propose_unary (RDWeaken j) j j)] |}.
Definition example_reject_first_api : search_api [] example_graph :=
  {| node_label := example_lookup;
     node_indices := fun g => seq 0 (List.length g.(example_labels));
     generate_rules := fun _ _ j => example_alternative_menu j;
     compile_descriptor := example_compiler [];
     apply_application := example_apply [];
     close_exact := example_close_exact;
     partial_trace_check := fun _ => true;
     final_accept := fun g => example_closedb g && Nat.eqb g.(example_steps) 2 |}.
Example final_rejection_backtracks_and_iterative_deepening_finds_next_graph :
  result_depth (iddfs example_reject_first_api 100 10 0 3 example_initial 0) = Some 2.
Proof. vm_compute; reflexivity. Qed.
Example raw_candidate_is_separate_from_acceptance :
  result_depth (candidate_dfs example_reject_first_api 100 10 1 example_initial 0) = Some 1.
Proof. vm_compute; reflexivity. Qed.
Example rejected_raw_candidate_is_unknown :
  accept_candidate example_reject_first_api
    (candidate_dfs example_reject_first_api 100 10 1 example_initial 0) =
  Unknown AcceptanceRejected.
Proof. vm_compute; reflexivity. Qed.
Example maximum_depth_is_enforced :
  result_depth (iddfs example_reject_first_api 100 10 0 1 example_initial 0) = None.
Proof. vm_compute; reflexivity. Qed.
Example reversed_depth_interval_is_unknown :
  iddfs example_reject_first_api 100 10 3 1 example_initial 0 = Unknown DepthExhausted.
Proof. reflexivity. Qed.

Definition example_direct_backlink_menu g i j := {| menu_axioms := [];
  menu_simplifications := []; menu_choices := map ProgramBacklink
    (backlink_plans default_generation_limits i j
      (flat_map (fun n => match example_lookup g n with
       | Some k => [(n,k)] | None => [] end)
       (seq 0 (List.length g.(example_labels))))) |}.
Definition example_backlink_api : search_api [] example_graph :=
  {| node_label := example_lookup;
     node_indices := fun g => seq 0 (List.length g.(example_labels));
     generate_rules := example_direct_backlink_menu;
     compile_descriptor := example_compiler [];
     apply_application := example_apply [];
     close_exact := example_close_exact;
     partial_trace_check := fun _ => true;
     final_accept := example_closedb |}.
Definition example_two_nodes := {| example_labels := [example_identity_goal;example_identity_goal];
  example_open := [0]; example_steps := 0 |}.
Example abstract_graph_search_executes_exact_backlink_to_other_node :
  result_depth (bounded_dfs example_backlink_api 20 10 1 example_two_nodes 0) = Some 1.
Proof. vm_compute; reflexivity. Qed.

Definition example_bad_expected_menu j := {| menu_axioms := [];
  menu_simplifications := []; menu_choices :=
    [primitive_program (propose RDIdentity j [j])] |}.
Definition example_bad_expected_api : search_api [] example_graph :=
  {| node_label := example_lookup;
     node_indices := fun g => seq 0 (List.length g.(example_labels));
     generate_rules := fun _ _ j => example_bad_expected_menu j;
     compile_descriptor := example_compiler [];
     apply_application := example_apply [];
     close_exact := example_close_exact;
     partial_trace_check := fun _ => true;
     final_accept := example_closedb |}.
Example certificate_and_proposal_premises_must_agree :
  result_depth (bounded_dfs example_bad_expected_api 20 10 2 example_initial 0) = None.
Proof. vm_compute; reflexivity. Qed.
Example exact_backlinks_cannot_fabricate_a_progressing_edge :
  exact_backlink_edgeb example_identity_goal
    {| continuations := [(0,0)]; progressing := [(0,0)] |} = false.
Proof. reflexivity. Qed.
Example exact_backlinks_cannot_link_a_nonexistent_occurrence :
  exact_backlink_edgeb example_identity_goal
    {| continuations := [(17,17)]; progressing := [] |} = false.
Proof. vm_compute; reflexivity. Qed.
Definition example_reject_partial_api : search_api [] example_graph :=
  {| node_label := example_lookup;
     node_indices := fun g => seq 0 (List.length g.(example_labels));
     generate_rules := fun _ _ j => example_alternative_menu j;
     compile_descriptor := example_compiler [];
     apply_application := example_apply [];
     close_exact := example_close_exact;
     partial_trace_check := fun _ => false;
     final_accept := example_closedb |}.
Example partial_trace_rejection_prunes_graph_applications :
  result_depth (iddfs example_reject_partial_api 20 10 0 2 example_initial 0) = None.
Proof. vm_compute; reflexivity. Qed.
