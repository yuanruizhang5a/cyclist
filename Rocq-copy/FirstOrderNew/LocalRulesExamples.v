From Stdlib Require Import List String ZArith.
From CyclistRocq.FirstOrderNew Require Import LocalRules.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition example_rule_present {d j} (c : option (certified_application d j)) :=
  match c with Some _ => true | None => false end.
Definition example_premise {d j} (c : option (certified_application d j)) :=
  match c with Some c => match premises (certified_rule d j c) with
    | [p] => Some (premise_label p) | _ => None end | None => None end.
Definition example_continuations {d j} (c : option (certified_application d j)) :=
  match c with Some c => match premises (certified_rule d j c) with
    | [p] => Some (continuations (premise_trace p)) | _ => None end | None => None end.
Definition example_prefix_present {d j k s}
  (c : option (certified_application d j * certified_application d (subst_sequent s k))) :=
  match c with Some _ => true | None => false end.
Definition example_rule_names d j := map (fun c => application_name (certified_rule d j c)).

Definition example_x := Var (Free 0).
Definition example_y := Var (Free 1).
Definition example_e := Var (Exist 0).
Definition example_p t := Pred 7 "P" [t].
Definition example_q t := Pred 7 "Q" [t].

Example left_disjunction_uses_flattened_source_offsets :
  map (fun p => continuations (premise_trace p))
    (premises (certified_rule [] _ (left_disjunction []
      {| antecedent := [[Eq zero zero; example_p zero]; [example_p zero; example_q zero]];
         succedent := [] |}))) = [[(1,1)]; [(2,0); (3,1)]].
Proof. reflexivity. Qed.

Example trivial_equality_reindexes_occurrences :
  example_continuations (trivial_equality_rule []
    (singleton_label [Eq example_x example_x; example_p example_x; example_q example_x] [])) =
    Some [(1,0); (2,1)].
Proof. vm_compute; reflexivity. Qed.

Example trivial_equality_does_not_merge_duplicate_predicates :
  example_continuations (trivial_equality_rule []
    (singleton_label [Eq zero zero; example_p zero; example_p zero] [])) =
    Some [(1,0); (2,1)].
Proof. vm_compute; reflexivity. Qed.

Example exact_exchange_preserves_each_target_occurrence :
  example_continuations (checked_weakening []
    (singleton_label [example_p example_x; example_q example_y] [])
    (singleton_label [example_q example_y; example_p example_x] [])) = Some [(1,0); (0,1)].
Proof. vm_compute; reflexivity. Qed.

Example weakening_keeps_duplicate_target_occurrences :
  example_continuations (checked_weakening []
    (singleton_label [example_p example_x; Eq example_x zero] [[example_p example_x]; []])
    (singleton_label [example_p example_x; example_p example_x] [[example_p example_x]])) =
    Some [(0,0); (0,1)].
Proof. vm_compute; reflexivity. Qed.

Example weakening_does_not_accept_variable_matching :
  example_rule_present (checked_weakening []
    (singleton_label [example_p example_x] [])
    (singleton_label [example_p example_y] [])) = false.
Proof. vm_compute; reflexivity. Qed.

Definition example_companion := singleton_label [example_p example_x; example_p example_y] [].
Example backwards_substitution_keeps_collapsed_occurrences :
  example_continuations (checked_backward_substitution []
    [(Free 0,zero); (Free 1,zero)] example_companion) = Some [(0,0); (1,1)].
Proof. vm_compute; reflexivity. Qed.
Example backlinks_accept_free_only_instances_and_weakening :
  example_prefix_present (backlink_prefix []
    (singleton_label [Eq zero zero; example_p zero; example_p zero] [])
    example_companion [(Free 0,zero); (Free 1,zero)]) = true.
Proof. vm_compute; reflexivity. Qed.
Example backlink_weakening_preserves_collapsed_instance_multiplicity :
  example_continuations (checked_weakening []
    (singleton_label [Eq zero zero; example_p zero; example_p zero] [])
    (subst_sequent [(Free 0,zero); (Free 1,zero)] example_companion)) = Some [(1,0); (2,1)].
Proof. vm_compute; reflexivity. Qed.
Example backlinks_reject_free_to_existential_capture :
  example_rule_present (checked_backward_substitution [] [(Free 0,example_e)] example_companion) = false.
Proof. vm_compute; reflexivity. Qed.
Example backlinks_reject_unchecked_existential_renaming :
  example_rule_present (checked_backward_substitution [] [(Exist 0,Var (Exist 1))]
    (singleton_label [example_p example_e] [])) = false.
Proof. vm_compute; reflexivity. Qed.

Definition example_left_eq := singleton_label
  [Eq example_x zero; example_p example_x; example_q example_x] [[example_p zero]].
Example left_equality_substitutes_predicates_without_losing_positions :
  example_premise (left_equality_rule [] example_left_eq) =
    Some (singleton_label [Eq zero zero; example_p zero; example_q zero] [[example_p zero]]) /\
  example_continuations (left_equality_rule [] example_left_eq) = Some [(1,1); (2,2)].
Proof. vm_compute; auto. Qed.
Example left_equality_rejects_existential_scope_capture :
  example_rule_present (left_equality_rule []
    (singleton_label [Eq example_e example_x; example_p example_x] [[example_p example_e]])) = false.
Proof. vm_compute; reflexivity. Qed.
Example cyclic_left_equality_is_a_verified_finite_step :
  example_rule_present (left_equality_rule []
    (singleton_label [Eq example_x (successor example_x); example_p example_x] [])) = true.
Proof. vm_compute; reflexivity. Qed.

Example rhs_equality_instantiates_only_its_selected_disjunct :
  example_premise (right_equality_rule []
    (singleton_label [example_p zero] [[Eq example_e zero; example_p example_e]; [example_q zero]])) =
    Some (singleton_label [example_p zero]
      [[Eq zero zero; example_p zero]; [example_q zero]]).
Proof. vm_compute; reflexivity. Qed.
Example generic_rhs_instantiation_rejects_free_domain :
  example_rule_present (checked_rhs_instantiation [] example_left_eq [example_p zero] [(Free 0,zero)]) = false.
Proof. vm_compute; reflexivity. Qed.
Example rhs_discharge_uses_free_antecedent_truth :
  example_premise (right_discharge_rule []
    (singleton_label [example_p example_x] [[example_p example_x; example_q example_y]])) =
    Some (singleton_label [example_p example_x] [[example_q example_y]]).
Proof. vm_compute; reflexivity. Qed.
Example rhs_discharge_rejects_existential_antecedent_scope :
  example_rule_present (right_discharge_rule []
    (singleton_label [example_p example_e] [[example_p example_e]])) = false.
Proof. vm_compute; reflexivity. Qed.

Example constructor_injectivity_shifts_after_expanded_cons :
  example_premise (left_injectivity_rule []
    (singleton_label [Eq (cons example_x zero) (cons example_y zero); example_p example_x] [])) =
    Some (singleton_label [Eq example_x example_y; Eq zero zero; example_p example_x] []) /\
  example_continuations (left_injectivity_rule []
    (singleton_label [Eq (cons example_x zero) (cons example_y zero); example_p example_x] [])) =
    Some [(1,2)].
Proof. vm_compute; auto. Qed.
Example malformed_successor_injectivity_is_rejected :
  example_rule_present (left_injectivity_rule []
    (singleton_label [Eq (Fun "s" [example_x;zero]) (Fun "s" [example_y;zero])] [])) = false.
Proof. vm_compute; reflexivity. Qed.
Example arbitrary_functions_are_not_assumed_injective :
  example_rule_present (left_injectivity_rule []
    (singleton_label [Eq (Fun "f" [example_x]) (Fun "f" [example_y])] [])) = false.
Proof. vm_compute; reflexivity. Qed.
Example arbitrary_function_congruence_is_verified :
  example_premise (right_congruence_rule []
    (singleton_label [] [[Eq (Fun "f" [example_x;zero]) (Fun "f" [example_y;zero])]])) =
    Some (singleton_label [] [[Eq example_x example_y; Eq zero zero]]).
Proof. vm_compute; reflexivity. Qed.

Example right_conjunction_merges_independent_existential_witnesses :
  example_rule_present (checked_right_split []
    (singleton_label [] [[example_p (Var (Exist 0)); example_q (Var (Exist 1))]]) 1) = true.
Proof. vm_compute; reflexivity. Qed.
Example right_conjunction_rejects_a_shared_existential_witness :
  example_rule_present (checked_right_split []
    (singleton_label [] [[example_p example_e; example_q example_e]]) 1) = false.
Proof. vm_compute; reflexivity. Qed.
Example right_conjunction_allows_shared_free_variables :
  example_rule_names [] (singleton_label [] [[example_p example_x; example_q example_x]])
    (structural_rules [] (singleton_label [] [[example_p example_x; example_q example_x]])) = ["AndR"].
Proof. vm_compute; reflexivity. Qed.
Example structural_generator_avoids_a_singleton_left_self_loop :
  structural_rules [] (singleton_label [example_p zero] []) = [].
Proof. reflexivity. Qed.
Example simplification_generator_avoids_unchanged_rules :
  simplification_rules [] (singleton_label [example_p zero] [[example_q zero]]) = [].
Proof. vm_compute; reflexivity. Qed.
Example simplification_generator_returns_all_applicable_verified_families :
  example_rule_names [] example_left_eq (simplification_rules [] example_left_eq) = ["simplEq"].
Proof. vm_compute; reflexivity. Qed.

(** A semantic end-to-end use of a local certificate, not just a syntax test. *)
Example equality_substitution_proves_an_inductive_predicate_instance d :
  valid d (singleton_label [Eq example_x zero; example_p example_x] [[example_p zero]]).
Proof.
  apply (certified_local_sound d _
    (left_equality_substitution d [Eq example_x zero; example_p example_x]
      [[example_p zero]] (Free 0) zero
      (ex_intro _ (Eq example_x zero) (conj (or_introl eq_refl) eq_refl)) eq_refl)).
  intros p [Hp|Hp]; [subst p|contradiction].
  apply identity_sound; reflexivity.
Qed.

Definition example_r t := Pred 37 "R" [t].
Definition example_fold_clause := {| clause_name := "R"; head := [example_x]; body := [example_p example_x] |}.
Definition example_fact_clause := {| clause_name := "P"; head := [zero]; body := [] |}.
Definition example_fold_definitions := [example_fold_clause; example_fact_clause].
Definition example_fold_source := singleton_label
  [Pred 9 "P" [zero]; Eq example_x example_x; Pred 11 "P" [zero]; example_q zero; example_q zero]
  [[example_r zero]].
Example folding_removes_all_logical_body_copies_and_keeps_the_rhs :
  example_premise (checked_fold example_fold_definitions example_fold_source
    example_fold_clause [(Free 0,zero)] 37) =
    Some (singleton_label [example_r zero; Eq example_x example_x; example_q zero; example_q zero]
      [[example_r zero]]).
Proof. vm_compute; reflexivity. Qed.
Example folding_traces_only_distinct_unchanged_remainder_occurrences :
  example_continuations (checked_fold example_fold_definitions example_fold_source
    example_fold_clause [(Free 0,zero)] 37) = Some [(3,2); (4,3)].
Proof. vm_compute; reflexivity. Qed.
Example folding_rejects_nonmember_clauses :
  example_rule_present (checked_fold [] example_fold_source example_fold_clause [(Free 0,zero)] 37) = false.
Proof. vm_compute; reflexivity. Qed.
Example folding_rejects_a_missing_instantiated_body_atom :
  example_rule_present (checked_fold example_fold_definitions (singleton_label [example_q zero] [])
    example_fold_clause [(Free 0,zero)] 37) = false.
Proof. vm_compute; reflexivity. Qed.
Example folding_rejects_existentials_in_the_source_lhs :
  example_rule_present (checked_fold example_fold_definitions (singleton_label [example_p example_e] [])
    example_fold_clause [(Free 0,example_e)] 37) = false.
Proof. vm_compute; reflexivity. Qed.
Definition example_existential_head_clause := {| clause_name := "R"; head := [example_e]; body := [] |}.
Example folding_rejects_an_unmapped_existential_head :
  example_rule_present (checked_fold [example_existential_head_clause] (singleton_label [] [])
    example_existential_head_clause [] 37) = false.
Proof. vm_compute; reflexivity. Qed.
Definition example_existential_fold_clause :=
  {| clause_name := "R"; head := [example_e]; body := [example_p example_e] |}.
Example folding_accepts_free_instantiation_of_raw_clause_existentials :
  example_premise (checked_fold [example_existential_fold_clause]
    (singleton_label [example_p example_y] []) example_existential_fold_clause [(Exist 0,example_y)] 37) =
    Some (singleton_label [example_r example_y] []).
Proof. vm_compute; reflexivity. Qed.
Definition example_base_fold_clause := {| clause_name := "R"; head := [zero]; body := [] |}.
Example base_clause_folding_does_not_consume_source_atoms :
  example_premise (checked_fold [example_base_fold_clause] (singleton_label [example_p zero] [])
    example_base_fold_clause [] 37) = Some (singleton_label [example_r zero; example_p zero] []) /\
  example_continuations (checked_fold [example_base_fold_clause] (singleton_label [example_p zero] [])
    example_base_fold_clause [] 37) = Some [(0,1)].
Proof. vm_compute; auto. Qed.
Definition example_duplicate_body_clause :=
  {| clause_name := "R"; head := [zero]; body := [example_p zero; example_p zero] |}.
Example folding_accepts_logically_repeated_body_facts :
  example_premise (checked_fold [example_duplicate_body_clause] (singleton_label [example_p zero] [])
    example_duplicate_body_clause [] 37) = Some (singleton_label [example_r zero] []).
Proof. vm_compute; reflexivity. Qed.

Example folding_certificate_proves_a_raw_clause_instance d (Hc : In example_fold_clause d) :
  valid d (singleton_label [example_p zero] [[example_r zero]]).
Proof.
  apply (certified_local_sound d _ (fold_application d [example_p zero] [[example_r zero]]
    example_fold_clause [(Free 0,zero)] 37 [] Hc eq_refl eq_refl)).
  intros p [Hp|Hp]; [subst p|contradiction]; apply identity_sound; reflexivity.
Qed.

Definition example_scoped_companion := singleton_label [example_p example_x; example_p example_y]
  [[Eq (Var (Exist 0)) example_x; Eq (Var (Exist 1)) example_y]].
Example scoped_substitution_accepts_independent_fresh_existential_images :
  example_continuations (checked_backward_substitution_scoped []
    [(Free 0,zero); (Free 1,successor zero); (Exist 0,Var (Exist 4)); (Exist 1,Var (Exist 5))]
    example_scoped_companion) = Some [(0,0); (1,1)].
Proof. vm_compute; reflexivity. Qed.
Example scoped_substitution_accepts_an_existential_swap :
  example_rule_present (checked_backward_substitution_scoped []
    [(Exist 0,Var (Exist 1)); (Exist 1,Var (Exist 0))] example_scoped_companion) = true.
Proof. vm_compute; reflexivity. Qed.
Example scoped_substitution_rejects_collision_with_an_unmapped_existential :
  example_rule_present (checked_backward_substitution_scoped []
    [(Exist 0,Var (Exist 1))] example_scoped_companion) = false.
Proof. vm_compute; reflexivity. Qed.
Example scoped_substitution_rejects_two_mapped_existentials_colliding :
  example_rule_present (checked_backward_substitution_scoped []
    [(Exist 0,Var (Exist 2)); (Exist 1,Var (Exist 2))] example_scoped_companion) = false.
Proof. vm_compute; reflexivity. Qed.
Example scoped_substitution_collects_unmapped_existentials_in_nested_terms :
  example_rule_present (checked_backward_substitution_scoped [] [(Exist 0,Var (Exist 1))]
    (singleton_label [] [[Eq example_e zero; example_q (Fun "f" [Var (Exist 1)])]])) = false.
Proof. vm_compute; reflexivity. Qed.
Example scoped_substitution_accepts_a_fresh_rename_of_one_repeated_existential :
  example_rule_present (checked_backward_substitution_scoped [] [(Exist 0,Var (Exist 1))]
    (singleton_label [] [[Eq example_e zero; example_p example_e; example_q example_e]])) = true.
Proof. vm_compute; reflexivity. Qed.
Example scoped_substitution_rejects_free_to_existential_capture :
  example_rule_present (checked_backward_substitution_scoped [] [(Free 0,example_e)] example_companion) = false.
Proof. vm_compute; reflexivity. Qed.
Example scoped_substitution_rejects_existential_to_free_images :
  example_rule_present (checked_backward_substitution_scoped [] [(Exist 0,example_x)] example_scoped_companion) = false.
Proof. vm_compute; reflexivity. Qed.
Example scoped_substitution_rejects_nonvariable_existential_images :
  example_rule_present (checked_backward_substitution_scoped [] [(Exist 0,successor example_e)]
    example_scoped_companion) = false.
Proof. vm_compute; reflexivity. Qed.
Example scoped_backlink_prefix_connects_a_renamed_rhs_to_its_companion :
  example_prefix_present (backlink_prefix_scoped []
    (subst_sequent [(Exist 0,Var (Exist 4)); (Exist 1,Var (Exist 5))] example_scoped_companion)
    example_scoped_companion [(Exist 0,Var (Exist 4)); (Exist 1,Var (Exist 5))]) = true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions left_disjunction.
Print Assumptions backward_substitution.
Print Assumptions left_equality_substitution.
Print Assumptions guarded_right_conjunction.
Print Assumptions certified_local_sound.
Print Assumptions fold_application.
Print Assumptions checked_fold_target.
Print Assumptions scoped_witness_lookup.
Print Assumptions right_scoped_substitution.
Print Assumptions backward_substitution_scoped.
Print Assumptions backlink_prefix_scoped_sound.
