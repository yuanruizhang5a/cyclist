From Stdlib Require Import List String Arith.
From CyclistRocq.FirstOrderNew Require Import Unfolding.
From CyclistRocq.FirstOrderNew Require Import SourceDefinitions.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** Regression checks exercise position-based traces, clause universalization,
    arbitrary antecedent disjunctions, base cases, and rejected descriptors. *)
Definition unfolding_example_base := {| clause_name := "NAT";
  head := [zero]; body := [] |}.
Definition unfolding_example_step := {| clause_name := "NAT";
  head := [successor (Var (Free 0))];
  body := [Eq (Var (Exist 0)) (Var (Free 0)); Pred 88 "NAT" [Var (Exist 0)]] |}.
Definition unfolding_example_definitions := [unfolding_example_base; unfolding_example_step].
Definition unfolding_example_goal := {|
  antecedent := [[Pred 7 "NAT" [Var (Free 3)]; Pred 7 "NAT" [Var (Free 3)]];
    [Eq zero zero; Pred 9 "NAT" [Var (Free 2)]]];
  succedent := [[Pred 31 "NAT" [Var (Exist 4)]; Pred 31 "NAT" [zero]]] |}.
Definition unfolding_example_first := {| unfold_prefix := [];
  unfold_suffix := [Pred 7 "NAT" [Var (Free 3)]];
  unfold_logical_tag := 7; unfold_symbol := "NAT"; unfold_arguments := [Var (Free 3)] |}.
Definition unfolding_example_second_product := {| unfold_prefix := [Eq zero zero];
  unfold_suffix := []; unfold_logical_tag := 9; unfold_symbol := "NAT";
  unfold_arguments := [Var (Free 2)] |}.

Example unfolding_generates_all_occurrences :
  List.length (left_unfold_rules unfolding_example_definitions unfolding_example_goal) = 3 /\
  List.length (right_unfold_rules unfolding_example_definitions unfolding_example_goal) = 4.
Proof. vm_compute; auto. Qed.

Example left_cases_include_other_disjunct :
  List.length (premises (left_unfold_at_application unfolding_example_definitions
    unfolding_example_goal 0 unfolding_example_first)) = 3.
Proof. reflexivity. Qed.

Example left_shared_logical_tags_keep_distinct_occurrence_origins :
  premise_trace (left_unfold_premise unfolding_example_goal unfolding_example_first
    unfolding_example_step) = {|
      continuations := [(0,1);(0,3);(1,4)]; progressing := [(0,1)] |}.
Proof. reflexivity. Qed.

Example left_universalizes_both_variable_classes :
  left_unfold_body unfolding_example_goal unfolding_example_first unfolding_example_step =
    [Eq (Var (Free 6)) (Var (Free 5)); Pred 7 "NAT" [Var (Free 6)]].
Proof. reflexivity. Qed.

Example left_retained_copy_has_fresh_logical_tag :
  nth_error (left_unfold_product unfolding_example_goal unfolding_example_first
    unfolding_example_step) 3 = Some (Pred 10 "NAT" [Var (Free 3)]).
Proof. reflexivity. Qed.

Example left_global_offsets_are_rebased :
  premise_trace (rebase_premise (product_offset unfolding_example_goal 1)
    (left_unfold_premise unfolding_example_goal unfolding_example_second_product
      unfolding_example_step)) = {|
        continuations := [(3,1);(3,3)]; progressing := [(3,1)] |}.
Proof. reflexivity. Qed.

Example passthrough_keeps_global_origin :
  premise_trace (passthrough_premise unfolding_example_goal 1) = {|
    continuations := [(3,1)]; progressing := [] |}.
Proof. reflexivity. Qed.

Example left_base_case_has_only_copy_and_context :
  premise_trace (left_unfold_premise unfolding_example_goal unfolding_example_first
    unfolding_example_base) = {|
      continuations := [(0,1);(1,2)]; progressing := [] |}.
Proof. reflexivity. Qed.

Example undefined_selected_symbol_still_has_passthrough :
  List.length (premises (left_unfold_at_application [] unfolding_example_goal 0
    unfolding_example_first)) = 1 /\
  left_unfold_at_check [] unfolding_example_goal 0 unfolding_example_first = true.
Proof. vm_compute; auto. Qed.

Example unequal_clause_arity_is_rejected :
  left_unfold_at_check [{| clause_name := "NAT"; head := []; body := [] |}]
    unfolding_example_goal 0 unfolding_example_first = false.
Proof. reflexivity. Qed.

Example wrong_product_position_is_rejected :
  left_unfold_at_check unfolding_example_definitions unfolding_example_goal 1
    unfolding_example_first = false.
Proof. reflexivity. Qed.

Example existential_antecedent_is_rejected :
  left_unfold_rules unfolding_example_definitions
    {| antecedent := [[Pred 0 "NAT" [Var (Exist 0)]]]; succedent := [] |} = [].
Proof. reflexivity. Qed.

Example right_freshening_preserves_classes :
  right_clause 5 unfolding_example_step = {| clause_name := "NAT";
    head := [successor (Var (Free 5))];
    body := [Eq (Var (Exist 5)) (Var (Free 5)); Pred 88 "NAT" [Var (Exist 5)]] |}.
Proof. reflexivity. Qed.

Example successor_bound_is_assigned_to_copy_and_predecessor_to_children :
  let bounds := left_unfold_bounds unfolding_example_goal unfolding_example_first
    unfolding_example_step (fun k => 7+k) 6 in
  bounds 1 = 6 /\ bounds 3 = 7 /\ bounds 4 = 8.
Proof. vm_compute; auto. Qed.

(** Observe only the certified rule's premise labels, so these tests also check
    successful certification without comparing opaque evidence proof terms. *)
Definition unfolding_example_checked_labels {d j} (r : option (certified_application d j)) :=
  match r with Some r => Some (map premise_label (premises (certified_rule d j r)))
  | None => None end.

(** The actual supplied natural-number clauses and the unmodified N(x) |- N(x)
    goal.  Arbitrary instances are certified even when structural head matching
    cannot match a constructor against the goal variable: the equality stays. *)
Definition unfolding_actual_n_identity := {|
  antecedent := [[Pred 0 "N" [x]]]; succedent := [[Pred 1 "N" [x]]] |}.
Definition unfolding_actual_n_descriptor := {| unfold_prefix := []; unfold_suffix := [];
  unfold_logical_tag := 1; unfold_symbol := "N"; unfold_arguments := [x] |}.
Definition unfolding_actual_n_step := mk_clause "N" [successor x] [ip "N" [x]].

Example actual_n_identity_right_instance_keeps_nonmatching_head_equality :
  unfolding_example_checked_labels (checked_right_unfold_instance natural_definitions
    unfolding_actual_n_identity unfolding_actual_n_descriptor unfolding_actual_n_step
    [(Free 1, x)]) = Some [{|
      antecedent := [[Pred 0 "N" [x]]];
      succedent := [[Eq x (successor x); ip "N" [x]]] |}].
Proof. reflexivity. Qed.

Example actual_n_identity_right_base_instance_is_certified :
  unfolding_example_checked_labels (checked_right_unfold_instance natural_definitions
    unfolding_actual_n_identity unfolding_actual_n_descriptor (mk_clause "N" [zero] []) []) =
    Some [{| antecedent := [[Pred 0 "N" [x]]]; succedent := [[Eq x zero]] |}].
Proof. reflexivity. Qed.

(** This is the successor case of the same identity after its left-hand head
    equality is resolved.  Matching now instantiates the fresh Free 2, making
    the head equality reflexive and leaving the original child N(y). *)
Definition unfolding_actual_n_successor_identity :=
  subst_sequent [(Free 0, successor y)] unfolding_actual_n_identity.
Definition unfolding_actual_n_successor_descriptor := {| unfold_prefix := []; unfold_suffix := [];
  unfold_logical_tag := 1; unfold_symbol := "N"; unfold_arguments := [successor y] |}.

Example actual_n_successor_right_match_instantiates_fresh_head :
  right_unfold_matched_substitution 5 unfolding_actual_n_successor_identity
    unfolding_actual_n_successor_descriptor unfolding_actual_n_step = Some [(Free 2, y)].
Proof. reflexivity. Qed.

Example actual_n_successor_right_match_is_certified :
  unfolding_example_checked_labels (checked_right_unfold_matched 5 natural_definitions
    unfolding_actual_n_successor_identity unfolding_actual_n_successor_descriptor
    unfolding_actual_n_step) = Some [{|
      antecedent := [[Pred 0 "N" [successor y]]];
      succedent := [[Eq (successor y) (successor y); ip "N" [y]]] |}].
Proof. reflexivity. Qed.

Example actual_n_matched_enumeration_follows_constructor_cases :
  List.length (right_unfold_matched_rules 5 natural_definitions
    unfolding_actual_n_successor_identity) = 1 /\
  List.length (right_unfold_matched_rules 5 natural_definitions
    (subst_sequent [(Free 0, zero)] unfolding_actual_n_identity)) = 1.
Proof. vm_compute; auto. Qed.

(** A modified definition exposes a different variable in the head and keeps
    its defining equality in the body.  Matching instantiates the exposed head
    variable; a caller-supplied instance can instantiate the body variable too. *)
Definition unfolding_example_modifieddef := mk_clause "N" [successor y]
  [Eq (successor x) (successor y); ip "N" [x]].
Definition unfolding_example_modified_definitions :=
  [mk_clause "N" [zero] []; unfolding_example_modifieddef].

Example modifieddef_right_match_preserves_body_guard :
  unfolding_example_checked_labels (checked_right_unfold_matched 5
    unfolding_example_modified_definitions unfolding_actual_n_successor_identity
    unfolding_actual_n_successor_descriptor unfolding_example_modifieddef) = Some [{|
      antecedent := [[Pred 0 "N" [successor y]]];
      succedent := [[Eq (successor y) (successor y);
        Eq (successor (Var (Free 2))) (successor y); ip "N" [Var (Free 2)]]] |}].
Proof. reflexivity. Qed.

Example modifieddef_right_instance_instantiates_head_and_body :
  unfolding_example_checked_labels (checked_right_unfold_instance
    unfolding_example_modified_definitions unfolding_actual_n_successor_identity
    unfolding_actual_n_successor_descriptor unfolding_example_modifieddef
    [(Free 3, y); (Free 2, y)]) = Some [{|
      antecedent := [[Pred 0 "N" [successor y]]];
      succedent := [[Eq (successor y) (successor y);
        Eq (successor y) (successor y); ip "N" [y]]] |}].
Proof. reflexivity. Qed.

(** Repeated heads may return a substitution even for unequal occurrences.
    Rebuilding every head equality prevents dropping that essential constraint. *)
Definition unfolding_example_repeated_head := mk_clause "REPEAT" [x; x] [ip "N" [x]].
Definition unfolding_example_repeated_goal := {|
  antecedent := [[ip "N" [zero]]]; succedent := [[Pred 2 "REPEAT" [zero; successor zero]]] |}.
Definition unfolding_example_repeated_descriptor := {| unfold_prefix := []; unfold_suffix := [];
  unfold_logical_tag := 2; unfold_symbol := "REPEAT"; unfold_arguments := [zero; successor zero] |}.

Example repeated_head_right_match_preserves_all_head_equalities :
  unfolding_example_checked_labels (checked_right_unfold_matched 5
    (unfolding_example_repeated_head :: natural_definitions) unfolding_example_repeated_goal
    unfolding_example_repeated_descriptor unfolding_example_repeated_head) = Some [{|
      antecedent := [[ip "N" [zero]]];
      succedent := [[Eq zero zero; Eq (successor zero) zero; ip "N" [zero]]] |}].
Proof. reflexivity. Qed.

Example arbitrary_simultaneous_instance_can_differ_from_matcher :
  unfolding_example_checked_labels (checked_right_unfold_instance
    (unfolding_example_repeated_head :: natural_definitions) unfolding_example_repeated_goal
    unfolding_example_repeated_descriptor unfolding_example_repeated_head
    [(Free 1, successor zero); (Free 1, zero); (Free 8, Var (Exist 4))]) = Some [{|
      antecedent := [[ip "N" [zero]]];
      succedent := [[Eq zero (successor zero); Eq (successor zero) (successor zero);
        ip "N" [successor zero]]] |}].
Proof. reflexivity. Qed.

Example right_instance_keeps_antecedent_trace_identical :
  map premise_trace (premises (right_unfold_instance_application unfolding_actual_n_identity
    unfolding_actual_n_descriptor unfolding_actual_n_step [(Free 1, x)])) =
    [{| continuations := [(0,0)]; progressing := [] |}].
Proof. reflexivity. Qed.

Example insufficient_matching_fuel_produces_no_rules :
  right_unfold_matched_rules 0 natural_definitions unfolding_actual_n_successor_identity = [].
Proof. reflexivity. Qed.

Example head_matching_does_not_bypass_clause_membership_check :
  checked_right_unfold_matched 5 natural_definitions unfolding_actual_n_successor_identity
    unfolding_actual_n_successor_descriptor unfolding_example_modifieddef = None.
Proof. reflexivity. Qed.

Example head_matching_does_not_bypass_descriptor_check :
  checked_right_unfold_matched 5 natural_definitions unfolding_actual_n_identity
    unfolding_actual_n_successor_descriptor unfolding_actual_n_step = None.
Proof. reflexivity. Qed.
