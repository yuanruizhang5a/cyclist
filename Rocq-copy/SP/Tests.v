From Stdlib Require Import List String.

From CyclistRocq.SP Require Import
  Syntax Semantics Rules Automation RuleGeneration Definitions Benchmarks.

Import ListNotations.
Open Scope string_scope.

(** * Executable generator regression tests *)

Definition test_identity_goal : judgment :=
  mk_judgment []
    (mk_sequent (singleton_formula emp) (singleton_formula emp)).

Example identity_generator_positive :
  match exact_identity_candidate test_identity_goal with
  | Some _ => true | None => false
  end = true.
Proof. reflexivity. Qed.

Definition test_inconsistent_goal : judgment :=
  mk_judgment []
    (mk_sequent
      (singleton_formula (mk_heap [Disequal Nil Nil] [] [])) false_formula).

Example inconsistency_generator_positive :
  match inconsistency_candidate test_inconsistent_goal with
  | Some _ => true | None => false
  end = true.
Proof. reflexivity. Qed.

Definition test_tagged_formula : formula :=
  singleton_formula
    (mk_heap [] [] [tagged_pred 4 "P" [Var (free_var 0)]]).

Definition test_tag_erasure_goal : judgment :=
  mk_judgment []
    (mk_sequent test_tagged_formula (erase_formula_tags test_tagged_formula)).

Example tag_erasure_generator_positive :
  match tag_erasure_candidate test_tag_erasure_goal with
  | Some _ => true | None => false
  end = true.
Proof. reflexivity. Qed.

Example predicate_intro_generator_positive :
  match predicate_intro_candidate benchmark_base_19_1 with
  | Some _ => true | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example predicate_intro_rejects_unmatched_goal :
  predicate_intro_candidate benchmark_base_01_1 = None.
Proof. vm_compute. reflexivity. Qed.

Example left_split_generator_positive :
  match left_disjunction_candidate benchmark_base_21_1 with
  | Some _ => true | None => false
  end = true.
Proof. reflexivity. Qed.

Definition test_right_disjunction_goal : judgment :=
  mk_judgment []
    (mk_sequent (singleton_formula emp)
      (mk_formula [] [emp; mk_heap [Equal Nil Nil] [] []])).

Example right_split_generator_positive :
  match right_disjunction_candidate test_right_disjunction_goal with
  | Some _ => true | None => false
  end = true.
Proof. reflexivity. Qed.

Example right_split_rejects_singleton :
  right_disjunction_candidate test_identity_goal = None.
Proof. reflexivity. Qed.

Example normalization_unit h : normalize_heap (normalize_heap h) = h.
Proof. reflexivity. Qed.

Example points_to_ownership_unit rho p h :
  points_to_holds rho p h -> List.length h = 1.
Proof. apply points_to_owns_exactly_one. Qed.
