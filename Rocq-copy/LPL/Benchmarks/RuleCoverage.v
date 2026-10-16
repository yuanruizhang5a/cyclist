From Stdlib Require Import List Bool Arith ZArith String.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Open Scope list_scope.
Fixpoint judgments_eqb a b := match a,b with
  | [],[] => true | x::xs,y::ys => judgment_eqb x y && judgments_eqb xs ys | _,_ => false end.
Definition has_shape j req expected := match generate_requested j req with
  | Some r => judgments_eqb (map Cyclic.premise_judgment r.(Cyclic.rule_premises)) expected
  | None => false end.
Definition a := nonnegative.
Definition b := iszero.
Definition p := Assign 0 one.
Definition q := Assign 1 x.
Definition u := u0.
Definition sigma := TraceLabel 0.
Definition joined := Join sigma (StateLabel u).
Definition after := Join joined (StateLabel (AssignUpdate 0 one u)).
Definition stutter := Join joined (StateLabel u).
Definition guard_label := Join (StateLabel u) (StateLabel u).
Definition gamma := [assertion l1 (First Truth)].
Definition delta := [assertion l1 Falsity].
Definition lhs f := Jdg (gamma ++ [f]) delta.
Definition rhs f := Jdg gamma (delta ++ [f]).
Example b_assign_l : has_shape (lhs (assertion joined (Box p a))) (Local OnLeft 1 "B.Assign.L") ([Jdg (gamma ++ [assertion after a]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_seq_l : has_shape (lhs (assertion sigma (Box (Seq p q) a))) (Local OnLeft 1 "B.Seq.L") ([Jdg (gamma ++ [assertion sigma (Box p (Box q a))]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_choice_l : has_shape (lhs (assertion sigma (Box (Choice p q) a))) (Local OnLeft 1 "B.Choice.L") ([Jdg (gamma ++ [assertion sigma (Box p a)]) delta;Jdg (gamma ++ [assertion sigma (Box q a)]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_star_l : has_shape (lhs (assertion sigma (Box (Star p) a))) (Local OnLeft 1 "B.Star.L") ([Jdg (gamma ++ [assertion sigma (Box (Test Truth) a)]) delta;Jdg (gamma ++ [assertion sigma (Box p (Box (Star p) a))]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_assign_l : has_shape (lhs (assertion joined (Diamond p a))) (Local OnLeft 1 "D.Assign.L") ([Jdg (gamma ++ [assertion after a]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_seq_l : has_shape (lhs (assertion sigma (Diamond (Seq p q) a))) (Local OnLeft 1 "D.Seq.L") ([Jdg (gamma ++ [assertion sigma (Diamond p (Diamond q a))]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_choice_l : has_shape (lhs (assertion sigma (Diamond (Choice p q) a))) (Local OnLeft 1 "D.Choice.L") ([Jdg (gamma ++ [assertion sigma (Diamond p a)]) delta;Jdg (gamma ++ [assertion sigma (Diamond q a)]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_star_l : has_shape (lhs (assertion sigma (Diamond (Star p) a))) (Local OnLeft 1 "D.Star.L") ([Jdg (gamma ++ [assertion sigma (Diamond (Test Truth) a)]) delta;Jdg (gamma ++ [assertion sigma (Diamond p (Diamond (Star p) a))]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example at_l : has_shape (lhs (assertion (Join (StateLabel u) sigma) a)) (Local OnLeft 1 "At.L") ([Jdg (gamma ++ [assertion (StateLabel u) a]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example first_l : has_shape (lhs (assertion (Join (StateLabel u) sigma) (First (Conj a b)))) (Local OnLeft 1 "First.L") ([Jdg (gamma ++ [assertion (StateLabel u) (Conj a b)]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example and_l : has_shape (lhs (assertion sigma (Conj a b))) (Local OnLeft 1 "And.L") ([Jdg (gamma ++ [assertion sigma a;assertion sigma b]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example or_l : has_shape (lhs (assertion sigma (Disj a b))) (Local OnLeft 1 "Or.L") ([Jdg (gamma ++ [assertion sigma a]) delta;Jdg (gamma ++ [assertion sigma b]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example suffix_l : has_shape (lhs (assertion (Join (StateLabel u) sigma) (Suffix a b))) (Local OnLeft 1 "Suffix.L") ([Jdg (gamma ++ [assertion sigma b]) delta;Jdg (gamma ++ [assertion sigma a;assertion sigma (Suffix a b)]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example dualsuffix_l : has_shape (lhs (assertion (Join (StateLabel u) sigma) (DualSuffix a b))) (Local OnLeft 1 "DualSuffix.L") ([Jdg (gamma ++ [assertion sigma b;assertion sigma a]) delta;Jdg (gamma ++ [assertion sigma b;assertion sigma (DualSuffix a b)]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_assign_r : has_shape (rhs (assertion joined (Box p a))) (Local OnRight 1 "B.Assign.R") ([Jdg gamma (delta ++ [assertion after a])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_seq_r : has_shape (rhs (assertion sigma (Box (Seq p q) a))) (Local OnRight 1 "B.Seq.R") ([Jdg gamma (delta ++ [assertion sigma (Box p (Box q a))])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_choice_r : has_shape (rhs (assertion sigma (Box (Choice p q) a))) (Local OnRight 1 "B.Choice.R") ([Jdg gamma (delta ++ [assertion sigma (Box p a)]);Jdg gamma (delta ++ [assertion sigma (Box q a)])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_star_r : has_shape (rhs (assertion sigma (Box (Star p) a))) (Local OnRight 1 "B.Star.R") ([Jdg gamma (delta ++ [assertion sigma (Box (Test Truth) a)]);Jdg gamma (delta ++ [assertion sigma (Box p (Box (Star p) a))])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_assign_r : has_shape (rhs (assertion joined (Diamond p a))) (Local OnRight 1 "D.Assign.R") ([Jdg gamma (delta ++ [assertion after a])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_seq_r : has_shape (rhs (assertion sigma (Diamond (Seq p q) a))) (Local OnRight 1 "D.Seq.R") ([Jdg gamma (delta ++ [assertion sigma (Diamond p (Diamond q a))])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_choice_r : has_shape (rhs (assertion sigma (Diamond (Choice p q) a))) (Local OnRight 1 "D.Choice.R") ([Jdg gamma (delta ++ [assertion sigma (Diamond p a);assertion sigma (Diamond q a)])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_star_r : has_shape (rhs (assertion sigma (Diamond (Star p) a))) (Local OnRight 1 "D.Star.R") ([Jdg gamma (delta ++ [assertion sigma (Diamond (Test Truth) a);assertion sigma (Diamond p (Diamond (Star p) a))])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example at_r : has_shape (rhs (assertion (Join (StateLabel u) sigma) a)) (Local OnRight 1 "At.R") ([Jdg gamma (delta ++ [assertion (StateLabel u) a])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example first_r : has_shape (rhs (assertion (Join (StateLabel u) sigma) (First (Conj a b)))) (Local OnRight 1 "First.R") ([Jdg gamma (delta ++ [assertion (StateLabel u) (Conj a b)])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example and_r : has_shape (rhs (assertion sigma (Conj a b))) (Local OnRight 1 "And.R") ([Jdg gamma (delta ++ [assertion sigma a]);Jdg gamma (delta ++ [assertion sigma b])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example or_r : has_shape (rhs (assertion sigma (Disj a b))) (Local OnRight 1 "Or.R") ([Jdg gamma (delta ++ [assertion sigma a;assertion sigma b])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example suffix_r : has_shape (rhs (assertion (Join (StateLabel u) sigma) (Suffix a b))) (Local OnRight 1 "Suffix.R") ([Jdg gamma (delta ++ [assertion sigma b;assertion sigma a]);Jdg gamma (delta ++ [assertion sigma b;assertion sigma (Suffix a b)])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example dualsuffix_r : has_shape (rhs (assertion (Join (StateLabel u) sigma) (DualSuffix a b))) (Local OnRight 1 "DualSuffix.R") ([Jdg gamma (delta ++ [assertion sigma b]);Jdg gamma (delta ++ [assertion sigma a;assertion sigma (DualSuffix a b)])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_test_r : has_shape (rhs (assertion joined (Box (Test b) a))) (Local OnRight 1 "B.Test.R") ([Jdg (gamma ++ [assertion guard_label b]) (delta ++ [assertion stutter a])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_test_l : has_shape (Jdg (gamma ++ [assertion joined (Box (Test b) a);assertion guard_label b]) delta) (Local OnLeft 1 "B.Test.L") ([Jdg (gamma ++ [assertion stutter a]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_test_r : has_shape (Jdg (gamma ++ [assertion guard_label b]) (delta ++ [assertion joined (Diamond (Test b) a)])) (Local OnRight 1 "D.Test.R") ([Jdg gamma (delta ++ [assertion stutter a])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example d_test_l : has_shape (lhs (assertion joined (Diamond (Test b) a))) (Local OnLeft 1 "D.Test.L") ([Jdg (gamma ++ [assertion stutter a;assertion guard_label b]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example not_r : has_shape (rhs (assertion sigma (Neg a))) (Local OnRight 1 "Not.R") ([Jdg (gamma ++ [assertion sigma a]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example not_l : has_shape (lhs (assertion sigma (Neg a))) (Local OnLeft 1 "Not.L") ([Jdg gamma (assertion sigma a :: delta)]) = true.
Proof. vm_compute; reflexivity. Qed.
Example impl_r : has_shape (rhs (assertion sigma (Impl a b))) (Local OnRight 1 "Impl.R") ([Jdg (gamma ++ [assertion sigma a]) (delta ++ [assertion sigma b])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example impl_l : has_shape (lhs (assertion sigma (Impl a b))) (Local OnLeft 1 "Impl.L") ([Jdg gamma (assertion sigma a :: delta);Jdg (gamma ++ [assertion sigma b]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example weakening_onleft : has_shape (lhs (assertion sigma (First a))) (Weaken OnLeft 1) ([Jdg gamma delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example weakening_onright : has_shape (rhs (assertion sigma (First a))) (Weaken OnRight 1) ([Jdg gamma delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example all_onleft : has_shape (lhs (assertion sigma (All 0 (Equal x zero)))) (Instantiate OnLeft 1 one) ([Jdg (gamma ++ [assertion sigma (subst_fo 0 (one) (Equal x zero))]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example ex_onright : has_shape (rhs (assertion sigma (Ex 0 (Equal x zero)))) (Instantiate OnRight 1 one) ([Jdg gamma (delta ++ [assertion sigma (subst_fo 0 (one) (Equal x zero))])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example all_onright : has_shape (rhs (assertion sigma (All 0 (Equal x zero)))) (Eigen OnRight 1 5) ([Jdg gamma (delta ++ [assertion sigma (subst_fo 0 (Var 5) (Equal x zero))])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example ex_onleft : has_shape (lhs (assertion sigma (Ex 0 (Equal x zero)))) (Eigen OnLeft 1 5) ([Jdg (gamma ++ [assertion sigma (subst_fo 0 (Var 5) (Equal x zero))]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Definition world_sub_original := Jdg [assertion l0 a] [assertion sigma (Box p a)].
Example world_sub : has_shape (map_labels (subst_world_label 0 (AssignUpdate 0 one u0)) world_sub_original) (SubstituteWorld world_sub_original 0 (AssignUpdate 0 one u0)) ([world_sub_original]) = true.
Proof. vm_compute; reflexivity. Qed.
Definition trace_sub_original := Jdg [assertion l0 a] [assertion sigma (Box p a)].
Example trace_sub : has_shape (map_labels (subst_trace_label 0 (Join l0 l1)) trace_sub_original) (SubstituteTrace trace_sub_original 0 (Join l0 l1)) ([trace_sub_original]) = true.
Proof. vm_compute; reflexivity. Qed.
Example cut_two_contexts : has_shape (Jdg (gamma ++ [assertion l0 a]) (delta ++ [assertion l1 b])) (Cut gamma [assertion l0 a] delta [assertion l1 b] (assertion sigma Truth)) ([Jdg gamma (assertion sigma Truth :: delta);Jdg [assertion l0 a;assertion sigma Truth] [assertion l1 b]]) = true.
Proof. vm_compute; reflexivity. Qed.
Example exchange_onleft : has_shape (Jdg [assertion l0 a;assertion l1 b] delta) (ExchangeAdjacent OnLeft 0) ([Jdg [assertion l1 b;assertion l0 a] delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example exchange_onright : has_shape (Jdg gamma [assertion l0 a;assertion l1 b]) (ExchangeAdjacent OnRight 0) ([Jdg gamma [assertion l1 b;assertion l0 a]]) = true.
Proof. vm_compute; reflexivity. Qed.
Definition tagged_goal := Jdg [] [traced sigma (Box p a) 0].
Definition retagged_goal := Jdg [] [traced sigma (Box p a) 7].
Example exact_backlink : has_shape (tagged_goal) (BacklinkExact tagged_goal) ([tagged_goal]) = true.
Proof. vm_compute; reflexivity. Qed.
Example tag_backlink : has_shape (tagged_goal) (BacklinkTags [(0,7)] retagged_goal) ([retagged_goal]) = true.
Proof. vm_compute; reflexivity. Qed.
Example reject_empty_complete : someb (generate_axiom (Jdg [] [assertion Empty Truth])) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_malformed_arity : judgment_wfb (Jdg [] [assertion l0 (Pred 0 [])]) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_modal_body : formula_wfb (All 0 (Box p a)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_nested_modal_body : formula_wfb (Ex 0 (Conj a (All 1 (Box p b)))) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_temporal_body : formula_wfb (All 0 (Next a)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_duplicate_tags : judgment_wfb (Jdg [] [traced sigma (Box p a) 0;traced sigma (Box q a) 0]) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_tag_on_left : judgment_wfb (Jdg [traced sigma (Box p a) 0] []) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_tag_on_atom : judgment_wfb (Jdg [] [traced l0 a 0]) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_empty_substitution : someb (generate_requested tagged_goal (SubstituteTrace tagged_goal 0 Empty)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_wrong_position : someb (generate_requested tagged_goal (Weaken OnRight 3)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_wrong_shape : someb (generate_requested tagged_goal (Instantiate OnRight 0 one)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_wrong_name : someb (generate_requested tagged_goal (Local OnRight 0 "Wk.R")) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_bad_backlink : someb (generate_requested tagged_goal (BacklinkExact retagged_goal)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_bad_tag_companion : someb (generate_requested tagged_goal (BacklinkTags [(0,8)] retagged_goal)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_missing_test_guard : someb (generate_requested (rhs (assertion joined (Diamond (Test b) a))) (Local OnRight 1 "D.Test.R")) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_wrong_test_guard : someb (generate_requested (Jdg (gamma ++ [assertion guard_label a]) (delta ++ [assertion joined (Diamond (Test b) a)])) (Local OnRight 1 "D.Test.R")) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_label_eigenvariable : someb (generate_requested (Jdg [] [assertion (StateLabel (AssignUpdate 1 zero u0)) (All 0 (Equal x zero))]) (Eigen OnRight 0 1)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_context_eigenvariable : someb (generate_requested (Jdg [assertion l0 (Equal y zero)] [assertion l0 (All 0 (Equal x zero))]) (Eigen OnRight 0 1)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_body_eigenvariable : someb (generate_requested (Jdg [] [assertion l0 (All 0 (Equal x y))]) (Eigen OnRight 0 1)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reject_bad_term_request : someb (generate_requested (Jdg [] [assertion l0 (Ex 0 Truth)]) (Instantiate OnRight 0 (Fun 2 []))) = false.
Proof. vm_compute; reflexivity. Qed.
Example outside_modal_quantifier_accepted : formula_wfb (Box p (All 0 (Impl a (Ex 1 b)))) = true.
Proof. reflexivity. Qed.
Example outside_temporal_quantifier_accepted : formula_wfb (Next (All 0 a)) = true.
Proof. reflexivity. Qed.
Example pure_boundary_stops : List.length (generate_rules (Jdg [] [assertion l0 (All 0 (Equal x x))])) = 0.
Proof. vm_compute; reflexivity. Qed.
Example empty_context_is_not_axiom : someb (generate_axiom (Jdg [] [])) = false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions universal_right.
Print Assumptions suffix_right.

Print Assumptions box_choice_right.
Print Assumptions trace_substitution_rule.
Print Assumptions tag_renaming_backlink.
Print Assumptions raw_check_sound.

Example finite_scan_finds_non_head_rule :
  existsb (fun r => String.eqb r.(Cyclic.rule_name) "B.Choice.R")
    (generate_rules (rhs (assertion sigma (Box (Choice p q) a)))) = true.
Proof. vm_compute; reflexivity. Qed.
Definition bare_weakening_goal := Jdg [] [assertion l0 Falsity].
Definition bare_weakening := requested bare_weakening_goal (Weaken OnRight 0) ltac:(vm_compute; reflexivity).
Example weakening_keeps_empty_context_premise :
  has_shape bare_weakening_goal (Weaken OnRight 0) [Jdg [] []] = true.
Proof. vm_compute; reflexivity. Qed.
Example context_only_premise_stays_open : someb (generate_axiom (premise_at bare_weakening 0)) = false.
Proof. vm_compute; reflexivity. Qed.
