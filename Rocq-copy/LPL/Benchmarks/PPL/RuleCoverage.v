(** * Executable examples of every public rule/request family

    Compare these expected ordered premise lists with RULE_EXPANSIONS.md.
    Each example computes a fixed request and checks its exact shape; semantic
    soundness comes from the kernel record the generator returned. Most
    principals are at position 1, after a nonempty surrounding context, to
    demonstrate that generation is not limited to the head of a sequent.

    The second part gives rejected requests and syntax, followed by assumption
    audits and explicit finite-scan/weakening regressions. These computations
    check the generator interface; they do not establish proof-search
    completeness or decide whether rejected goals are false. *)
From Stdlib Require Import List Bool Arith String.
From CyclistRocq.LPL.Benchmarks.PPL Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Open Scope list_scope.
Fixpoint judgments_eqb a b := match a,b with
  | [],[] => true | x::xs,y::ys => judgment_eqb x y && judgments_eqb xs ys | _,_ => false end.
(** Ignore proof fields when checking premise shape; retain full judgment
    syntax, including context order, labels and tags. A failed request also
    makes the shape check false, so an empty expected list cannot hide it. *)
Definition has_shape j req expected := match generate_requested j req with
  | Some r => judgments_eqb (map Cyclic.premise_judgment r.(Cyclic.rule_premises)) expected
  | None => false end.
Definition a := safe.
Definition b := atom IsIdle.
Definition p := act Acquire.
Definition q := act Release.
Definition u := 0.
Definition sigma := TraceLabel 0.
Definition joined := Join sigma (StateLabel u).
Definition stutter := Join joined (StateLabel u).
Definition guard_label := Join (StateLabel u) (StateLabel u).
Definition gamma := [assertion l1 (First Truth)].
Definition delta := [assertion l1 Falsity].
Definition lhs f := Jdg (gamma ++ [f]) delta.
Definition rhs f := Jdg gamma (delta ++ [f]).
(** Left schemes: atomic actions expose a successor world, sequence nests its
    modalities, and choice/star retain the catalog's two separate premises.
    Boolean and temporal schemes below preserve the same context split. *)
Example b_seq_l : has_shape (lhs (assertion sigma (Box (Seq p q) a))) (Local OnLeft 1 "B.Seq.L") ([Jdg (gamma ++ [assertion sigma (Box p (Box q a))]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_choice_l : has_shape (lhs (assertion sigma (Box (Choice p q) a))) (Local OnLeft 1 "B.Choice.L") ([Jdg (gamma ++ [assertion sigma (Box p a)]) delta;Jdg (gamma ++ [assertion sigma (Box q a)]) delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_star_l : has_shape (lhs (assertion sigma (Box (Star p) a))) (Local OnLeft 1 "B.Star.L") ([Jdg (gamma ++ [assertion sigma (Box (Test Truth) a)]) delta;Jdg (gamma ++ [assertion sigma (Box p (Box (Star p) a))]) delta]) = true.
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
(** Right schemes: conjunction/box-choice branch into premises, whereas
    disjunction/diamond-choice put both alternatives in one succedent. The
    literal label trees also check retention of action/test states. *)
Example b_seq_r : has_shape (rhs (assertion sigma (Box (Seq p q) a))) (Local OnRight 1 "B.Seq.R") ([Jdg gamma (delta ++ [assertion sigma (Box p (Box q a))])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_choice_r : has_shape (rhs (assertion sigma (Box (Choice p q) a))) (Local OnRight 1 "B.Choice.R") ([Jdg gamma (delta ++ [assertion sigma (Box p a)]);Jdg gamma (delta ++ [assertion sigma (Box q a)])]) = true.
Proof. vm_compute; reflexivity. Qed.
Example b_star_r : has_shape (rhs (assertion sigma (Box (Star p) a))) (Local OnRight 1 "B.Star.R") ([Jdg gamma (delta ++ [assertion sigma (Box (Test Truth) a)]);Jdg gamma (delta ++ [assertion sigma (Box p (Box (Star p) a))])]) = true.
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
(** Test rules have explicit guard occurrences at the stutter label. Some
    schemes require that guard in the input context; later negative examples
    check that a missing or different guard cannot be consumed accidentally. *)
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
(** Parameterized requests explicitly choose weakening positions, quantifier
    terms/eigenvariables, sorted substitutions, cut contexts, permutations and
    companion tag mappings. These are caller inputs rather than guessed data. *)
Example weakening_onleft : has_shape (lhs (assertion sigma (First a))) (Weaken OnLeft 1) ([Jdg gamma delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Example weakening_onright : has_shape (rhs (assertion sigma (First a))) (Weaken OnRight 1) ([Jdg gamma delta]) = true.
Proof. vm_compute; reflexivity. Qed.
Definition world_sub_original := Jdg [assertion l0 a] [assertion sigma (Box p a)].
Example world_sub : has_shape (map_labels (subst_world_label 0 2) world_sub_original) (SubstituteWorld world_sub_original 0 2) ([world_sub_original]) = true.
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
(** Rejected syntax cannot obtain a generated rule merely because its outer
    constructor matches. In particular purity is recursive, tags belong only
    to traceable succedents, and eigenvariable freshness includes update
    targets in labels. A malformed instantiating term is rejected even when
    the bound variable is unused in the body. *)
Example reject_empty_complete : someb (generate_axiom (Jdg [] [assertion Empty Truth])) = false.
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
Example empty_context_is_not_axiom : someb (generate_axiom (Jdg [] [])) = false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions box_atomic_right.
Print Assumptions suffix_right.

Print Assumptions box_choice_right.
Print Assumptions trace_substitution_rule.
Print Assumptions tag_renaming_backlink.
Print Assumptions raw_check_sound.

(** Finally exercise the public finite scan, not only selected requests, and
    isolate the empty-context weakening case. Removing the only succedent
    still leaves one open premise [Jdg [] []]; it never becomes an axiom. *)
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

(** Relational action schemas at non-head positions, with unrelated relations
    on both sides of the selected transition. *)
Definition rp := [CustomRelation SameState [l1;l1]].
Definition rq := [action_relation Stutter 1 2].
Definition edge := action_relation Acquire u 1.
Definition full_relations := rp ++ edge :: rq.
Example atomic_box_left_shape :
  has_shape (Rdg full_relations (gamma ++ [assertion joined (Box p a)]) delta) (AtomicUse OnLeft 1 1)
    [Rdg (rp ++ rq) (gamma ++ [assertion (action_label sigma u 1) a]) delta] = true.
Proof. vm_compute; reflexivity. Qed.
Example atomic_diamond_right_shape :
  has_shape (Rdg full_relations gamma (delta ++ [assertion joined (Diamond p a)])) (AtomicUse OnRight 1 1)
    [Rdg (rp ++ rq) gamma (delta ++ [assertion (action_label sigma u 1) a])] = true.
Proof. vm_compute; reflexivity. Qed.
Example atomic_box_right_shape :
  has_shape (Rdg (rp ++ rq) gamma (delta ++ [assertion joined (Box p a)])) (AtomicEigen OnRight 1 3)
    [Rdg ((rp ++ rq) ++ [action_relation Acquire u 3]) gamma (delta ++ [assertion (action_label sigma u 3) a])] = true.
Proof. vm_compute; reflexivity. Qed.
Example atomic_diamond_left_shape :
  has_shape (Rdg (rp ++ rq) (gamma ++ [assertion joined (Diamond p a)]) delta) (AtomicEigen OnLeft 1 3)
    [Rdg ((rp ++ rq) ++ [action_relation Acquire u 3]) (gamma ++ [assertion (action_label sigma u 3) a]) delta] = true.
Proof. vm_compute; reflexivity. Qed.
Example relation_weakening_shape : has_shape (Rdg full_relations gamma delta) (WeakenRelation 1)
  [Rdg (rp ++ rq) gamma delta] = true.
Proof. vm_compute; reflexivity. Qed.
Example relation_contraction_shape : has_shape (Rdg full_relations gamma delta) (ContractRelation 1)
  [Rdg (rp ++ edge :: edge :: rq) gamma delta] = true.
Proof. vm_compute; reflexivity. Qed.
Example relation_exchange_shape : has_shape (Rdg full_relations gamma delta) (ExchangeRelation 0)
  [Rdg (edge :: rp ++ rq) gamma delta] = true.
Proof. vm_compute; reflexivity. Qed.
Example common_rule_retains_relations : has_shape
  (Rdg full_relations gamma (delta ++ [assertion sigma (Conj a b)])) (Local OnRight 1 "And.R")
  [Rdg full_relations gamma (delta ++ [assertion sigma a]);Rdg full_relations gamma (delta ++ [assertion sigma b])] = true.
Proof. vm_compute; reflexivity. Qed.
Definition algebra_original := Rdg [edge] gamma [assertion (Join l0 (Join l1 l0)) a].
Example label_association_shape : has_shape (map_labels (rotate_label [] true) algebra_original)
  (RotateLabels algebra_original [] true) [algebra_original] = true.
Proof. vm_compute; reflexivity. Qed.
Example label_unit_shape : has_shape (map_labels (unit_label [] true true) algebra_original)
  (UnitLabels algebra_original [] true true) [algebra_original] = true.
Proof. vm_compute; reflexivity. Qed.
Example propositional_scan_remains_enabled : existsb (fun r => String.eqb r.(Cyclic.rule_name) "And.R")
  (generate_rules (Jdg [] [assertion l0 (Conj a b)])) = true.
Proof. vm_compute; reflexivity. Qed.
Example relation_index_checked : someb (generate_requested (Rdg full_relations gamma delta) (WeakenRelation 99)) = false.
Proof. vm_compute; reflexivity. Qed.
Example malformed_relation_cannot_close : someb (generate_axiom (Rdg [CustomRelation SameState [l0]] [] [assertion l0 Truth])) = false.
Proof. vm_compute; reflexivity. Qed.
Example backlink_companion_relations_must_agree :
  someb (generate_requested (Rdg [edge] [] [traced sigma (Box p a) 0]) (BacklinkExact tagged_goal)) = false.
Proof. vm_compute; reflexivity. Qed.

Example cut_splits_relational_contexts : has_shape
  (Rdg (rp ++ rq) (gamma ++ [assertion l0 a]) (delta ++ [assertion l1 b]))
  (CutRelations rp rq gamma [assertion l0 a] delta [assertion l1 b] (assertion sigma Truth))
  [Rdg rp gamma (assertion sigma Truth :: delta);Rdg rq [assertion l0 a;assertion sigma Truth] [assertion l1 b]] = true.
Proof. vm_compute; reflexivity. Qed.
