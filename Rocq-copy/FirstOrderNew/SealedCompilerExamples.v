From Stdlib Require Import List Bool Arith String.
From CyclistRocq.FirstOrderNew Require Import SealedCompiler Adapter.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Definition sealed_example_x := Var (Free 5).
Definition sealed_example_base := {| clause_name := "N"; head := [zero]; body := [] |}.
Definition sealed_example_step := {| clause_name := "N"; head := [successor (Var (Free 0))];
  body := [Pred 0 "N" [Var (Free 0)]] |}.
Definition sealed_example_pack := {| clause_name := "PACK"; head := [successor (Var (Free 0))];
  body := [Pred 0 "N" [Var (Free 0)]] |}.
Definition sealed_example_definitions := [sealed_example_base; sealed_example_step; sealed_example_pack].
Definition sealed_example_label p g := {| antecedent := [p]; succedent := g |}.
Definition sealed_example_present d j rd :=
  match sealed_compile_rule_descriptor d j rd with Some _ => true | None => false end.
Definition sealed_example_matches d j rd labels :=
  match sealed_compile_rule_descriptor d j rd with
  | Some c => application_matches (propose rd j labels) (certified_rule d j c)
  | None => false end.
Definition sealed_example_application d j rd :=
  option_map (certified_rule d j) (sealed_compile_rule_descriptor d j rd).

Example sealed_identity_has_exact_conclusion_and_zero_premises :
  sealed_example_matches [] (sealed_example_label [Pred 3 "P" [sealed_example_x]]
    [[Pred 9 "P" [sealed_example_x]]]) RDIdentity [] = true.
Proof. vm_compute; reflexivity. Qed.
Example sealed_ex_falso_retains_the_original_check :
  sealed_example_matches [] (sealed_example_label [Deq sealed_example_x sealed_example_x] [])
    RDExFalso [] = true.
Proof. vm_compute; reflexivity. Qed.
Example sealed_trivial_equalities_preserve_exact_occurrence_annotations :
  let j := sealed_example_label [Eq zero zero; Pred 7 "P" [sealed_example_x]; Pred 7 "P" [sealed_example_x]]
    [[Eq sealed_example_x sealed_example_x]] in
  sealed_example_application [] j RDTrivialEqualities = Some
    {| application_name := "simplAllTaut"; conclusion := j;
       premises := [{| premise_label := sealed_example_label
         [Pred 7 "P" [sealed_example_x]; Pred 7 "P" [sealed_example_x]] [[]];
         premise_trace := {| continuations := [(1,0); (2,1)]; progressing := [] |} |}] |}.
Proof. vm_compute; reflexivity. Qed.
Example sealed_left_equality_has_exact_substituted_premises :
  sealed_example_matches [] (sealed_example_label
    [Eq sealed_example_x zero; Pred 3 "P" [sealed_example_x]] [[Pred 0 "Q" [sealed_example_x]]])
    (RDLeftEquality (Free 5) zero)
    [sealed_example_label [Eq zero zero; Pred 3 "P" [zero]] [[Pred 0 "Q" [zero]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example sealed_binary_right_split_keeps_both_ordered_premises :
  sealed_example_matches [] (sealed_example_label []
    [[Pred 0 "P" [Var (Exist 0)]; Pred 0 "Q" [Var (Exist 1)]]]) (RDRightSplit 1)
    [sealed_example_label [] [[Pred 0 "P" [Var (Exist 0)]]];
     sealed_example_label [] [[Pred 0 "Q" [Var (Exist 1)]]]] = true.
Proof. vm_compute; reflexivity. Qed.
Example sealed_left_disjunction_preserves_every_native_premise :
  sealed_example_matches [] {| antecedent := [[Pred 3 "P" []]; [Pred 8 "Q" []]]; succedent := [] |}
    RDLeftDisjunction [sealed_example_label [Pred 3 "P" []] []; sealed_example_label [Pred 8 "Q" []] []] = true.
Proof. vm_compute; reflexivity. Qed.
Definition sealed_example_fold_goal := sealed_example_label
  [Pred 3 "N" [sealed_example_x]; Pred 7 "ANCHOR" [zero]; Pred 4 "N" [sealed_example_x]] [].
Example sealed_fold_keeps_the_checked_raw_clause_and_remainder_layout :
  sealed_example_matches sealed_example_definitions sealed_example_fold_goal
    (RDFold 2 [(Free 0,sealed_example_x)] 8)
    [sealed_example_label [Pred 8 "PACK" [successor sealed_example_x]; Pred 7 "ANCHOR" [zero]] []] = true.
Proof. vm_compute; reflexivity. Qed.
Definition sealed_example_right_goal := sealed_example_label [] [[Pred 0 "N" [successor sealed_example_x]]].
Example sealed_right_unfold_retains_checked_head_equalities :
  sealed_example_matches sealed_example_definitions sealed_example_right_goal (RDRightUnfoldMatched 12 0 0 1)
    [sealed_example_label [] [[Eq (successor sealed_example_x) (successor sealed_example_x);
      Pred 0 "N" [sealed_example_x]]]] = true.
Proof. vm_compute; reflexivity. Qed.

Example sealed_identity_rejects_an_unproved_goal :
  sealed_example_present [] (sealed_example_label [Pred 3 "P" []] [[Pred 0 "Q" []]]) RDIdentity = false.
Proof. vm_compute; reflexivity. Qed.
Example sealed_ex_falso_checks_every_disjunct :
  sealed_example_present [] {| antecedent := [[Deq sealed_example_x sealed_example_x]; []]; succedent := [] |}
    RDExFalso = false.
Proof. vm_compute; reflexivity. Qed.
Example sealed_equality_rejects_wrong_descriptor_bindings :
  sealed_example_present [] (sealed_example_label [Eq sealed_example_x zero] [])
    (RDLeftEquality (Free 4) zero) = false.
Proof. vm_compute; reflexivity. Qed.
Example sealed_split_rejects_shared_existential_witnesses :
  sealed_example_present [] (sealed_example_label []
    [[Pred 0 "P" [Var (Exist 0)]; Pred 0 "Q" [Var (Exist 0)]]]) (RDRightSplit 1) = false.
Proof. vm_compute; reflexivity. Qed.
Example sealed_unfold_rejects_wrong_clause_indices :
  sealed_example_present sealed_example_definitions sealed_example_right_goal
    (RDRightUnfoldMatched 12 0 0 99) = false.
Proof. vm_compute; reflexivity. Qed.
Example sealed_unfold_preserves_matching_fuel_checks :
  sealed_example_present sealed_example_definitions sealed_example_right_goal
    (RDRightUnfoldMatched 0 0 0 1) = false.
Proof. vm_compute; reflexivity. Qed.
Example sealed_fold_rejects_incorrect_fresh_tags :
  sealed_example_present sealed_example_definitions sealed_example_fold_goal
    (RDFold 2 [(Free 0,sealed_example_x)] 7) = false.
Proof. vm_compute; reflexivity. Qed.
Definition sealed_example_companion := sealed_example_label [Pred 3 "P" [sealed_example_x]]
  [[Pred 0 "R" [Var (Exist 0); Var (Exist 1)]]].
Example sealed_substitution_rejects_wrong_conclusion_labels :
  sealed_example_present [] (sealed_example_label [Pred 3 "P" [zero]; Eq zero zero] [])
    (RDSubstitute [(Free 5,zero)] sealed_example_companion) = false.
Proof. vm_compute; reflexivity. Qed.
Example sealed_substitution_rejects_capture_of_unmapped_existentials :
  let theta := [(Exist 0,Var (Exist 1))] in
  sealed_example_present [] (subst_sequent theta sealed_example_companion)
    (RDSubstitute theta sealed_example_companion) = false.
Proof. vm_compute; reflexivity. Qed.

(** Freeze a complete Type-valued certificate, not merely its metadata. Its
    evidence field must remain the opaque theorem applied only to data. *)
Definition sealed_example_left_goal := sealed_example_label
  [Deq sealed_example_x zero; Pred 3 "N" [sealed_example_x]; Pred 3 "N" [sealed_example_x]] [].
Definition sealed_example_left_descriptor := RDLeftUnfoldAt 0 1 4.
Definition sealed_native_vm_snapshot := Eval vm_compute in
  sealed_compile_rule_descriptor sealed_example_definitions sealed_example_left_goal sealed_example_left_descriptor.
Definition sealed_snapshot_certificate : certified_application sealed_example_definitions sealed_example_left_goal :=
  match sealed_native_vm_snapshot with Some c => c
  | None => LocalRules.left_disjunction sealed_example_definitions sealed_example_left_goal end.
Example frozen_sealed_certificate_has_original_application_data :
  option_map (certified_rule sealed_example_definitions sealed_example_left_goal) sealed_native_vm_snapshot =
  compiled_application_data sealed_example_definitions sealed_example_left_goal sealed_example_left_descriptor.
Proof. vm_compute; reflexivity. Qed.
Example frozen_semantic_evidence_is_the_data_only_opaque_theorem :
  certified_evidence sealed_example_definitions sealed_example_left_goal sealed_snapshot_certificate =
    compiled_data_evidence sealed_example_definitions sealed_example_left_goal sealed_example_left_descriptor
      (certified_rule sealed_example_definitions sealed_example_left_goal sealed_snapshot_certificate) eq_refl.
Proof. reflexivity. Qed.

Module SealedExampleEnvironment <: DEFINITION_ENV.
  Definition defs := sealed_example_definitions.
End SealedExampleEnvironment.
Module SealedExampleFO := Make SealedExampleEnvironment.
Definition sealed_example_cyclic_payload j rd :=
  match sealed_compile_rule_descriptor SealedExampleEnvironment.defs j rd with
  | Some c => Some (SealedExampleFO.rule (certified_rule SealedExampleEnvironment.defs j c)
      (certified_evidence SealedExampleEnvironment.defs j c))
  | None => None end.
Definition sealed_cyclic_vm_snapshot := Eval vm_compute in
  sealed_example_cyclic_payload sealed_example_left_goal sealed_example_left_descriptor.
Example frozen_cyclic_payload_preserves_all_ordered_premise_labels :
  option_map (fun r => map SealedExampleFO.Cyclic.premise_judgment (SealedExampleFO.Cyclic.rule_premises r))
    sealed_cyclic_vm_snapshot =
  option_map (fun a => map premise_label (premises a))
    (compiled_application_data sealed_example_definitions sealed_example_left_goal sealed_example_left_descriptor).
Proof. vm_compute; reflexivity. Qed.
Example frozen_cyclic_payload_preserves_dense_converted_trace_annotations :
  option_map (fun r => map SealedExampleFO.Cyclic.premise_edge (SealedExampleFO.Cyclic.rule_premises r))
    sealed_cyclic_vm_snapshot =
  option_map (fun a => map (fun p => SealedExampleFO.edge (conclusion a) (premise_label p) (premise_trace p))
    (premises a)) (compiled_application_data sealed_example_definitions sealed_example_left_goal sealed_example_left_descriptor).
Proof. vm_compute; reflexivity. Qed.

Example sealed_data_still_proves_the_checked_identity d :
  valid d (sealed_example_label [Pred 3 "P" [sealed_example_x]] [[Pred 9 "P" [sealed_example_x]]]).
Proof.
  pose (j := sealed_example_label [Pred 3 "P" [sealed_example_x]] [[Pred 9 "P" [sealed_example_x]]]).
  pose (a := native_axiom_application "Id" j).
  assert (Hdata : compiled_application_data d j RDIdentity = Some a) by reflexivity.
  apply (proj2 (compiled_fields_sound d j RDIdentity a Hdata)); intros p H; contradiction.
Qed.

About compiled_data_evidence.
Print Assumptions compiled_data_evidence.
Print Assumptions sealed_compile_application_data.
Print Assumptions sealed_compile_rejects.
Print Assumptions compiled_fields_sound.
Print Assumptions sealed_compiled_proposal_local_sound.
