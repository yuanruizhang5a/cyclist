From Stdlib Require Import List ZArith.
From CyclistRocq.LPL Require Import Signature Rules RuleGeneration Certification.
From CyclistRocq.LPL.Benchmarks Require Import Support InvariantSupport.
Import ListNotations.

Module Type PROPERTY.
  Parameter holds : Z -> Prop.
End PROPERTY.
Module ArbitraryPredicate (Property : PROPERTY).
  Module Kernel.
    Module Core := MakeRules ZSignature.
    Module Model <: Core.Pr.Sem.INTERPRETATION.
      Definition interpretation := Core.Pr.Sem.Model Z 0%Z ZKernel.Model.fn
        (fun _ args => match args with [x] => Property.holds x | _ => False end).
    End Model.
    Include Core.ForModel Model.
  End Kernel.
  Module Export G := MakeRuleGeneration ZSignature Kernel.
  Definition invariant (s : state M) := Property.holds (s 1).
  Definition observation := Pred 0 [Var 1].
  Definition increment := Assign 0 (Fun 2 [Var 0]).
  Definition decrement := Assign 0 (Fun 3 [Var 0]).
  Definition nested := Seq (Choice (Seq increment decrement) (Test Truth))
    (Star (Choice increment (Seq (Test Truth) decrement))).

  Lemma assignment_safe t : trace_safe invariant (program_holds M (Assign 0 t)).
  Proof.
    intros s tail [start Htrace] Hinitial; injection Htrace as Hs Htail; subst s tail.
    constructor; [exact Hinitial|]. constructor; [|constructor].
    unfold invariant in *; rewrite write_other by discriminate; exact Hinitial.
  Qed.
  Lemma test_safe : trace_safe invariant (program_holds M (Test Truth)).
  Proof.
    intros s tail [start [Htrace _]] Hinitial; injection Htrace as Hs Htail; subst;
      repeat constructor; exact Hinitial.
  Qed.
  Lemma seq_safe a b : trace_safe invariant (program_holds M a) ->
    trace_safe invariant (program_holds M b) -> trace_safe invariant (program_holds M (Seq a b)).
  Proof. apply compose_safe. Qed.
  Lemma union_safe a b : trace_safe invariant (program_holds M a) ->
    trace_safe invariant (program_holds M b) -> trace_safe invariant (program_holds M (Choice a b)).
  Proof. apply choice_safe. Qed.
  Lemma star_safe a : trace_safe invariant (program_holds M a) -> trace_safe invariant (program_holds M (Star a)).
  Proof.
    intros Ha s tail [n Hpower] Hinitial.
    change (trace_power (program_holds M a) n (s :: tail)) in Hpower.
    exact (power_safe invariant (program_holds M a) Ha n s tail Hpower Hinitial).
  Qed.
  Lemma nested_safe : trace_safe invariant (program_holds M (Star nested)).
  Proof.
    apply star_safe, seq_safe.
    - apply union_safe; [apply seq_safe; apply assignment_safe|apply test_safe].
    - apply star_safe, union_safe; [apply assignment_safe|].
      apply seq_safe; [apply test_safe|apply assignment_safe].
  Qed.
  Definition root := Jdg [Occ (StateLabel (Base 0)) observation None]
    [Occ (StateLabel (Base 0)) (Box (Star nested) (Always observation)) None].
  Theorem preserves_uninterpreted_predicate_at_every_state : Cyclic.Valid root.
  Proof.
    intros w Hadm Hleft; pose proof (proj1 (left_singleton w _) Hleft) as [_ Hinitial].
    exists (Occ (StateLabel (Base 0)) (Box (Star nested) (Always observation)) None); split; [now left|].
    split; [discriminate|].
    change (formula_holds M (Box (Star nested) (Always observation)) [eval_update M w (Base 0)]).
    intros execution result Hprogram Ho; apply overlap_list_singleton in Ho as [tail [Heq ->]]; subst execution.
    apply always_pure_forall; [reflexivity|discriminate|].
    exact (nested_safe (eval_update M w (Base 0)) tail Hprogram Hinitial).
  Qed.
  Definition witness_world : world M.
  Proof. refine (World M (fun _ _ => 0%Z) (fun _ => [fun _ => 0%Z]) _); discriminate. Defined.
  Example nonvacuity : exists w, admissible M root w.
  Proof. exists witness_world; apply judgment_wfb_admissible; reflexivity. Qed.
End ArbitraryPredicate.
Module EvenProperty <: PROPERTY.
  Definition holds z := exists k, z = (2 * k)%Z.
End EvenProperty.
Module Example := ArbitraryPredicate EvenProperty.
Print Assumptions Example.preserves_uninterpreted_predicate_at_every_state.
