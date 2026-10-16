From Stdlib Require Import List Bool ZArith.
From CyclistRocq.LPL Require Import Signature Rules RuleGeneration Certification.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations.
Module Type ARBITRARY_MODEL.
  Parameter carrier : Type.
  Parameter point : carrier.
  Parameter fn : nat -> list carrier -> carrier.
  Parameter pr : nat -> list carrier -> Prop.
End ARBITRARY_MODEL.
Module Symbolic (A : ARBITRARY_MODEL).
  Module Kernel.
    Module Core := MakeRules ZSignature.
    Module Model <: Core.Pr.Sem.INTERPRETATION.
      Definition interpretation := Core.Pr.Sem.Model A.carrier A.point A.fn A.pr.
    End Model.
    Include Core.ForModel Model.
  End Kernel.
  Module Export G := MakeRuleGeneration ZSignature Kernel.
  Module Export C := MakeCertification ZSignature Kernel.
  Definition root := Jdg [] [Occ (StateLabel (Base 0)) (Equal (Var 0) (Var 0)) None].
  Definition ax : Cyclic.axiom_instance.
  Proof.
    refine (close_atoms root eq_refl eq_refl _); intros w Hleft.
    exists (Occ (StateLabel (Base 0)) (Equal (Var 0) (Var 0)) None); split; [now left|];
      split; [discriminate|reflexivity].
  Defined.
  Theorem arbitrary_model_reflexivity : Cyclic.Valid root.
  Proof. exact (raw_check_sound (axiom_graph ax) empty_trace_witness (axiom_graph_raw_check ax)). Qed.
  Definition witness_world : world M.
  Proof. refine (World M (fun _ _ => A.point) (fun _ => [fun _ => A.point]) _); discriminate. Defined.
  Example nonvacuity : exists w, admissible M root w.
  Proof. exists witness_world; apply judgment_wfb_admissible; reflexivity. Qed.
End Symbolic.

Module BooleanSignature <: SIGNATURE.
  Definition function_symbol := bool.
  Definition predicate_symbol := unit.
  Definition function_eq_dec := Bool.bool_dec.
  Definition predicate_eq_dec : forall x y : unit, {x=y}+{x<>y}.
  Proof. decide equality. Defined.
  Definition function_arity (f : bool) := if f then 1 else 0.
  Definition predicate_arity (_ : unit) := 1.
End BooleanSignature.
Module BooleanKernel.
  Module Core := MakeRules BooleanSignature.
  Module Model <: Core.Pr.Sem.INTERPRETATION.
    Definition interpretation := Core.Pr.Sem.Model bool false
      (fun f args => match f,args with true,[x] => x | _,_ => false end)
      (fun _ args => args = [true]).
  End Model.
  Include Core.ForModel Model.
End BooleanKernel.
Module BooleanInstance.
  Module Export G := MakeRuleGeneration BooleanSignature BooleanKernel.
  Module Export C := MakeCertification BooleanSignature BooleanKernel.
  Definition root := Jdg [] [Occ (StateLabel (Base 0)) Truth None].
  Definition ax := match generate_axiom root as result return
    (match result with Some _ => True | None => False end) -> Cyclic.axiom_instance with
    | Some a => fun _ => a | None => fun H => False_rect _ H end I.
  Theorem boolean_signature_valid : Cyclic.Valid root.
  Proof. exact (raw_check_sound (axiom_graph ax) empty_trace_witness (axiom_graph_raw_check ax)). Qed.
  Definition witness_world : world M.
  Proof. refine (World M (fun _ _ => false) (fun _ => [fun _ => false]) _); discriminate. Defined.
  Example nonvacuity : exists w, admissible M root w.
  Proof. exists witness_world; apply judgment_wfb_admissible; reflexivity. Qed.
End BooleanInstance.

Import Generation Cert.
Example functions_are_not_constructors : eval_term M (constant_state 0) (Fun 5 [zero]) =
  eval_term M (constant_state 0) (Fun 5 [one]) /\ eval_term M (constant_state 0) zero <> eval_term M (constant_state 0) one.
Proof. split; [reflexivity|discriminate]. Qed.
Print Assumptions BooleanInstance.boolean_signature_valid.

Module ZArbitraryModel <: ARBITRARY_MODEL.
  Definition carrier := Z.
  Definition point := 0%Z.
  Definition fn := ZKernel.Model.fn.
  Definition pr := ZKernel.Model.pred.
End ZArbitraryModel.
Module SymbolicZ := Symbolic ZArbitraryModel.
Print Assumptions SymbolicZ.arbitrary_model_reflexivity.
