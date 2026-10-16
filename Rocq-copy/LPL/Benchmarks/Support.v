From Stdlib Require Import List Bool Arith ZArith Lia String.
From CyclistRocq.LPL Require Import Signature Semantics Rules RuleGeneration Certification.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Module ZSignature <: SIGNATURE.
  Definition function_symbol := nat.
  Definition predicate_symbol := nat.
  Definition function_eq_dec := Nat.eq_dec.
  Definition predicate_eq_dec := Nat.eq_dec.
  Definition function_arity f := match f with 0 | 1 => 0 | 2 | 3 | 5 => 1 | _ => 2 end.
  Definition predicate_arity p := match p with 0 | 1 => 1 | _ => 2 end.
End ZSignature.
Module ZKernel.
  Module Core := MakeRules ZSignature.
  Module Model <: Core.Pr.Sem.INTERPRETATION.
    Definition fn f (args : list Z) : Z :=
      match f, args with
      | 0, _ => 0%Z | 1, _ => 1%Z | 2, [x] => (x+1)%Z | 3, [x] => (x-1)%Z
      | 4, [x;y] => (x+y)%Z | _, _ => 0%Z end.
    Definition pred p (args : list Z) : Prop :=
      match p, args with
      | 0, [x] => (0 <= x)%Z | 1, [x] => (x = 0)%Z
      | 2, [x;y] => (x < y)%Z | 3, [x;y] => (x = y)%Z | _, _ => False end.
    Definition interpretation := Core.Pr.Sem.Model Z 0%Z fn pred.
  End Model.
  Include Core.ForModel Model.
End ZKernel.
Module Export Generation := MakeRuleGeneration ZSignature ZKernel.
Module Export Cert := MakeCertification ZSignature ZKernel.

Definition x := Var 0.
Definition y := Var 1.
Definition zero := Fun 0 [].
Definition one := Fun 1 [].
Definition inc t := Fun 2 [t].
Definition dec t := Fun 3 [t].
Definition plus a b := Fun 4 [a;b].
Definition nonnegative := Pred 0 [x].
Definition iszero := Pred 1 [x].
Definition u0 := Base 0.
Definition u1 := Base 1.
Definition l0 := StateLabel u0.
Definition l1 := StateLabel u1.
Definition assertion l a := Occ l a None.
Definition traced l a t := Occ l a (Some t).
Definition constant_state (z : Z) : state M := fun _ => z.
Definition constant_world (z : Z) : world M.
Proof. refine (World M (fun _ => constant_state z) (fun _ => [constant_state z]) _); discriminate. Defined.

Definition someb {A} (value : option A) := match value with Some _ => true | None => false end.
Definition require_rule (value : option Cyclic.rule_instance) (H : someb value = true) : Cyclic.rule_instance.
Proof. destruct value as [r|]; [exact r|discriminate]. Defined.
Definition require_axiom (value : option Cyclic.axiom_instance) (H : someb value = true) : Cyclic.axiom_instance.
Proof. destruct value as [a|]; [exact a|discriminate]. Defined.
Definition requested j req (H : someb (generate_requested j req) = true) := require_rule (generate_requested j req) H.
Definition generated_axiom j (H : someb (generate_axiom j) = true) := require_axiom (generate_axiom j) H.
Definition premise_at r k := match nth_error r.(Cyclic.rule_premises) k with
  | Some p => p.(Cyclic.premise_judgment) | None => r.(Cyclic.rule_conclusion) end.

Lemma root_nonvacuous j : judgment_wfb j = true -> exists w, admissible M j w.
Proof. intro H; exists (constant_world 0); apply judgment_wfb_admissible; exact H. Qed.

Lemma concrete_valid j : Cyclic.Valid j -> admissible M j (constant_world 0) ->
  left_holds M (constant_world 0) j.(antecedent) -> right_holds M (constant_world 0) j.(succedent).
Proof. intros Hvalid Ha Hl; exact (Hvalid (constant_world 0) Ha Hl). Qed.
