(** * An arbitrary protected component with an uninterpreted predicate.
    Actions may change the active component nondeterministically. No decision
    procedure or inductive definition of the protected predicate is assumed. *)
From Stdlib Require Import List Bool Arith.
From CyclistRocq.LPL.PPL Require Import Instance.
From CyclistRocq.LPL Require Import TraceSafety.
Import ListNotations.
Module Type PROTECTED_DATA.
  Parameter Active Protected : Type.
  Parameter active_inhabitant : Active.
  Parameter protected_inhabitant : Protected.
  Parameter property : Protected -> Prop.
  Parameter active_step : nat -> Active -> Active -> Prop.
End PROTECTED_DATA.
Module ProtectedProgram (D : PROTECTED_DATA).
Module V <: VOCABULARY.
  Definition action := nat.
  Definition proposition := unit.
  Definition relation_symbol := Empty_set.
  Definition action_eq_dec := Nat.eq_dec.
  Definition proposition_eq_dec (x y : unit) : {x=y}+{x<>y}. Proof. decide equality. Defined.
  Definition relation_eq_dec (x y : Empty_set) : {x=y}+{x<>y} := match x with end.
  Definition relation_wfb (x : Empty_set) (_ : nat) : bool := match x with end.
End V.
Module F <: FRAME V.
  Definition State := (D.Active * D.Protected)%type.
  Definition inhabitant := (D.active_inhabitant,D.protected_inhabitant).
  Definition step a (s t : State) := D.active_step a (fst s) (fst t) /\ snd t = snd s.
  Definition proposition_holds (_ : unit) (s : State) := D.property (snd s).
  Definition relation_holds (x : Empty_set) (_ : list (list State)) : Prop := match x with end.
End F.
Module Instance := MakeInstance V F.
Module S := Instance.Syn.
Module Sem := Instance.Sem.
Module Safety := MakeSafety Instance.Language Instance.Syn Instance.Sem.
Definition M := Instance.Model.interpretation.
Definition atom := S.Atom tt [].
Definition action x := S.Atomic x tt.
Definition nested := S.Seq (S.Star (S.Choice (action 0) (S.Seq (S.Test S.Truth) (action 1))))
  (S.Choice (action 2) (S.Star (action 1))).
Definition Inv (s : F.State) := D.property (snd s).
Lemma preserves a payload s t : Sem.interpret_action M a payload s t -> Inv s -> Inv t.
Proof. intros [_ Heq] H; unfold Inv in *; now rewrite Heq. Qed.
Theorem all_visited_preserved : trace_safe Inv (Sem.program_holds M nested).
Proof. exact (Safety.program_safe M Inv preserves nested). Qed.
Definition label := S.StateLabel 0.
Definition root := S.Jdg [S.Occ label atom None] [S.Occ label (S.Box nested (S.Always atom)) None].
Theorem arbitrary_predicate_invariant : Sem.Valid M root.
Proof.
  intros w Ha Hrelations Hleft; pose proof (Forall_inv Hleft) as [_ Hinitial].
  exists (S.Occ label (S.Box nested (S.Always atom)) None); split; [now left|].
  split; [discriminate|]. intros execution result Hprogram Ho.
  apply Sem.overlap_list_singleton in Ho as [tail [Heq ->]]; subst execution.
  apply (proj2 (Safety.always_head_forall M atom ltac:(intros s tail'; reflexivity) (Sem.eval_update M w 0 :: tail) ltac:(discriminate))).
  eapply all_visited_preserved; eauto.
Qed.
Definition witness_world (b : D.Protected) : Sem.world M.
Proof. refine (Sem.World M (fun _ => (D.active_inhabitant,b)) (fun _ => [(D.active_inhabitant,b)]) _); discriminate. Defined.
Theorem nonvacuity b : D.property b ->
  Sem.admissible M root (witness_world b) /\ Sem.left_holds M (witness_world b) root.(S.antecedent).
Proof. intro H; split; [apply Sem.judgment_wfb_admissible; reflexivity|]. constructor; [split; [discriminate|exact H]|constructor]. Qed.
End ProtectedProgram.
Module Concrete <: PROTECTED_DATA.
  Definition Active := nat.
  Definition Protected := bool.
  Definition active_inhabitant := 0.
  Definition protected_inhabitant := false.
  Definition property b := b=true.
  Definition active_step (_ x y : nat) := y=x \/ y=S x.
End Concrete.
Module Example := ProtectedProgram Concrete.
Example concrete_nonvacuity : Example.Sem.admissible Example.M Example.root (Example.witness_world true) /\
  Example.Sem.left_holds Example.M (Example.witness_world true) Example.root.(Example.S.antecedent).
Proof. apply Example.nonvacuity; reflexivity. Qed.
Print Assumptions Example.arbitrary_predicate_invariant.
Print Assumptions Example.all_visited_preserved.
