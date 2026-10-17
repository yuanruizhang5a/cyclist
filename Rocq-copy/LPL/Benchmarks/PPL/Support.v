(** * A small nondeterministic machine and explicit proof-script helpers. *)
From Stdlib Require Import List Bool Arith Lia String.
From CyclistRocq.LPL.PPL Require Import Instance.
From CyclistRocq.LPL Require Import Progress Rules RuleGeneration Certification.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Inductive action := Acquire | Release | Reset | Stutter | Cycle.
Inductive proposition := Safe | IsIdle | IsHeld | IsReleased.
Inductive extra_relation := SameState.
Inductive machine_state := Idle | Held | Released | Bad | Dead.

Module Vocabulary <: VOCABULARY.
  Definition action := action.
  Definition proposition := proposition.
  Definition relation_symbol := extra_relation.
  Definition action_eq_dec (x y : action) : {x=y}+{x<>y}.
  Proof. decide equality. Defined.
  Definition proposition_eq_dec (x y : proposition) : {x=y}+{x<>y}.
  Proof. decide equality. Defined.
  Definition relation_eq_dec (x y : extra_relation) : {x=y}+{x<>y}.
  Proof. decide equality. Defined.
  Definition relation_wfb (_ : extra_relation) n := Nat.eqb n 2.
End Vocabulary.
Module Frame <: FRAME Vocabulary.
  Definition State := machine_state.
  Definition inhabitant := Idle.
  Definition step a s t : Prop := match a with
    | Acquire => s=Idle /\ (t=Held \/ t=Released)
    | Release => s=Held /\ t=Released
    | Reset => s=Released /\ t=Idle
    | Stutter => s<>Bad /\ t=s
    | Cycle => (s=Idle /\ (t=Held \/ t=Released)) \/ (s=Held /\ t=Released) \/ (s=Released /\ t=Idle) end.
  Definition proposition_holds p s : Prop := match p with
    | Safe => s<>Bad | IsIdle => s=Idle | IsHeld => s=Held | IsReleased => s=Released end.
  Definition relation_holds (_ : extra_relation) (arguments : list (list State)) : Prop :=
    exists s, arguments=[[s];[s]].
End Frame.
Module Machine := MakeInstance Vocabulary Frame.
Module Export Syn := Machine.Syn.
Module Export Sem := Machine.Sem.
Module Pr := MakeProgress Machine.Language Machine.Syn Machine.Sem.
Module MachineKernel.
  Module Core := MakeRules Machine.Language Machine.Syn Machine.Sem Pr.
  Module Model := Machine.Model.
  Include Core.ForModel Model.
End MachineKernel.
Module Export Kernel := MachineKernel.
Module Export Generation := MakeRuleGeneration Machine.Language Machine.Syn Machine.Sem Pr MachineKernel.
Module Export Cert := MakeCertification Machine.Language Machine.Syn Machine.Sem Pr MachineKernel.
Definition M := Machine.Model.interpretation.
Definition act a := Atomic a .
Definition atom p := Atom p.
Definition safe := atom Safe.
Definition l0 := StateLabel 0.
Definition l1 := StateLabel 1.
Definition assertion l a := Occ l a None.
Definition traced l a t := Occ l a (Some t).
Definition constant_world (s : machine_state) : world M.
Proof. refine (World M (fun _ => s) (fun _ => [s]) _); discriminate. Defined.
Definition someb {A} (x : option A) := match x with Some _ => true | None => false end.
Definition require_rule (x : option Cyclic.rule_instance) (H : someb x = true) : Cyclic.rule_instance.
Proof. destruct x as [r|]; [exact r|discriminate]. Defined.
Definition require_axiom (x : option Cyclic.axiom_instance) (H : someb x = true) : Cyclic.axiom_instance.
Proof. destruct x as [a|]; [exact a|discriminate]. Defined.
Definition requested j req (H : someb (generate_requested j req) = true) := require_rule (generate_requested j req) H.
Definition generated_axiom j (H : someb (generate_axiom j) = true) := require_axiom (generate_axiom j) H.
Definition premise_at r k := match nth_error r.(Cyclic.rule_premises) k with
  | Some p => p.(Cyclic.premise_judgment) | None => r.(Cyclic.rule_conclusion) end.
Lemma root_nonvacuous j : judgment_wfb j = true -> exists w, admissible M j w.
Proof. intro H; exists (constant_world Idle); apply judgment_wfb_admissible; exact H. Qed.

Lemma action_safe a s t : Frame.proposition_holds Safe s -> Frame.step a s t -> Frame.proposition_holds Safe t.
Proof. destruct a; cbn [Frame.step Frame.proposition_holds]; intros Hs Hstep; intuition congruence. Qed.
