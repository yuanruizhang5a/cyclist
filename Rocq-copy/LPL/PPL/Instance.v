(** * Plain PPL instances over arbitrary user vocabularies and frames.

    An action name is arbitrary data. Its interpretation can be infinite,
    nondeterministic and undecidable. Propositions are arbitrary predicates.
    No first-order term, assignment or quantifier is required here. *)
From Stdlib Require Import List Bool Arith.
From CyclistRocq.LPL Require Import Signature Syntax Semantics Progress Rules RuleGeneration Certification.
Import ListNotations.

Module Type VOCABULARY.
  Parameter action proposition relation_symbol : Type.
  Parameter action_eq_dec : forall x y : action, {x=y}+{x<>y}.
  Parameter proposition_eq_dec : forall x y : proposition, {x=y}+{x<>y}.
  Parameter relation_eq_dec : forall x y : relation_symbol, {x=y}+{x<>y}.
  Parameter relation_wfb : relation_symbol -> nat -> bool.
End VOCABULARY.

Module MakeLanguage (V : VOCABULARY) <: LANGUAGE.
  Definition atom := V.proposition.
  Definition binder := Empty_set.
  Definition action := V.action.
  Definition world_term := nat.
  Definition relation_symbol := V.relation_symbol.
  Definition atom_eq_dec := V.proposition_eq_dec.
  Definition binder_eq_dec (x y : binder) : {x=y}+{x<>y} := match x with end.
  Definition action_eq_dec := V.action_eq_dec.
  Definition world_term_eq_dec := Nat.eq_dec.
  Definition relation_eq_dec := V.relation_eq_dec.
  Definition atom_wfb (_ : atom) := true.
  Definition extension_wfb (x : binder) (_ : bool) : bool := match x with end.
  Definition action_wfb (_ : action) := true.
  Definition world_term_wfb (_ : nat) := true.
  Definition custom_relation_wfb := V.relation_wfb.
  Definition world_name (x : nat) := x.
  Definition world_support (x : nat) := [x].
  Definition subst_world x replacement u := if Nat.eqb x u then replacement else u.
End MakeLanguage.

Module Type FRAME (V : VOCABULARY).
  Parameter State : Type.
  Parameter inhabitant : State.
  Parameter step : V.action -> State -> State -> Prop.
  Parameter proposition_holds : V.proposition -> State -> Prop.
  Parameter relation_holds : V.relation_symbol -> list (list State) -> Prop.
End FRAME.

Module MakeInstance (V : VOCABULARY) (F : FRAME V).
  Module Language := MakeLanguage V.
  Module Syn := MakeSyntax Language.
  Module Sem := MakeSemantics Language Syn.
  Module Model <: Sem.INTERPRETATION.
    Definition interpretation : Sem.model.
    Proof.
      refine {| Sem.carrier := F.State;
        Sem.carrier_inhabitant := F.inhabitant;
        Sem.interpret_atom := F.proposition_holds;
        Sem.interpret_extension := fun x _ _ => match x with end;
        Sem.interpret_action := F.step;
        Sem.interpret_atomic_trace := fun a tr => exists s t, tr=[s;t] /\ F.step a s t;
        Sem.interpret_world_term := fun rho x => rho x;
        Sem.interpret_relation := F.relation_holds |}.
      - intros; reflexivity.
      - intros; reflexivity.
      - intros rho rho' u H; apply H; now left.
      - intros rho x replacement u; unfold Language.subst_world;
          destruct (Nat.eqb x u); reflexivity.
    Defined.
  End Model.
End MakeInstance.
