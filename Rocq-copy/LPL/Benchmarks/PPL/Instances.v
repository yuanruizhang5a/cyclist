(** * Independent vocabularies, arbitrary frames, and structured world terms. *)
From Stdlib Require Import List Bool Arith.
From CyclistRocq.LPL.PPL Require Import Instance.
From CyclistRocq.LPL Require Import Signature Syntax Semantics Progress Rules RuleGeneration.
Import ListNotations.
Module AbstractFrame (V : VOCABULARY) (F : FRAME V).
Module Instance := MakeInstance V F.
Definition M := Instance.Model.interpretation.
Theorem arbitrary_predicate p s tail :
  Instance.Sem.formula_holds M (Instance.Syn.Atom p) (s::tail) <-> F.proposition_holds p s.
Proof. reflexivity. Qed.
Theorem arbitrary_action a tr : Instance.Sem.program_holds M (Instance.Syn.Atomic a) tr <->
  exists s t, tr=[s;t] /\ F.step a s t.
Proof. reflexivity. Qed.
End AbstractFrame.
Module BooleanVocabulary <: VOCABULARY.
  Definition action := bool.
  Definition proposition := bool.
  Definition relation_symbol := nat.
  Definition action_eq_dec := Bool.bool_dec.
  Definition proposition_eq_dec := Bool.bool_dec.
  Definition relation_eq_dec := Nat.eq_dec.
  Definition relation_wfb (_ : nat) n := Nat.eqb n 1.
End BooleanVocabulary.
Module BooleanFrame <: FRAME BooleanVocabulary.
  Definition State := bool.
  Definition inhabitant := false.
  Definition step (a s t : bool) := if a then t=negb s else t=s.
  Definition proposition_holds (p s : bool) := s=p.
  Definition relation_holds (_ : nat) (arguments : list (list bool)) := exists tr, arguments=[tr] /\ tr<>[].
End BooleanFrame.
Module Boolean := MakeInstance BooleanVocabulary BooleanFrame.
Definition BM := Boolean.Model.interpretation.
Example boolean_atomic_run : Boolean.Sem.program_holds BM (Boolean.Syn.Atomic true) [false;true].
Proof. exists false, true; split; reflexivity. Qed.
Example boolean_predicate : Boolean.Sem.formula_holds BM (Boolean.Syn.Atom true) [true;false].
Proof. reflexivity. Qed.

Inductive world_expr := WName (x : nat) | WFlip (body : world_expr).
Fixpoint world_expr_eq_dec (a b : world_expr) : {a=b}+{a<>b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Fixpoint world_names u := match u with WName x => [x] | WFlip u => world_names u end.
Fixpoint world_substitute x value u := match u with
  | WName y => if Nat.eqb x y then value else u
  | WFlip u => WFlip (world_substitute x value u) end.
Fixpoint world_eval (rho : nat -> bool) u := match u with
  | WName x => rho x | WFlip u => negb (world_eval rho u) end.
Module Base := MakeLanguage BooleanVocabulary.
Module Structured <: LANGUAGE.
  Definition atom := Base.atom.
  Definition binder := Base.binder.
  Definition action := Base.action.
  Definition world_term := world_expr.
  Definition relation_symbol := Base.relation_symbol.
  Definition atom_eq_dec := Base.atom_eq_dec.
  Definition binder_eq_dec := Base.binder_eq_dec.
  Definition action_eq_dec := Base.action_eq_dec.
  Definition world_term_eq_dec := world_expr_eq_dec.
  Definition relation_eq_dec := Base.relation_eq_dec.
  Definition atom_wfb := Base.atom_wfb.
  Definition extension_wfb := Base.extension_wfb.
  Definition action_wfb := Base.action_wfb.
  Definition world_term_wfb (_ : world_expr) := true.
  Definition custom_relation_wfb := Base.custom_relation_wfb.
  Definition world_name := WName.
  Definition world_support := world_names.
  Definition subst_world := world_substitute.
End Structured.
Module SS := CyclistRocq.LPL.Syntax.MakeSyntax Structured.
Module SM := CyclistRocq.LPL.Semantics.MakeSemantics Structured SS.
Definition structured_model : SM.model.
Proof.
  refine {| SM.carrier := bool; SM.carrier_inhabitant := false;
    SM.interpret_atom := fun p s => s=p;
    SM.interpret_extension := fun x _ _ => match x with end;
    SM.interpret_action := fun a s t => if a then t=negb s else t=s;
    SM.interpret_atomic_trace := fun a tr => exists s t, tr=[s;t] /\ (if a then t=negb s else t=s);
    SM.interpret_world_term := world_eval;
    SM.interpret_relation := fun _ _ => True |}.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros rho rho' u; induction u; intro H; cbn [world_eval].
    + apply H; now left.
    + now rewrite IHu.
  - intros rho x value u; unfold Structured.subst_world; induction u; cbn [world_substitute world_eval].
    + destruct (Nat.eqb x x0); reflexivity.
    + now rewrite IHu.
Defined.
Definition structured_world : SM.world structured_model.
Proof. refine (SM.World structured_model (fun _ => false) (fun _ => [false]) _); discriminate. Defined.
Example structured_labels_are_interpreted :
  SM.eval_label structured_model structured_world
    (SS.Join (SS.StateLabel (WName 0)) (SS.StateLabel (WFlip (WName 0)))) = [false;true].
Proof. reflexivity. Qed.
Example structured_substitution :
  SS.subst_world_label 1 (WFlip (WName 0)) (SS.StateLabel (WFlip (WName 1))) = SS.StateLabel (WFlip (WFlip (WName 0))).
Proof. reflexivity. Qed.
Example custom_relation_payload : SM.relation_holds structured_model structured_world (SS.CustomRelation 7 [SS.StateLabel (WFlip (WName 0))]).
Proof. exact I. Qed.
Module SP := MakeProgress Structured SS SM.
Module SK.
  Module Core := MakeRules Structured SS SM SP.
  Module Model <: SM.INTERPRETATION.
    Definition interpretation := structured_model.
  End Model.
  Include Core.ForModel Model.
End SK.
Module SG := MakeRuleGeneration Structured SS SM SP SK.
Definition structured_root := SS.Jdg [SS.Occ (SS.StateLabel (WFlip (WName 0))) (SS.Atom true) None]
  [SS.Occ (SS.Join SS.Empty (SS.StateLabel (WFlip (WName 0)))) (SS.Box (SS.Atomic true) (SS.First (SS.Atom true))) None].
Example structured_action_rule_generated :
  match SG.generate_requested structured_root (SG.AtomicEigen SG.OnRight 0 1) with Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions structured_labels_are_interpreted.
Print Assumptions boolean_atomic_run.
