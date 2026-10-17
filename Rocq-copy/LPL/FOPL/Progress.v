(** * Semantic ranks for cyclic traces

    Read Semantics.v first. This module describes counterexample histories,
    assigns them a mathematical minimum measure, and proves the inequalities
    needed by traced rules. It finishes by instantiating Framework.THEORY.
    Rules.v packages these inequalities into proof-producing countersteps.

    A trace is a list of states; a history is a list of such traces. Its
    measure sums their lengths. A premise may describe a longer accumulated
    trace yet have smaller rank because an outer execution-history component
    has been removed. No execution enumeration or program evaluator is used
    to compute these semantic minima. *)
From Stdlib Require Import List Bool Arith Lia Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription Logic.ConstructiveEpsilon.
From CyclistRocq.LPL.FOPL Require Import Signature Syntax Semantics.
From CyclistRocq.LPL Require Import Progress.
From CyclistRocq.Cyclic Require Import Framework.
Import ListNotations.

Module MakeProgress (S : SIGNATURE).
Module Export Sem := MakeSemantics S.
Module Shared := CyclistRocq.LPL.Progress.MakeProgress Sem.Syn.Language Sem.Syn.Shared Sem.Shared.
Module ForModel (I : Sem.INTERPRETATION)
  (SharedModel : Sem.Shared.INTERPRETATION with Definition interpretation := Sem.general_model I.interpretation)
  (Base : Shared.MODEL SharedModel).
Module Export Common := Base.
Definition M := I.interpretation.
Lemma assignment_execution prefix s x t run :
  execution_sequence (prefix ++ [s]) (Assign x t) run <->
  run = [prefix ++ [s]; (prefix ++ [s]) ++ [write M s x (eval_term M s t)]].
Proof.
  split.
  - intros [start [steps [result [[initial Heq] [_ [Ho Hrun]]]]]].
    inversion Heq; subst start steps. apply overlap_snoc in Ho as [-> ->].
    rewrite Hrun. reflexivity.
  - intro Hrun. exists s, [write M s x (eval_term M s t)],
      ((prefix ++ [s]) ++ [write M s x (eval_term M s t)]).
    split; [exists s; reflexivity|]. split; [discriminate|].
    split; [apply overlap_snoc; auto|exact Hrun].
Qed.

Lemma assignment_decrease prefix s x t body :
  ~ formula_holds M (Box (Assign x t) body) (prefix ++ [s]) ->
  minimum_counterexample body ((prefix ++ [s]) ++ [write M s x (eval_term M s t)]) <
  minimum_counterexample (Box (Assign x t) body) (prefix ++ [s]).
Proof.
  intro Hfalse.
  assert (prefix ++ [s] <> []) as Htr by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  assert ((prefix ++ [s]) ++ [write M s x (eval_term M s t)] <> []) as Hnext
    by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  assert (forall run, execution_sequence (prefix ++ [s]) (Assign x t) run <-> True /\ run = [prefix ++ [s]; (prefix ++ [s]) ++ [write M s x (eval_term M s t)]]) as Hstep.
  { intro run. rewrite assignment_execution. tauto. }
  destruct (atomic_minimum (Assign x t) (prefix ++ [s]) ((prefix ++ [s]) ++ [write M s x (eval_term M s t)]) True body Htr Hnext Hstep Hfalse) as [_ [_ Hrank]].
  destruct prefix; cbn in *; lia.
Qed.

Section CounterSwitch.
Context (v : nat) (f : domain M -> domain M) (Hf : forall d, f (f d) = d).
Let T := switch M v f.
Let HT := switch_involutive M v f Hf.
Definition map_history := map (map T).

Lemma history_switch tr rest :
  map_history (execution_history tr rest) = execution_history (map T tr) (map T rest).
Proof.
  revert tr; induction rest as [|s rest IH]; intro tr; cbn [map_history execution_history map]; [reflexivity|].
  rewrite IH, map_app; reflexivity.
Qed.

Lemma last_map_history history : last (map_history history) [] = map T (last history []).
Proof.
  induction history as [|tr history IH]; [reflexivity|].
  destruct history; cbn [map_history map last] in *; assumption || reflexivity.
Qed.

Lemma execution_switch tr p history : ~ In v (program_vars p) ->
  execution_sequence tr p history -> execution_sequence (map T tr) p (map_history history).
Proof.
  intros Hfresh [s [rest [result [Hp [Hrest [Ho ->]]]]]].
  exists (T s), (map T rest), (map T result); split.
  - exact (proj2 (proj2 (switch_semantics M v f Hf) p Hfresh (s :: rest)) Hp).
  - split.
    + intro H; apply map_eq_nil in H; contradiction.
    + split; [exact (overlap_list_map T _ _ _ Ho)|apply history_switch].
Qed.

Lemma counterexample_switch_forward a : ~ In v (formula_vars a) -> forall tr history,
  counterexample a tr history -> counterexample a (map T tr) (map_history history).
Proof.
  induction a; intros Hfresh tr history Hce; cbn [counterexample] in *;
    try solve [destruct Hce as [Hbad ->]; split; [intro H; apply Hbad;
      exact (proj1 (proj1 (switch_semantics M v f Hf) _ Hfresh tr) H)|reflexivity]].
  assert (~ In v (program_vars p)) as Hp by (intro H; apply Hfresh; apply in_app_iff; auto).
  assert (~ In v (formula_vars a)) as Ha by (intro H; apply Hfresh; apply in_app_iff; auto).
  destruct Hce as [run [final [rest [Hrun [Hlast [Hrest Ho]]]]]].
  exists (map_history run), (map T final), (map_history rest); split.
  - apply execution_switch; assumption.
  - split; [rewrite last_map_history; exact (f_equal (map T) Hlast)|]. split; [apply IHa; assumption|].
    exact (overlap_list_map (map T) _ _ _ Ho).
Qed.

Lemma map_history_measure history : sequence_measure (map_history history) = sequence_measure history.
Proof.
  induction history; cbn [map_history map sequence_measure] in *; [reflexivity|].
  change (length (map T a) + sequence_measure (map_history history) = length a + sequence_measure history).
  rewrite length_map, IHhistory; reflexivity.
Qed.

Lemma measure_switch a tr n : ~ In v (formula_vars a) ->
  (measure_possible a (map T tr) n <-> measure_possible a tr n).
Proof.
  intro Hfresh; split; intros [history [Hce Hmeasure]]; exists (map_history history); split.
  - pose proof (counterexample_switch_forward a Hfresh _ _ Hce) as H.
    rewrite (map_involutive T HT tr) in H; exact H.
  - now rewrite map_history_measure.
  - apply counterexample_switch_forward; assumption.
  - now rewrite map_history_measure.
Qed.

End CounterSwitch.

Lemma minimum_switch v f (Hf : forall d, f (f d) = d) a tr : ~ In v (formula_vars a) ->
  minimum_counterexample a (map (switch M v f) tr) = minimum_counterexample a tr.
Proof. intro Hfresh; apply minimum_extensional; intro n; apply (measure_switch v f Hf); exact Hfresh. Qed.
End ForModel.
End MakeProgress.
