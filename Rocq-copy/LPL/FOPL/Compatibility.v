(** * Preservation against the frozen, import-only legacy oracle.
    Production modules never import LegacyReference. *)
From Stdlib Require Import List Bool Arith Lia Classical_Prop Logic.ClassicalDescription.
From CyclistRocq.LPL.FOPL Require Import Signature Semantics.
From CyclistRocq.LPL.FOPL.LegacyReference Require Import Progress.
From CyclistRocq.LPL Require Import Progress.
Import ListNotations.
Module MakeCompatibility (S : SIGNATURE).
Module OldRanks := CyclistRocq.LPL.FOPL.LegacyReference.Progress.MakeProgress S.
Module Old := OldRanks.Sem.
Module New := CyclistRocq.LPL.FOPL.Semantics.MakeSemantics S.
Module O := Old.Syn.
Module NF := New.Syn.
Module N := NF.Shared.
(* Pass the semantic module's canonical syntax path. Alias chains in module
   arguments lose inductive sharing in Rocq 9.1's independent checker. *)
Module NewRanks := CyclistRocq.LPL.Progress.MakeProgress New.Syn.Language New.Syn.Shared New.Shared.
Fixpoint translate_term (t : O.term) : NF.term := match t with
| O.Var x => NF.Var x | O.Fun f args => NF.Fun f (map translate_term args) end.
Fixpoint translate_formula (a : O.formula) : N.formula := match a with
| O.Truth => N.Truth | O.Falsity => N.Falsity
| O.Pred p args => NF.Pred p (map translate_term args)
| O.Equal a b => NF.Equal (translate_term a) (translate_term b)
| O.Neg a => N.Neg (translate_formula a)
| O.Conj a b => N.Conj (translate_formula a) (translate_formula b)
| O.Disj a b => N.Disj (translate_formula a) (translate_formula b)
| O.Impl a b => N.Impl (translate_formula a) (translate_formula b)
| O.All x a => N.Extension x (translate_formula a)
| O.Ex x a => N.Coextension x (translate_formula a)
| O.First a => N.First (translate_formula a)
| O.Suffix a b => N.Suffix (translate_formula a) (translate_formula b)
| O.DualSuffix a b => N.DualSuffix (translate_formula a) (translate_formula b)
| O.Box p a => N.Box (translate_program p) (translate_formula a)
| O.Diamond p a => N.Diamond (translate_program p) (translate_formula a) end
with translate_program (p : O.program) : N.program := match p with
| O.Assign x t => NF.Assign x (translate_term t) | O.Test a => N.Test (translate_formula a)
| O.Seq a b => N.Seq (translate_program a) (translate_program b)
| O.Choice a b => N.Choice (translate_program a) (translate_program b)
| O.Star a => N.Star (translate_program a) end.
Fixpoint translate_update (u : O.update) : NF.update := match u with
| O.Base x => NF.Base x
| O.AssignUpdate x t u => NF.AssignUpdate x (translate_term t) (translate_update u) end.
Fixpoint translate_label (l : O.label) : N.label := match l with
| O.Empty => N.Empty | O.StateLabel u => N.StateLabel (translate_update u)
| O.TraceLabel x => N.TraceLabel x | O.Join a b => N.Join (translate_label a) (translate_label b) end.
Definition translate_occurrence o := N.Occ (translate_label o.(O.occurrence_label))
  (translate_formula o.(O.occurrence_formula)) o.(O.occurrence_tag).
Definition translate_judgment j := N.Jdg (map translate_occurrence j.(O.antecedent)) (map translate_occurrence j.(O.succedent)).
Lemma translate_term_wfb t : NF.term_wfb (translate_term t) = O.term_wfb t.
Proof.
  revert t; fix IH 1; intro t; destruct t as [x|f args]; cbn [translate_term NF.term_wfb O.term_wfb]; [reflexivity|].
  rewrite length_map; f_equal; induction args as [|a args IHargs]; cbn; [reflexivity|]. now rewrite IH, IHargs.
Qed.
Lemma translate_terms_wfb args : forallb NF.term_wfb (map translate_term args) = forallb O.term_wfb args.
Proof. induction args; cbn; [reflexivity|]. now rewrite translate_term_wfb, IHargs. Qed.
Lemma translate_pureb a : N.pureb (translate_formula a) = O.pureb a.
Proof. induction a; cbn [NF.Pred NF.Equal N.Falsity N.Disj N.Impl N.Coextension N.DualSuffix N.Diamond translate_formula N.pureb O.pureb]; rewrite ?IHa, ?IHa1, ?IHa2; reflexivity. Qed.
Lemma translate_formula_program_wfb :
  (forall a, N.formula_wfb (translate_formula a) = O.formula_wfb a) /\
  (forall p, N.program_wfb (translate_program p) = O.program_wfb p).
Proof.
  apply O.formula_program_mutind; intros;
    cbn [NF.Pred NF.Equal NF.Assign N.Falsity N.Disj N.Impl N.Coextension N.DualSuffix N.Diamond translate_formula translate_program N.formula_wfb N.program_wfb O.formula_wfb O.program_wfb];
    unfold NF.Language.atom_wfb, NF.Language.atom_wfb, NF.Language.extension_wfb, NF.Language.extension_wfb, NF.Language.action_wfb;
    rewrite ?length_map, ?translate_terms_wfb, ?translate_term_wfb, ?translate_pureb; try congruence.
  cbn [N.pureb]; rewrite translate_pureb; congruence.
Qed.
Lemma translate_update_wfb u : NF.update_wfb (translate_update u) = O.update_wfb u.
Proof. induction u; cbn [translate_update NF.update_wfb O.update_wfb]; rewrite ?translate_term_wfb, ?IHu; reflexivity. Qed.
Lemma translate_label_wfb l : N.label_wfb (translate_label l) = O.label_wfb l.
Proof.
  induction l; cbn [translate_label N.label_wfb O.label_wfb]; unfold NF.Language.world_term_wfb;
    rewrite ?translate_update_wfb, ?IHl1, ?IHl2; reflexivity.
Qed.
Lemma translate_label_nonempty l : N.label_nonemptyb (translate_label l) = O.label_nonemptyb l.
Proof. induction l; cbn [translate_label N.label_nonemptyb O.label_nonemptyb]; congruence. Qed.
(** Primitive encodings collapse constructor distinctions. A legacy tag
    remains legal; the converse fails for an explicitly expanded dual. *)
Lemma translate_traceable a : O.traceableb a = true -> N.traceableb (translate_formula a) = true.
Proof. destruct a; cbn [O.traceableb]; intro H; discriminate || reflexivity. Qed.
Lemma translate_occurrence_wfb side o : O.occurrence_wfb side o = true ->
  N.occurrence_wfb side (translate_occurrence o) = true.
Proof.
  unfold N.occurrence_wfb, O.occurrence_wfb; cbn [translate_occurrence N.occurrence_label N.occurrence_formula N.occurrence_tag].
  rewrite translate_label_wfb, translate_label_nonempty, (proj1 translate_formula_program_wfb).
  destruct (O.occurrence_tag o); rewrite !andb_true_iff; intuition eauto using translate_traceable.
Qed.
Lemma translate_context_wfb side context : forallb (O.occurrence_wfb side) context = true ->
  forallb (N.occurrence_wfb side) (map translate_occurrence context) = true.
Proof. induction context; cbn; [auto|]. rewrite !andb_true_iff; intuition eauto using translate_occurrence_wfb. Qed.
Lemma translate_tags j : N.judgment_tags (translate_judgment j) = O.judgment_tags j.
Proof.
  unfold N.judgment_tags, O.judgment_tags, translate_judgment, N.Jdg; cbn [N.succedent].
  induction (O.succedent j) as [|o rest IH]; cbn [map flat_map translate_occurrence N.occurrence_tag]; [reflexivity|]. now rewrite IH.
Qed.
Theorem translate_judgment_wfb j : O.judgment_wfb j = true -> N.judgment_wfb (translate_judgment j) = true.
Proof.
  unfold N.judgment_wfb, O.judgment_wfb; rewrite translate_tags.
  cbn [translate_judgment N.Jdg N.relations N.antecedent N.succedent forallb].
  rewrite !andb_true_iff; intuition eauto using translate_context_wfb.
Qed.
Module ForModel (I : Old.INTERPRETATION).
Definition M := I.interpretation.
Definition translated_model := New.Model (Old.domain M) (Old.domain_inhabitant M) (Old.interpret_function M) (Old.interpret_predicate M).
Module NewModel <: New.Shared.INTERPRETATION.
  Definition interpretation := New.general_model translated_model.
End NewModel.
Module NR := NewRanks.ForModel NewModel.
Module OR := OldRanks.ForModel I.
Definition translate_world (w : Old.world M) : New.world translated_model :=
  New.World translated_model (Old.world_mapping M w) (Old.trace_mapping M w) (Old.trace_mapping_nonempty M w).
Definition untranslate_world (w : New.world translated_model) : Old.world M :=
  Old.World M (New.world_mapping translated_model w) (New.trace_mapping translated_model w) (New.trace_mapping_nonempty translated_model w).
Lemma world_roundtrip w : translate_world (untranslate_world w) = w.
Proof. destruct w; reflexivity. Qed.
Lemma translate_term_eval t : forall s, New.eval_term translated_model s (translate_term t) = Old.eval_term M s t.
Proof.
  revert t; fix IH 1; intro t; destruct t as [x|f args]; intro s;
    cbn [translate_term New.eval_term Old.eval_term translated_model New.interpret_function]; [reflexivity|].
  f_equal; rewrite map_map; induction args as [|a args IHargs]; [reflexivity|].
  change (New.eval_term translated_model s (translate_term a) ::
    map (fun t => New.eval_term translated_model s (translate_term t)) args =
    Old.eval_term M s a :: map (Old.eval_term M s) args).
  rewrite IH, IHargs; reflexivity.
Qed.
Lemma power_iff (R T : list (Old.state M) -> Prop) : (forall tr, R tr <-> T tr) -> forall n tr, Old.finite_power M R n tr <-> Old.finite_power M T n tr.
Proof.
  intros H n; induction n; intro tr; cbn [Old.finite_power]; [reflexivity|].
  unfold Old.compose; setoid_rewrite H; setoid_rewrite IHn; reflexivity.
Qed.
Theorem formula_program_semantics :
  (forall a tr, New.Shared.formula_holds (New.general_model translated_model) (translate_formula a) tr <-> Old.formula_holds M a tr) /\
  (forall p tr, New.Shared.program_holds (New.general_model translated_model) (translate_program p) tr <-> Old.program_holds M p tr).
Proof.
  apply O.formula_program_mutind.
  - intros [|s tail]; reflexivity.
  - intros [|s tail]; cbn; tauto.
  - intros p args [|s tail]; [reflexivity|].
    change (Old.interpret_predicate M p (map (New.eval_term translated_model s) (map translate_term args)) <-> Old.interpret_predicate M p (map (Old.eval_term M s) args)).
    rewrite map_map; assert (map (fun t => New.eval_term translated_model s (translate_term t)) args = map (Old.eval_term M s) args) as ->.
    { apply map_ext; intro t; apply translate_term_eval. } reflexivity.
  - intros a b [|s tail]; [reflexivity|].
    change (New.eval_term translated_model s (translate_term a) = New.eval_term translated_model s (translate_term b) <-> Old.eval_term M s a = Old.eval_term M s b).
    now rewrite !translate_term_eval.
  - intros a IH [|s tail]; [reflexivity|].
    change (~ New.Shared.formula_holds (New.general_model translated_model) (translate_formula a) (s::tail) <-> ~ Old.formula_holds M a (s::tail)); now rewrite IH.
  - intros a Ha b Hb [|s tail]; [reflexivity|]. cbn [translate_formula New.Shared.formula_holds Old.formula_holds]; rewrite Ha, Hb; reflexivity.
  - intros a Ha b Hb [|s tail]; [reflexivity|]. cbn [translate_formula]; rewrite New.Shared.nonempty_disj by discriminate.
    cbn [Old.formula_holds]; rewrite Ha, Hb; reflexivity.
  - intros a Ha b Hb [|s tail]; [reflexivity|]. cbn [translate_formula]; rewrite New.Shared.nonempty_impl by discriminate.
    cbn [Old.formula_holds]; rewrite Ha, Hb; reflexivity.
  - intros x a Ha [|s tail]; [reflexivity|].
    change ((forall value, New.Shared.formula_holds (New.general_model translated_model) (translate_formula a) (map (fun s => Old.write M s x value) (s::tail))) <-> forall value, Old.formula_holds M a (map (fun s => Old.write M s x value) (s::tail))).
    setoid_rewrite Ha; reflexivity.
  - intros x a Ha [|s tail]; [reflexivity|].
    change (~ (forall value, New.Shared.formula_holds (New.general_model translated_model) (N.Neg (translate_formula a))
      (map (fun s => Old.write M s x value) (s::tail))) <-> exists value, Old.formula_holds M a (map (fun s => Old.write M s x value) (s::tail))).
    assert (forall value, New.Shared.formula_holds (New.general_model translated_model) (N.Neg (translate_formula a))
      (map (fun s => Old.write M s x value) (s::tail)) <->
      ~ Old.formula_holds M a (map (fun s => Old.write M s x value) (s::tail))) as Heq.
    { intro value; rewrite New.Shared.nonempty_neg by discriminate; apply not_iff_compat, Ha. }
    setoid_rewrite Heq; split.
    + intro H; apply not_all_ex_not in H as [value H]; exists value; tauto.
    + intros [value H] Hall; exact (Hall value H).
  - intros a Ha [|s tail]; [reflexivity|]. apply Ha.
  - intros a Ha b Hb [|s tail]; [reflexivity|]. cbn [translate_formula New.Shared.formula_holds Old.formula_holds]; setoid_rewrite Ha; setoid_rewrite Hb; reflexivity.
  - intros a Ha b Hb [|s tail]; [reflexivity|].
    cbn [translate_formula]. rewrite New.Shared.dual_suffix_dual by discriminate.
    rewrite New.Shared.suffix_clause by discriminate; cbn [Old.formula_holds].
    assert (forall c tr, tr <> [] -> New.Shared.formula_holds (New.general_model translated_model) (N.Neg c) tr <->
      ~ New.Shared.formula_holds (New.general_model translated_model) c tr) as Hneg by (intros; apply New.Shared.nonempty_neg; assumption).
    split; intros H E; apply H; destruct E as [small [Hp [Hbody Hmiddle]]]; exists small; split; [exact Hp| |exact Hp|].
    + split; [apply Hneg; [exact (proj1 Hp)|rewrite Hb; exact Hbody]|].
      intros middle Hsm Hmt; apply Hneg; [exact (proj1 Hmt)|]. rewrite Ha; eauto.
    + split; [rewrite Hneg, Hb in Hbody by exact (proj1 Hp); exact Hbody|].
      intros middle Hsm Hmt; specialize (Hmiddle middle Hsm Hmt).
      rewrite Hneg, Ha in Hmiddle by exact (proj1 Hmt); exact Hmiddle.
  - intros p Hp a Ha [|s tail]; [reflexivity|]. cbn [translate_formula New.Shared.formula_holds Old.formula_holds]; setoid_rewrite Hp; setoid_rewrite Ha; reflexivity.
  - intros p Hp a Ha [|s tail]; [reflexivity|]. cbn [translate_formula]; rewrite New.Shared.diamond_clause by discriminate.
    cbn [Old.formula_holds]; setoid_rewrite Hp; setoid_rewrite Ha; reflexivity.
  - intros x t tr.
    change ((exists s, tr=[s;New.write translated_model s x (New.eval_term translated_model s (translate_term t))]) <-> exists s, tr=[s;Old.write M s x (Old.eval_term M s t)]).
    setoid_rewrite translate_term_eval; reflexivity.
  - intros a Ha tr. cbn [translate_program New.Shared.program_holds Old.program_holds]; setoid_rewrite Ha; reflexivity.
  - intros a Ha b Hb tr. cbn [translate_program New.Shared.program_holds Old.program_holds]; unfold New.Shared.compose, CyclistRocq.LPL.Semantics.TraceAlgebra.trace_compose, Old.compose; setoid_rewrite Ha; setoid_rewrite Hb; reflexivity.
  - intros a Ha b Hb tr. cbn [translate_program New.Shared.program_holds Old.program_holds]; rewrite Ha, Hb; reflexivity.
  - intros a Ha tr.
    change ((exists n, Old.finite_power M (New.Shared.program_holds (New.general_model translated_model) (translate_program a)) n tr) <-> exists n, Old.finite_power M (Old.program_holds M a) n tr).
    split; intros [n H]; exists n; [apply (proj1 (power_iff _ _ Ha n tr))|apply (proj2 (power_iff _ _ Ha n tr))]; exact H.
Qed.

Lemma update_evaluation u : forall w,
  New.eval_world_term translated_model (Old.world_mapping M w) (translate_update u) = Old.eval_update M w u.
Proof.
  induction u; intro w; cbn [translate_update New.eval_world_term Old.eval_update]; [reflexivity|].
  rewrite IHu, translate_term_eval; reflexivity.
Qed.
Lemma translate_update_eval u w :
  New.eval_update translated_model (translate_world w) (translate_update u) = Old.eval_update M w u.
Proof. apply update_evaluation. Qed.
Lemma translate_label_eval l : forall w,
  New.Shared.eval_label (New.general_model translated_model) (translate_world w) (translate_label l) = Old.eval_label M w l.
Proof.
  induction l; intro w; cbn [translate_label New.Shared.eval_label Old.eval_label]; try reflexivity.
  - change ([New.eval_update translated_model (translate_world w) (translate_update u)] = [Old.eval_update M w u]); now rewrite translate_update_eval.
  - now rewrite IHl1, IHl2.
Qed.
Lemma labelled_semantics o w :
  New.labelled_holds translated_model (translate_world w) (translate_occurrence o) <-> Old.labelled_holds M w o.
Proof.
  unfold New.labelled_holds, New.Shared.labelled_holds, Old.labelled_holds,
    New.Shared.label_admissible, Old.label_admissible.
  cbn [translate_occurrence N.occurrence_label N.occurrence_formula].
  rewrite !translate_label_eval, (proj1 formula_program_semantics); reflexivity.
Qed.
Lemma context_admissibility context w :
  Forall (fun o => New.Shared.label_admissible (New.general_model translated_model) (translate_world w) (N.occurrence_label o)) (map translate_occurrence context) <->
  Forall (fun o => Old.label_admissible M w (O.occurrence_label o)) context.
Proof.
  rewrite Forall_map, !Forall_forall.
  unfold New.Shared.label_admissible, Old.label_admissible; cbn [translate_occurrence N.occurrence_label].
  setoid_rewrite translate_label_eval; reflexivity.
Qed.
Theorem admissibility_preserved j w :
  New.admissible translated_model (translate_judgment j) (translate_world w) <-> Old.admissible M j w.
Proof.
  unfold New.admissible, New.Shared.admissible, Old.admissible.
  cbn [translate_judgment N.Jdg N.antecedent N.succedent N.relations].
  rewrite <- map_app, context_admissibility.
  split; [tauto|intro H; split; [exact H|constructor]].
Qed.
Lemma left_context_semantics context w :
  New.left_holds translated_model (translate_world w) (map translate_occurrence context) <-> Old.left_holds M w context.
Proof.
  unfold New.left_holds, New.Shared.left_holds, Old.left_holds; rewrite Forall_map, !Forall_forall.
  setoid_rewrite labelled_semantics; reflexivity.
Qed.
Lemma right_context_semantics context w :
  New.right_holds translated_model (translate_world w) (map translate_occurrence context) <-> Old.right_holds M w context.
Proof.
  unfold New.right_holds, New.Shared.right_holds, Old.right_holds; setoid_rewrite in_map_iff; split.
  - intros [o [[original [Heq Hin]] Hholds]]; subst o; exists original; split; [exact Hin|apply labelled_semantics; exact Hholds].
  - intros [o [Hin Hholds]]; exists (translate_occurrence o); split; [exists o; auto|apply labelled_semantics; exact Hholds].
Qed.
Theorem denotation_preserved j w :
  New.denote translated_model (translate_judgment j) (translate_world w) <-> Old.denote M j w.
Proof.
  change ((New.admissible translated_model (translate_judgment j) (translate_world w) ->
    New.relations_hold translated_model (translate_world w) [] ->
    New.left_holds translated_model (translate_world w) (map translate_occurrence j.(O.antecedent)) ->
    New.right_holds translated_model (translate_world w) (map translate_occurrence j.(O.succedent))) <-> Old.denote M j w).
  rewrite admissibility_preserved, left_context_semantics, right_context_semantics.
  assert (New.relations_hold translated_model (translate_world w) []) as Hrel by constructor.
  unfold Old.denote; tauto.
Qed.
Theorem validity_preserved j : New.Valid translated_model (translate_judgment j) <-> Old.Valid M j.
Proof.
  split; intros H w.
  - apply (proj1 (denotation_preserved j w)); apply H.
  - rewrite <- (world_roundtrip w); apply (proj2 (denotation_preserved j (untranslate_world w))); apply H.
Qed.

Lemma execution_sequences_preserved p tr history :
  NR.execution_sequence tr (translate_program p) history <-> OR.execution_sequence tr p history.
Proof.
  unfold NR.execution_sequence, OR.execution_sequence.
  setoid_rewrite (proj2 formula_program_semantics); reflexivity.
Qed.
Theorem counterexamples_preserved a : forall tr history,
  NR.counterexample (translate_formula a) tr history <-> OR.counterexample a tr history.
Proof.
  induction a; intros tr history;
    match goal with |- NR.counterexample (translate_formula ?a) _ _ <-> _ =>
      pose proof (proj1 formula_program_semantics a tr) as Hsem end;
    cbn [NF.Pred NF.Equal N.Falsity N.Disj N.Impl N.Coextension N.DualSuffix N.Diamond translate_formula NR.counterexample OR.counterexample]; try (rewrite Hsem; reflexivity).
  setoid_rewrite execution_sequences_preserved; setoid_rewrite IHa; reflexivity.
Qed.
Lemma measures_preserved a tr n :
  NR.measure_possible (translate_formula a) tr n <-> OR.measure_possible a tr n.
Proof. unfold NR.measure_possible, OR.measure_possible; setoid_rewrite counterexamples_preserved; reflexivity. Qed.
Theorem minima_preserved a tr :
  NR.minimum_counterexample (translate_formula a) tr = OR.minimum_counterexample a tr.
Proof.
  destruct (classic (exists n, NR.measure_possible (translate_formula a) tr n)) as [Hnew|Hnone].
  - assert (exists n, OR.measure_possible a tr n) as Hold by (destruct Hnew as [n H]; exists n; apply measures_preserved; exact H).
    destruct (NR.minimum_spec _ _ Hnew) as [Hn Hnle].
    destruct (OR.minimum_spec _ _ Hold) as [Ho Hole].
    pose proof (Hnle _ (proj2 (measures_preserved _ _ _) Ho)).
    pose proof (Hole _ (proj1 (measures_preserved _ _ _) Hn)); lia.
  - assert (~ exists n, OR.measure_possible a tr n) as Hold.
    { intros [n H]; apply Hnone; exists n; apply measures_preserved; exact H. }
    unfold NR.minimum_counterexample, OR.minimum_counterexample.
    destruct (excluded_middle_informative (exists n, NR.measure_possible (translate_formula a) tr n)); [contradiction|].
    destruct (excluded_middle_informative (exists n, OR.measure_possible a tr n)); [contradiction|reflexivity].
Qed.
Theorem occurrence_ranks_preserved o w :
  NR.occurrence_rank (translate_occurrence o) (translate_world w) = OR.occurrence_rank o w.
Proof.
  unfold NR.occurrence_rank, OR.occurrence_rank; cbn [translate_occurrence N.occurrence_label N.occurrence_formula].
  rewrite translate_label_eval; apply minima_preserved.
Qed.
Theorem context_ranks_preserved context w tag :
  NR.rank_in_context (map translate_occurrence context) (translate_world w) tag = OR.rank_in_context context w tag.
Proof.
  induction context as [|o context IH]; cbn [map NR.rank_in_context OR.rank_in_context translate_occurrence N.occurrence_tag]; [reflexivity|].
  destruct (O.occurrence_tag o) as [t|]; [destruct (Nat.eqb tag t)|]; try exact IH.
  apply occurrence_ranks_preserved.
Qed.
Print Assumptions formula_program_semantics.
Print Assumptions validity_preserved.
Print Assumptions context_ranks_preserved.

End ForModel.
End MakeCompatibility.
