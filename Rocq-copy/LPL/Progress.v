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
From CyclistRocq.LPL Require Import Signature Syntax Semantics.
From CyclistRocq.Cyclic Require Import Framework.
Import ListNotations.

Module MakeProgress (L : LANGUAGE) (Syn : SYNTAX L) (Sem : SEMANTICS L Syn).
Export Syn Sem.
(** Fix an interpretation once so that ranks and the cyclic framework use
    the very same model. The outer functor shares the existing syntax and
    semantics modules; [ForModel] supplies their remaining model parameter. *)
Module ForModel (I : Sem.INTERPRETATION).
Definition M := I.interpretation.
Definition trace := Sem.trace M.

(** [execution_history prefix rest] includes the initial prefix and each
    subsequent accumulated trace. Its measure is the SUM of their lengths,
    never merely the number of transitions. For example, prefix [[s]] and
    rest [[t;u]] produce [[[s];[s;t];[s;t;u]]], with measure [1+2+3]. *)
Fixpoint execution_history (prefix rest : trace) : list trace :=
  prefix :: match rest with
    | [] => []
    | s :: tail => execution_history (prefix ++ [s]) tail
    end.

(** Record the successive accumulated prefixes produced by one execution
    that starts at the current trace's last state. [rest <> []] ensures an
    actual transition, including the stutters of tests and zero iterations. *)
Definition execution_sequence (tr : trace) (p : program) (history : list trace) : Prop :=
  exists s rest result, program_holds M p (s :: rest) /\
    rest <> [] /\ overlap M tr (s :: rest) result /\
    history = execution_history tr rest.

(** A box fails through an execution and a failing body. Join their histories
    by overlapping the shared final trace once; this use of [overlap_list]
    is at the level of lists of traces, not labels. For any non-box formula,
    failure is represented by the singleton history containing its trace. *)
Fixpoint counterexample (a : formula) (tr : trace) (history : list trace) : Prop :=
  match a with
  | Box p body => exists run final_run rest,
      execution_sequence tr p run /\
      last run [] = final_run /\
      counterexample body final_run rest /\ overlap_list run rest history
  | _ => ~ formula_holds M a tr /\ history = [tr]
  end.

Definition sequence_measure (history : list trace) : nat :=
  fold_right (fun tr n => length tr + n) 0 history.

(** Collect attainable measures as a predicate on natural numbers. Keeping
    the actual history existential lets the minimum range over arbitrarily
    many executions without requiring a list of all possible executions. *)
Definition measure_possible a tr n :=
  exists history, counterexample a tr history /\ sequence_measure history = n.

(** Classical existence checks and the standard least-number construction
    give a mathematical minimum in [nat], even if a program has infinitely
    many executions. The fallback 0 is confined to empty counterexample sets.
    [minimum_spec] supplies both attainment and minimality when a witness
    exists; later false-trace lemmas always establish that existence first. *)
Definition minimum_counterexample a tr : nat :=
  match excluded_middle_informative (exists n, measure_possible a tr n) with
  | left H => proj1_sig (epsilon_smallest (measure_possible a tr)
      (fun n => excluded_middle_informative (measure_possible a tr n)) H)
  | right _ => 0
  end.

Lemma minimum_spec a tr : (exists n, measure_possible a tr n) ->
  measure_possible a tr (minimum_counterexample a tr) /\
  forall n, measure_possible a tr n -> minimum_counterexample a tr <= n.
Proof.
  intro H. unfold minimum_counterexample.
  destruct (excluded_middle_informative (exists n, measure_possible a tr n)) as [Hex|Hno]; [|contradiction].
  destruct (epsilon_smallest (measure_possible a tr)
    (fun n => excluded_middle_informative (measure_possible a tr n)) Hex) as [n [Hn Hmin]].
  cbn. auto.
Qed.

Lemma execution_history_last prefix rest :
  last (execution_history prefix rest) [] = prefix ++ rest.
Proof.
  revert prefix. induction rest as [|s rest IH]; intro prefix.
  - cbn; now rewrite app_nil_r.
  - change (last (prefix :: execution_history (prefix ++ [s]) rest) [] = prefix ++ s :: rest).
    assert (exists tail, execution_history (prefix ++ [s]) rest = (prefix ++ [s]) :: tail) as Hex.
    { destruct rest; eexists; reflexivity. }
    destruct Hex as [tail Heq].
    rewrite Heq. change (last ((prefix ++ [s]) :: tail) [] = prefix ++ s :: rest).
    rewrite <- Heq, IH, <- app_assoc. reflexivity.
Qed.

Lemma execution_history_head prefix rest :
  exists tail, execution_history prefix rest = prefix :: tail.
Proof. destruct rest; eexists; reflexivity. Qed.

(** The last accumulated prefix is exactly a semantic execution result.
    This connects the explicit history representation to the overlap
    relation used by the box clause in Semantics.v. *)
Lemma execution_history_result tr p history :
  execution_sequence tr p history ->
  exists execution, program_holds M p execution /\ overlap M tr execution (last history []).
Proof.
  intros [s [rest [result [Hp [_ [Ho ->]]]]]].
  exists (s :: rest); split; [exact Hp|]. rewrite execution_history_last.
  destruct Ho as [prefix [s' [tail [Htr [Heq _]]]]].
  inversion Heq; subst. unfold overlap, overlap_list.
  exists prefix, s', tail. repeat split; auto. rewrite <- app_assoc. reflexivity.
Qed.

(** A counterexample history always starts with the trace it refutes.
    This is the boundary fact that lets a box execution history overlap
    its body's counterexample at one shared accumulated trace. *)
Lemma counterexample_head a tr history : counterexample a tr history ->
  exists tail, history = tr :: tail.
Proof.
  revert tr history. induction a; intros tr history H; cbn [counterexample] in H;
    try (destruct H as [_ ->]; exists []; reflexivity).
  destruct H as [run [final [rest [Hrun [Hfinal [Hrest Ho]]]]]].
  destruct Hrun as [s [tail [result [_ [_ [_ Hrun]]]]]]; subst run.
  destruct (execution_history_head tr tail) as [run_tail Hrun].
  destruct Ho as [prefix [endtr [rest_tail [Hleft [_ ->]]]]].
  rewrite Hrun in Hleft. destruct prefix as [|first prefix].
  - cbn in Hleft; inversion Hleft; subst. exists rest_tail; reflexivity.
  - cbn in Hleft; inversion Hleft; subst. eexists; reflexivity.
Qed.

(** These two directions connect histories back to truth: a counterexample
    refutes the formula, and a false formula on a nonempty trace has a
    counterexample. Their proofs recurse through boxes rather than assuming
    that every semantic failure has already been supplied as finite data. *)
Lemma counterexample_false a tr history : tr <> [] ->
  counterexample a tr history -> ~ formula_holds M a tr.
Proof.
  revert tr history. induction a; intros tr history Hne Hce;
    cbn [counterexample] in Hce; try tauto.
  destruct Hce as [run [final [rest [Hrun [Hfinal [Hrest _]]]]]].
  destruct (execution_history_result _ _ _ Hrun) as [execution [Hp Ho]].
  rewrite Hfinal in Ho.
  destruct (overlap_nonempty M _ _ _ Ho) as [_ [_ Hfinal_ne]].
  pose proof (IHa final rest Hfinal_ne Hrest) as Hbad.
  destruct tr as [|s tail]; [contradiction|]. cbn [formula_holds].
  intro H; apply Hbad; eapply H; eauto.
Qed.

Lemma list_split_last {A : Type} (xs : list A) default : xs <> [] ->
  exists prefix, xs = prefix ++ [last xs default].
Proof.
  induction xs as [|x xs IH]; intro Hne; [contradiction|].
  destruct xs as [|y xs].
  - exists []; reflexivity.
  - destruct (IH ltac:(discriminate)) as [prefix Hp].
    exists (x :: prefix). cbn in *; now rewrite <- Hp.
Qed.

(** For a false box, extract a failing execution from its universal meaning,
    recurse on the body, and overlap its counterexample with the execution
    history. [program_length] supplies the nonempty sequence of steps. *)
Lemma counterexample_exists a tr : tr <> [] -> ~ formula_holds M a tr ->
  exists history, counterexample a tr history.
Proof.
  revert tr. induction a; intros tr Hne Hfalse;
    try solve [exists [tr]; cbn [counterexample]; auto].
  destruct tr as [|s tail]; [contradiction|].
  cbn [formula_holds] in Hfalse.
  apply not_all_ex_not in Hfalse as [execution Hfalse].
  apply not_all_ex_not in Hfalse as [result Hfalse].
  assert (program_holds M p execution /\ overlap M (s :: tail) execution result /\
    ~ formula_holds M a result) as [Hp [Ho Hbad]] by tauto.
  destruct (overlap_nonempty M _ _ _ Ho) as [_ [_ Hresult]].
  destruct (IHa result Hresult Hbad) as [rest Hrest].
  destruct (counterexample_head a result rest Hrest) as [rest_tail Hhead].
  pose proof (program_length M p execution Hp) as Hlength.
  destruct execution as [|start steps]; cbn in Hlength; [lia|].
  assert (steps <> []) as Hsteps by (intro Heq; subst; cbn in Hlength; lia).
  set (run := execution_history (s :: tail) steps).
  assert (last run [] = result) as Hlast.
  { unfold run; rewrite execution_history_last.
    destruct Ho as [prefix [lasts [reststeps [Htr [Hexec Hresult_eq]]]]].
    inversion Hexec; subst. rewrite Htr, <- app_assoc. reflexivity. }
  assert (run <> []) as Hrun_ne by (unfold run; destruct steps; discriminate).
  destruct (list_split_last run [] Hrun_ne) as [prefix Hprefix].
  rewrite Hlast in Hprefix.
  exists (prefix ++ result :: rest_tail).
  cbn [counterexample]. exists run, result, rest.
  split.
  - exists start, steps, result. auto.
  - split; [exact Hlast|]. split; [exact Hrest|].
    exists prefix, result, rest_tail. auto.
Qed.

Lemma false_minimum_exists a tr : tr <> [] -> ~ formula_holds M a tr ->
  exists n, measure_possible a tr n.
Proof.
  intros Hne Hfalse; destruct (counterexample_exists a tr Hne Hfalse) as [history Hce].
  exists (sequence_measure history), history; auto.
Qed.

(** Non-box counterexamples have exactly one component, so their minimum is
    the length of that trace. Suffix descent will use this simple case. *)
Lemma nonbox_minimum a tr :
  (forall p b, a <> Box p b) -> tr <> [] -> ~ formula_holds M a tr ->
  minimum_counterexample a tr = length tr.
Proof.
  intros Hshape Hne Hfalse.
  destruct (minimum_spec a tr (false_minimum_exists a tr Hne Hfalse)) as [Hmin Hleast].
  destruct Hmin as [history [Hce Hmeasure]].
  destruct a; cbn [counterexample] in Hce; try (destruct Hce as [_ ->]; cbn in Hmeasure; lia).
  exfalso; eapply Hshape; reflexivity.
Qed.

Lemma test_execution prefix s guard run :
  execution_sequence (prefix ++ [s]) (Test guard) run <->
  formula_holds M guard [s;s] /\ run = [prefix ++ [s]; (prefix ++ [s]) ++ [s]].
Proof.
  split.
  - intros [start [steps [result [[initial [Heq Hg]] [_ [Ho Hrun]]]]]].
    inversion Heq; subst start steps. apply overlap_snoc in Ho as [-> ->].
    split; [exact Hg|]. rewrite Hrun; reflexivity.
  - intros [Hg Hrun]. exists s, [s], ((prefix ++ [s]) ++ [s]).
    split; [exists s; auto|]. split; [discriminate|].
    split; [apply overlap_snoc; auto|exact Hrun].
Qed.

(** In this helper, "atomic" means a uniquely specified one-step history
    under condition [G]. It applies to tests; arbitrary nondeterministic
    atomic programs use [atomic_minimum_successor] below instead. *)
Lemma atomic_counterexample p tr next (G : Prop) body history :
  (forall run, execution_sequence tr p run <-> G /\ run = [tr;next]) ->
  (counterexample (Box p body) tr history <->
    G /\ exists rest, counterexample body next rest /\ history = tr :: rest).
Proof.
  intro Hstep; cbn [counterexample]; split.
  - intros [run [final [rest [Hrun [Hlast [Hce Ho]]]]]].
    apply Hstep in Hrun as [HG ->]. cbn in Hlast; subst final.
    destruct (counterexample_head _ _ _ Hce) as [tail Hrest].
    split; [exact HG|]. exists rest; split; [exact Hce|].
    rewrite Hrest in Ho. change (overlap_list ([tr] ++ [next]) (next :: tail) history) in Ho.
    apply overlap_list_snoc in Ho as [_ ->]. now rewrite Hrest.
  - intros [HG [rest [Hce ->]]].
    exists [tr;next], next, rest; split; [apply Hstep; auto|].
    split; [reflexivity|]. split; [exact Hce|].
    destruct (counterexample_head _ _ _ Hce) as [tail ->].
    exists [tr], next, tail; auto.
Qed.

(** Factor the unique-step case once. A box counterexample contributes
    [length tr] plus the body's counterexample measure at [next]. To prove
    equality of minima, compare an attained source minimum with an attained
    body minimum in both directions; an upper bound alone would not suffice. *)
Lemma atomic_minimum p tr next (G : Prop) body :
  tr <> [] -> next <> [] ->
  (forall run, execution_sequence tr p run <-> G /\ run = [tr;next]) ->
  ~ formula_holds M (Box p body) tr ->
  G /\ ~ formula_holds M body next /\
  minimum_counterexample (Box p body) tr = length tr + minimum_counterexample body next.
Proof.
  intros Htr Hnext Hstep Hfalse.
  pose proof (minimum_spec _ _ (false_minimum_exists _ _ Htr Hfalse)) as [Hsource Hsource_least].
  destruct Hsource as [source_history [Hce Hmeasure]].
  apply (atomic_counterexample p tr next G body source_history Hstep) in Hce as [HG [rest [Hrest ->]]].
  pose proof (counterexample_false body next rest Hnext Hrest) as Hbad.
  pose proof (minimum_spec _ _ (false_minimum_exists _ _ Hnext Hbad)) as [Htarget Htarget_least].
  destruct Htarget as [target_history [Htarget Htarget_measure]].
  split; [exact HG|]; split; [exact Hbad|].
  assert (minimum_counterexample body next <= sequence_measure rest) as Hlower.
  { apply Htarget_least; exists rest; auto. }
  assert (minimum_counterexample (Box p body) tr <= length tr + minimum_counterexample body next) as Hupper.
  { apply Hsource_least; exists (tr :: target_history); split.
    - apply (atomic_counterexample p tr next G body _ Hstep); eauto.
    - change (length tr + sequence_measure target_history = length tr + minimum_counterexample body next). now rewrite Htarget_measure. }
  change (length tr + sequence_measure rest = minimum_counterexample (Box p body) tr) in Hmeasure. lia.
Qed.

Lemma test_decrease prefix s guard body :
  ~ formula_holds M (Box (Test guard) body) (prefix ++ [s]) ->
  minimum_counterexample body ((prefix ++ [s]) ++ [s]) <
  minimum_counterexample (Box (Test guard) body) (prefix ++ [s]).
Proof.
  intro Hfalse.
  assert (prefix ++ [s] <> []) as Htr by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  assert ((prefix ++ [s]) ++ [s] <> []) as Hnext
    by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  destruct (atomic_minimum (Test guard) (prefix ++ [s]) ((prefix ++ [s]) ++ [s])
    (formula_holds M guard [s;s]) body Htr Hnext (test_execution prefix s guard) Hfalse) as [_ [_ Hrank]].
  destruct prefix; cbn in *; lia.
Qed.

(** Regrouping sequence executions preserves the entire accumulated history.
    The shared middle trace is overlapped once, so nesting two boxes neither
    duplicates that history component nor changes its summed measure. *)
Lemma execution_history_concat tr first second :
  overlap_list (execution_history tr first) (execution_history (tr ++ first) second)
    (execution_history tr (first ++ second)).
Proof.
  revert tr; induction first as [|s first IH]; intro tr.
  - cbn [app execution_history]. rewrite app_nil_r.
    apply overlap_list_singleton. destruct second; eexists; split; reflexivity.
  - change (overlap_list
      (tr :: execution_history (tr ++ [s]) first)
      (execution_history (tr ++ s :: first) second)
      (tr :: execution_history (tr ++ [s]) (first ++ second))).
    apply overlap_list_cons.
    + destruct first; discriminate.
    + eexists; split; [reflexivity|].
      replace (tr ++ s :: first) with ((tr ++ [s]) ++ first) by (rewrite <- app_assoc; reflexivity).
      exact (IH (tr ++ [s])).
Qed.

Lemma execution_sequence_seq tr a b run : execution_sequence tr (Seq a b) run ->
  exists first middle second,
    execution_sequence tr a first /\ last first [] = middle /\
    execution_sequence middle b second /\ overlap_list first second run.
Proof.
  intros [start [steps [result [Hprogram [Hsteps [Ho Hrun]]]]]].
  destruct Hprogram as [execA [execB [Ha [Hb Hexec]]]].
  assert (exists middle, overlap_list tr execA middle /\ overlap_list middle execB result) as Hmiddle.
  { apply overlap_list_assoc. exists (start :: steps); auto. }
  destruct Hmiddle as [middle [HoA HoB]].
  pose proof (program_length M a execA Ha) as HlenA.
  pose proof (program_length M b execB Hb) as HlenB.
  pose proof (overlap_list_append _ _ _ HoA) as Hmiddle_eq.
  pose proof (overlap_list_append _ _ _ Hexec) as Hexec_eq.
  destruct execA as [|startA tailA]; cbn in HlenA; [lia|].
  destruct execB as [|startB tailB]; cbn in HlenB; [lia|].
  assert (tailA <> []) as HtailA by (intro H; subst; cbn in HlenA; lia).
  assert (tailB <> []) as HtailB by (intro H; subst; cbn in HlenB; lia).
  cbn in Hmiddle_eq, Hexec_eq. inversion Hexec_eq; subst start steps.
  exists (execution_history tr tailA), middle, (execution_history middle tailB).
  split; [exists startA, tailA, middle; auto|].
  split; [rewrite execution_history_last; symmetry; exact Hmiddle_eq|].
  split; [exists startB, tailB, result; auto|].
  rewrite Hrun, Hmiddle_eq. apply execution_history_concat.
Qed.

Lemma counterexample_sequence tr a b body history :
  counterexample (Box (Seq a b) body) tr history ->
  counterexample (Box a (Box b body)) tr history.
Proof.
  cbn [counterexample].
  intros [run [final [rest [Hrun [Hfinal [Hrest Ho]]]]]].
  destruct (execution_sequence_seq tr a b run Hrun) as [first [middle [second [Ha [Hmiddle [Hb Hjoin]]]]]].
  assert (last second [] = final) as Hlast.
  { transitivity (last run []); [symmetry; exact (overlap_list_last _ _ _ [] Hjoin)|exact Hfinal]. }
  assert (exists combined, overlap_list second rest combined /\ overlap_list first combined history) as Hcombined.
  { apply overlap_list_assoc. exists run; auto. }
  destruct Hcombined as [combined [Hsecond Hfirst]].
  exists first, middle, combined; split; [exact Ha|]. split; [exact Hmiddle|].
  split; [exists second, final, rest; auto|exact Hfirst].
Qed.

(** A measure-preserving map of counterexample witnesses gives nonincrease
    of minima: transport an attained source minimum, then bound the target
    minimum by that particular witness. *)
Lemma minimum_transport a b tr : tr <> [] -> ~ formula_holds M a tr ->
  (forall history, counterexample a tr history -> counterexample b tr history) ->
  ~ formula_holds M b tr /\ minimum_counterexample b tr <= minimum_counterexample a tr.
Proof.
  intros Hne Hfalse Hmap.
  destruct (minimum_spec _ _ (false_minimum_exists _ _ Hne Hfalse)) as [[history [Hce Hmeasure]] _].
  apply Hmap in Hce. pose proof (counterexample_false _ _ _ Hne Hce) as Hbad.
  split; [exact Hbad|].
  destruct (minimum_spec _ _ (false_minimum_exists _ _ Hne Hbad)) as [_ Hmin].
  apply Hmin; exists history; auto.
Qed.

Lemma sequence_nonincrease tr a b body : tr <> [] ->
  ~ formula_holds M (Box (Seq a b) body) tr ->
  ~ formula_holds M (Box a (Box b body)) tr /\
  minimum_counterexample (Box a (Box b body)) tr <= minimum_counterexample (Box (Seq a b) body) tr.
Proof. intros Hne Hfalse; eapply minimum_transport; eauto using counterexample_sequence. Qed.

Lemma counterexample_choice tr a b body history :
  counterexample (Box (Choice a b) body) tr history ->
  counterexample (Box a body) tr history \/ counterexample (Box b body) tr history.
Proof.
  cbn [counterexample]; intros [run [final [rest [Hrun [Hlast [Hrest Ho]]]]]].
  destruct Hrun as [s [steps [result [[Ha|Hb] [Hsteps [Hover Hhistory]]]]]];
    [left|right]; exists run, final, rest; split;
    try (exists s, steps, result; auto); auto.
Qed.

(** Choose a branch from a minimum source counterexample. Picking merely any
    false branch could give a larger minimum. Rules.v uses this joint result
    (branch falsity and its rank bound) to select one premise for an edge. *)
Lemma choice_nonincrease tr a b body : tr <> [] ->
  ~ formula_holds M (Box (Choice a b) body) tr ->
  (~ formula_holds M (Box a body) tr /\
    minimum_counterexample (Box a body) tr <= minimum_counterexample (Box (Choice a b) body) tr) \/
  (~ formula_holds M (Box b body) tr /\
    minimum_counterexample (Box b body) tr <= minimum_counterexample (Box (Choice a b) body) tr).
Proof.
  intros Hne Hfalse.
  destruct (minimum_spec _ _ (false_minimum_exists _ _ Hne Hfalse)) as [[history [Hce Hmeasure]] _].
  apply counterexample_choice in Hce as [Ha|Hb]; [left|right].
  - pose proof (counterexample_false _ _ _ Hne Ha) as HbadA; split; [exact HbadA|].
    destruct (minimum_spec _ _ (false_minimum_exists _ _ Hne HbadA)) as [_ Hmin].
    apply Hmin; exists history; auto.
  - pose proof (counterexample_false _ _ _ Hne Hb) as HbadB; split; [exact HbadB|].
    destruct (minimum_spec _ _ (false_minimum_exists _ _ Hne HbadB)) as [_ Hmin].
    apply Hmin; exists history; auto.
Qed.

(** Split the finite iteration count into zero and successor cases. Zero
    becomes [Test Truth]; a successor becomes one body execution followed by
    the remaining star. Unfolding itself claims no strict progress. *)
Lemma counterexample_star tr a body history :
  counterexample (Box (Star a) body) tr history ->
  counterexample (Box (Test Truth) body) tr history \/
  counterexample (Box a (Box (Star a) body)) tr history.
Proof.
  cbn [counterexample]; intros [run [final [rest [Hrun [Hlast [Hrest Ho]]]]]].
  destruct Hrun as [s [steps [result [[n Hn] [Hsteps [Hover Hhistory]]]]]].
  destruct n.
  - left; exists run, final, rest; split; [|auto].
    exists s, steps, result; split; [|auto].
    destruct Hn as [start Htrace]. exists start; split; [exact Htrace|exact I].
  - right. apply counterexample_sequence. cbn [counterexample].
    exists run, final, rest; split; [|auto].
    exists s, steps, result; split; [|auto].
    destruct Hn as [first [second [Ha [Hn Hex]]]].
    exists first, second; split; [exact Ha|]. split; [exists n; exact Hn|exact Hex].
Qed.

Lemma star_nonincrease tr a body : tr <> [] ->
  ~ formula_holds M (Box (Star a) body) tr ->
  (~ formula_holds M (Box (Test Truth) body) tr /\
    minimum_counterexample (Box (Test Truth) body) tr <= minimum_counterexample (Box (Star a) body) tr) \/
  (~ formula_holds M (Box a (Box (Star a) body)) tr /\
    minimum_counterexample (Box a (Box (Star a) body)) tr <= minimum_counterexample (Box (Star a) body) tr).
Proof.
  intros Hne Hfalse.
  destruct (minimum_spec _ _ (false_minimum_exists _ _ Hne Hfalse)) as [[history [Hce Hmeasure]] _].
  apply counterexample_star in Hce as [Hce|Hce]; [left|right];
    pose proof (counterexample_false _ _ _ Hne Hce) as Hbad;
    split; [exact Hbad| |exact Hbad|];
    destruct (minimum_spec _ _ (false_minimum_exists _ _ Hne Hbad)) as [_ Hmin];
    apply Hmin; exists history; auto.
Qed.

(** Continuing suffix obligations are non-box formulas. Both false ranks
    therefore equal their trace lengths, and removing one head state is a
    strict decrease. The caller must prove that the continuation is actually
    present and false on the chosen premise; the first suffix-right branch
    has no such recursive continuation. *)
Lemma suffix_decrease s tail a b : tail <> [] ->
  ~ formula_holds M (Suffix a b) (s :: tail) ->
  ~ formula_holds M (Suffix a b) tail ->
  minimum_counterexample (Suffix a b) tail < minimum_counterexample (Suffix a b) (s :: tail).
Proof.
  intros Hne Hwhole Htail. rewrite !nonbox_minimum; try assumption; try discriminate.
  cbn; lia.
Qed.

Lemma dual_suffix_decrease s tail a b : tail <> [] ->
  ~ formula_holds M (DualSuffix a b) (s :: tail) ->
  ~ formula_holds M (DualSuffix a b) tail ->
  minimum_counterexample (DualSuffix a b) tail < minimum_counterexample (DualSuffix a b) (s :: tail).
Proof.
  intros Hne Hwhole Htail. rewrite !nonbox_minimum; try assumption; try discriminate.
  cbn; lia.
Qed.

(** Equal sets of attainable measures have equal minima, including the
    empty-set fallback. This compares measures only; histories themselves
    need not have equal syntax or equal state lists. *)
Lemma minimum_extensional a tr b tr' :
  (forall n, measure_possible a tr n <-> measure_possible b tr' n) ->
  minimum_counterexample a tr = minimum_counterexample b tr'.
Proof.
  intro Heq; destruct (classic (exists n, measure_possible a tr n)) as [Ha|Ha].
  - assert (exists n, measure_possible b tr' n) as Hb by (destruct Ha as [n Hn]; exists n; apply Heq; exact Hn).
    destruct (minimum_spec _ _ Ha) as [Hmina Hlea]. destruct (minimum_spec _ _ Hb) as [Hminb Hleb].
    specialize (Hlea _ (proj2 (Heq _) Hminb)); specialize (Hleb _ (proj1 (Heq _) Hmina)); lia.
  - assert (~ (exists n, measure_possible b tr' n)) as Hb by
      (intros [n Hn]; apply Ha; exists n; apply Heq; exact Hn).
    unfold minimum_counterexample; destruct (excluded_middle_informative (exists n, measure_possible a tr n));
      [contradiction|]; destruct (excluded_middle_informative (exists n, measure_possible b tr' n));
      [contradiction|reflexivity].
Qed.

(** Each atomic action contributes one new state; all possible
    successors remain available in the relational model. *)
Lemma atomic_execution prefix s action run :
  execution_sequence (prefix ++ [s]) (Atomic action) run <->
  exists next, interpret_action M action s next /\
    run = [prefix ++ [s]; (prefix ++ [s]) ++ [next]].
Proof.
  split.
  - intros [start [steps [result [Hp [_ [Ho Hrun]]]]]].
    cbn [program_holds] in Hp; apply atomic_trace_law in Hp.
    destruct Hp as [initial [next [Heq Hstep]]].
    inversion Heq; subst start steps. apply overlap_snoc in Ho as [-> ->].
    exists next; split; [exact Hstep|]. rewrite Hrun; reflexivity.
  - intros [next [Hstep Hrun]].
    exists s, [next], ((prefix ++ [s]) ++ [next]); split.
    + cbn [program_holds]; apply atomic_trace_law; exists s, next; auto.
    + split; [discriminate|]. split; [apply overlap_snoc; auto|exact Hrun].
Qed.

(** A minimizing source counterexample selects ONE successor. Picking an
    unrelated successor would not establish this inequality. *)
Lemma atomic_minimum_successor prefix s action body :
  ~ formula_holds M (Box (Atomic action) body) (prefix ++ [s]) ->
  exists next, interpret_action M action s next /\
    ~ formula_holds M body ((prefix ++ [s]) ++ [next]) /\
    minimum_counterexample body ((prefix ++ [s]) ++ [next]) <
    minimum_counterexample (Box (Atomic action) body) (prefix ++ [s]).
Proof.
  intro Hfalse.
  assert (prefix ++ [s] <> []) as Htr by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  destruct (minimum_spec _ _ (false_minimum_exists _ _ Htr Hfalse)) as [[history [Hce Hmeasure]] Hleast].
  cbn [counterexample] in Hce.
  destruct Hce as [run [final [rest [Hrun [Hfinal [Hrest Hjoin]]]]]].
  apply atomic_execution in Hrun as [next [Hstep ->]].
  cbn in Hfinal; subst final.
  assert ((prefix ++ [s]) ++ [next] <> []) as Hnext by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  pose proof (counterexample_false _ _ _ Hnext Hrest) as Hbad.
  destruct (counterexample_head _ _ _ Hrest) as [tail Hhead].
  rewrite Hhead in Hjoin.
  change (overlap_list ([prefix ++ [s]] ++ [(prefix ++ [s]) ++ [next]])
    (((prefix ++ [s]) ++ [next]) :: tail) history) in Hjoin.
  apply overlap_list_snoc in Hjoin as [_ Hhistory].
  assert (history = (prefix ++ [s]) :: rest) as ->.
  { rewrite Hhead, Hhistory; reflexivity. }
  (* The attained source measure is [length current + measure rest]. The
     body's minimum is at most [measure rest], and the current trace is
     nonempty, so removing that component gives a strict decrease. *)
  destruct (minimum_spec _ _ (false_minimum_exists _ _ Hnext Hbad)) as [_ Htarget].
  assert (minimum_counterexample body ((prefix ++ [s]) ++ [next]) <= sequence_measure rest) as Hbound.
  { apply Htarget; exists rest; auto. }
  exists next; split; [exact Hstep|]. split; [exact Hbad|].
  change (length (prefix ++ [s]) + sequence_measure rest =
    minimum_counterexample (Box (Atomic action) body) (prefix ++ [s])) in Hmeasure.
  rewrite length_app in Hmeasure; cbn in Hmeasure; lia.
Qed.

(** Tags identify occurrences; the occurrence's formula and interpreted
    label determine its rank. Renaming the tag alone cannot change it. *)
Definition occurrence_rank (o : occurrence) (w : world M) :=
  minimum_counterexample o.(occurrence_formula) (eval_label M w o.(occurrence_label)).

(** Look up the first matching tag, falling back to 0 if absent. The syntax
    checker enforces uniqueness on well-formed succedents, and Rules.v proves
    that lookup then equals the rank of the intended occurrence. *)
Fixpoint rank_in_context (context : list occurrence) (w : world M) (tag : nat) : nat :=
  match context with
  | [] => 0
  | o :: rest =>
      match o.(occurrence_tag) with
      | Some t => if Nat.eqb tag t then occurrence_rank o w else rank_in_context rest w tag
      | None => rank_in_context rest w tag
      end
  end.

(** Syntactic label substitution and its matching environment transformation
    produce identical interpreted traces, hence identical occurrence ranks.
    This is the rank half of the substitution rules in Rules.v. *)
Lemma rank_label_mapping f w w' :
  (forall l, eval_label M w (f l) = eval_label M w' l) -> forall context tag,
  rank_in_context (map (map_label_occurrence f) context) w tag = rank_in_context context w' tag.
Proof.
  intros Hmap context; induction context as [|o rest IH]; intro tag; cbn [map rank_in_context map_label_occurrence occurrence_tag].
  - reflexivity.
  - destruct (occurrence_tag o) as [t|]; [destruct (Nat.eqb tag t)|]; try apply IH.
    unfold occurrence_rank; cbn [map_label_occurrence occurrence_label occurrence_formula]; now rewrite Hmap.
Qed.

(** Only succedent occurrences are trace elements. Missing tags have rank 0.
    True formulas have no counterexamples and receive the documented fallback
    0. False admissible formulas have the minimum specified above. *)
Module LPLTheory <: Framework.THEORY.
  Definition World := world M.
  Definition Judgment := judgment.
  Definition Sequent := World -> Prop.
  Definition judgment_eqb := Syn.judgment_eqb.
  Definition backlink_eqb := Syn.backlink_eqb.
  Definition denote := Sem.denote M.
  Definition tags := judgment_tags.
  Definition rank j w tag := rank_in_context j.(succedent) w tag.
End LPLTheory.

Module Cyclic := Framework.Make LPLTheory.

End ForModel.
Module Type MODEL (I : Sem.INTERPRETATION).
  Include ForModel I.
End MODEL.
End MakeProgress.
Module Type PROGRESS (L : LANGUAGE) (Syn : SYNTAX L) (Sem : SEMANTICS L Syn).
  Include MakeProgress L Syn Sem.
End PROGRESS.
