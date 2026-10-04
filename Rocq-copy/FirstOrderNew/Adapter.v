From Stdlib Require Import List Bool Arith Lia String.
From CyclistRocq.FirstOrderNew Require Export Rules.
From CyclistRocq.Cyclic Require Import Framework.
Import ListNotations.

(** Native tags are absolute atom positions. The cyclic framework sees only
    dense predicate ordinals; equality atoms must not inflate its trace width.
    [trace_index] selects the first occurrence and returns the list length when
    a position is absent. Edge conversion filters absent positions first. *)
Fixpoint trace_index (position : nat) (positions : list nat) : nat :=
  match positions with [] => 0 | p :: ps =>
    if Nat.eqb position p then 0 else S (trace_index position ps) end.
Lemma trace_index_nth position positions : In position positions ->
  nth (trace_index position positions) positions 0 = position.
Proof.
  induction positions as [|p ps IH]; cbn; [contradiction|].
  destruct (Nat.eqb position p) eqn:E.
  - intros _; now apply Nat.eqb_eq in E.
  - intros [H|H]; [subst p; rewrite Nat.eqb_refl in E; discriminate|now apply IH].
Qed.
Lemma trace_index_lt position positions : In position positions ->
  trace_index position positions < List.length positions.
Proof.
  induction positions as [|p ps IH]; cbn; [contradiction|].
  destruct (Nat.eqb position p) eqn:E; [lia|].
  intros [H|H]; [subst p; rewrite Nat.eqb_refl in E; discriminate|].
  specialize (IH H); lia.
Qed.
Lemma native_position_mem position positions :
  existsb (Nat.eqb position) positions = true <-> In position positions.
Proof.
  rewrite existsb_exists; split.
  - intros [p [Hp Heq]]; apply Nat.eqb_eq in Heq; now subst p.
  - intro H; exists position; split; [exact H|apply Nat.eqb_refl].
Qed.
Definition registered_pairb source target (ab : nat * nat) :=
  existsb (Nat.eqb (fst ab)) (trace_tags source) &&
  existsb (Nat.eqb (snd ab)) (trace_tags target).
Definition dense_pairs source target pairs :=
  map (fun ab => (trace_index (fst ab) (trace_tags source),
                 trace_index (snd ab) (trace_tags target)))
    (filter (registered_pairb source target) pairs).
Lemma dense_pairs_spec source target pairs a b : In (a,b) (dense_pairs source target pairs) ->
  exists x y, In (x,y) pairs /\ In x (trace_tags source) /\ In y (trace_tags target) /\
    a = trace_index x (trace_tags source) /\ b = trace_index y (trace_tags target).
Proof.
  unfold dense_pairs; rewrite in_map_iff; intros [[x y] [Heq Hpair]].
  apply filter_In in Hpair; destruct Hpair as [Hin Hregistered].
  unfold registered_pairb in Hregistered; cbn in Hregistered.
  apply andb_true_iff in Hregistered; destruct Hregistered as [Hx Hy].
  apply native_position_mem in Hx; apply native_position_mem in Hy.
  cbn in Heq; inversion Heq; subst a b; exists x,y; auto.
Qed.
Lemma dense_pairs_registered source target pairs a b : In (a,b) (dense_pairs source target pairs) ->
  In a (seq 0 (List.length (trace_tags source))) /\
  In b (seq 0 (List.length (trace_tags target))).
Proof.
  intro H; destruct (dense_pairs_spec source target pairs a b H)
    as (x & y & Hin & Hx & Hy & -> & ->).
  split; apply in_seq; split; [lia|now apply trace_index_lt|lia|now apply trace_index_lt].
Qed.

Module Type DEFINITION_ENV.
  Parameter defs : definitions.
End DEFINITION_ENV.

Module Make (D : DEFINITION_ENV).
  Module Theory <: Framework.THEORY.
    Definition World := world.
    Definition Judgment := sequent.
    Definition Sequent := World -> Prop.
    Definition judgment_eqb := sequent_eqb.
    Definition backlink_eqb := sequent_eqb.
    Definition denote := denote D.defs.
    Definition tags j := seq 0 (List.length (trace_tags j)).
    Definition rank j (w : World) dense := world_bounds w (nth dense (trace_tags j) 0).
  End Theory.
  Module Cyclic := Framework.Make Theory.

  Lemma dense_rank j w position : In position (trace_tags j) ->
    Theory.rank j w (trace_index position (trace_tags j)) = rank D.defs j w position.
  Proof. intro H; unfold Theory.rank, rank; now rewrite (trace_index_nth position _ H). Qed.
  Definition edge source target (e : trace_edge) : Cyclic.edge_info :=
    {| Cyclic.edge_valid := dense_pairs source target e.(continuations);
       Cyclic.edge_progress := dense_pairs source target e.(progressing) |}.
  Lemma edge_registered source target e :
    (forall a b, In (a,b) (Cyclic.edge_valid (edge source target e)) ->
      In a (Theory.tags source) /\ In b (Theory.tags target)) /\
    (forall a b, In (a,b) (Cyclic.edge_progress (edge source target e)) ->
      In a (Theory.tags source) /\ In b (Theory.tags target)).
  Proof. split; intros a b H; now apply dense_pairs_registered in H. Qed.
  Lemma edge_respects source target w w' e : respects D.defs source target w w' e ->
    Cyclic.respects_edge source target w w' (edge source target e).
  Proof.
    intros [Hvalid Hprogress]; split; intros a b Hpair.
    - destruct (dense_pairs_spec source target (continuations e) a b Hpair)
        as (x & y & Hin & Hx & Hy & -> & ->).
      rewrite (dense_rank target w' y Hy), (dense_rank source w x Hx); now apply Hvalid.
    - destruct (dense_pairs_spec source target (progressing e) a b Hpair)
        as (x & y & Hin & Hx & Hy & -> & ->).
      rewrite (dense_rank target w' y Hy), (dense_rank source w x Hx); now apply Hprogress.
  Qed.
  Definition premise source (p : native_premise) : Cyclic.premise :=
    {| Cyclic.premise_judgment := p.(premise_label);
       Cyclic.premise_edge := edge source p.(premise_label) p.(premise_trace) |}.
  Lemma valid_bridge j : valid D.defs j <-> Cyclic.Valid j.
  Proof. apply valid_iff_worlds. Qed.
  Definition rule (r : application) (E : local_evidence D.defs r) : Cyclic.rule_instance.
  Proof.
    refine {| Cyclic.rule_name := r.(application_name);
      Cyclic.rule_conclusion := r.(conclusion);
      Cyclic.rule_premises := map (premise r.(conclusion)) r.(premises) |}.
    - intro H; apply valid_bridge. apply (local_sound D.defs r E).
      intros p Hp; apply valid_bridge; apply (H (premise r.(conclusion) p)).
      apply in_map; exact Hp.
    - intros w Hfalse.
      destruct (local_counter_step D.defs r E w Hfalse)
        as [k [p [w' [Hk [Hbad Hrank]]]]].
      exists k, (premise r.(conclusion) p), w'; split.
      + rewrite nth_error_map, Hk; reflexivity.
      + split; [exact Hbad|now apply edge_respects].
  Defined.
  Definition axiom j (H : axiom_check j = true) : Cyclic.axiom_instance :=
    {| Cyclic.axiom_name := "FO axiom"%string; Cyclic.axiom_conclusion := j;
       Cyclic.axiom_theorem := proj1 (valid_bridge j) (axiom_check_sound D.defs j H) |}.
  Definition exact_backlink (j : sequent) : Cyclic.rule_instance.
  Proof.
    refine {| Cyclic.rule_name := "FO exact backlink"%string;
      Cyclic.rule_conclusion := j;
      Cyclic.rule_premises := [{| Cyclic.premise_judgment := j;
        Cyclic.premise_edge := {| Cyclic.edge_valid := Cyclic.identity_pairs (Theory.tags j);
                                 Cyclic.edge_progress := [] |} |}] |}.
    - intro H; apply (H {| Cyclic.premise_judgment := j;
        Cyclic.premise_edge := {| Cyclic.edge_valid := Cyclic.identity_pairs (Theory.tags j);
                                 Cyclic.edge_progress := [] |} |}); now left.
    - intros w Hbad; exists 0; eexists; exists w; split; [reflexivity|].
      split; [exact Hbad|]. split.
      + intros a b Hab. apply in_map_iff in Hab; destruct Hab as [t [Heq Hin]].
        inversion Heq; subst; apply Nat.le_refl.
      + intros a b H; contradiction.
  Defined.
End Make.
