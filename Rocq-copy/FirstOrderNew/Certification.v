From Stdlib Require Import List Bool Arith Lia.
From CyclistRocq.FirstOrderNew Require Export Adapter.
Import ListNotations.

(** These proofs are generic over the FO definition environment and graphs.
    In particular, examples do not supply bespoke cert_advance proofs. *)
Module Certify (D : DEFINITION_ENV).
  Module FO := Make D.
  Import FO.Cyclic.

  Lemma pair_mem_spec p ps : pair_mem p ps = true <-> In p ps.
  Proof.
    induction ps as [|[a b] ps IH]; cbn;
      [split; [discriminate|contradiction]|].
    unfold pair_eqb; destruct p as [x y]; cbn.
    rewrite orb_true_iff, andb_true_iff, !Nat.eqb_eq, IH.
    split.
    - intros [[Hx Hy]|H]; [subst; now left|now right].
    - intros [H|H]; [inversion H; subst; auto|auto].
  Qed.
  Lemma transition_reflect tw i j e : trace_transitionb tw i j e = true ->
    trace_transition tw i j e.
  Proof.
    unfold trace_transitionb, trace_transition.
    destruct (witness_tag tw i), (witness_tag tw j); cbn -[Nat.ltb].
    - rewrite andb_true_iff, orb_true_iff, pair_mem_spec, pair_mem_spec, Nat.ltb_lt; tauto.
    - discriminate.
    - auto.
    - apply Nat.ltb_lt.
  Qed.
  Lemma all_nodes_at g ns start i n : all_nodes_wfb_from g start ns = true ->
    nth_error ns i = Some n -> node_wfb g (start+i) n = true.
  Proof.
    revert start i; induction ns as [|a ns IH]; intros start [|i] H Hi;
      cbn in *; try discriminate; apply andb_true_iff in H; destruct H as [Ha Hrest].
    - inversion Hi; subst; now rewrite Nat.add_0_r.
    - replace (start+S i) with (S start+i) by lia. eapply IH; eauto.
  Qed.
  Lemma structural_node g i n : structural_check g = true ->
    node_at g i = Some n -> node_wfb g i n = true.
  Proof.
    unfold structural_check; destruct (graph_nodes g) as [|root ns] eqn:En; [discriminate|].
    intro H; apply andb_true_iff in H; destruct H as [H _].
    apply andb_true_iff in H; destruct H as [_ H].
    unfold node_at; rewrite En; intro Hi.
    exact (all_nodes_at g (root::ns) 0 i n H Hi).
  Qed.
  Lemma targets_at g source ts ps k p : targets_wfb_from g source ts ps = true ->
    nth_error ps k = Some p ->
    { j : nat | nth_error ts k = Some j /\ j < List.length (graph_nodes g) /\
      label_at g j = premise_judgment p }.
  Proof.
    revert ts k; induction ps as [|q ps IH]; intros [|j ts] [|k] H Hp;
      cbn in *; try discriminate.
    all: repeat rewrite andb_true_iff in H; destruct H as [[[Hj Heq] Hedge] Hrest].
    - inversion Hp; subst; exists j; split; [reflexivity|].
      split; [now apply Nat.ltb_lt|now apply sequent_eqb_spec].
    - exact (IH ts k Hrest Hp).
  Defined.
  Lemma combine_premise (ts : list nat) (ps : list premise) k j p : nth_error ts k = Some j ->
    nth_error ps k = Some p -> In (j,premise_edge p) (combine ts (map premise_edge ps)).
  Proof.
    revert ps k; induction ts as [|t ts IH]; intros [|q ps] [|k] Ht Hp;
      cbn in *; try discriminate.
    - inversion Ht; inversion Hp; subst; now left.
    - right; eapply IH; eauto.
  Qed.

  Definition closed_advance g (Hclosed : structural_check g = true) :
    forall i w, i < List.length (graph_nodes g) -> ~ holds (label_at g i) w ->
    { j : nat & { w' : world & { e : edge_info |
      edge_at g i j e /\ j < List.length (graph_nodes g) /\
      ~ holds (label_at g j) w' /\
      respects_edge (label_at g i) (label_at g j) w w' e } } }.
  Proof.
    intros i w Hi Hbad.
    destruct (node_at g i) as [n|] eqn:En.
    2: { unfold node_at in En. apply nth_error_None in En; lia. }
    pose proof (structural_node g i n Hclosed En) as Hn.
    assert (Hlabel : label_at g i = node_judgment n) by (unfold label_at; rewrite En; reflexivity).
    rewrite Hlabel in Hbad.
    unfold node_wfb in Hn.
    destruct (node_payload n) as [|a|r ts|r target] eqn:Ep; cbn -[Nat.ltb] in Hn.
    - discriminate.
    - apply sequent_eqb_spec in Hn. exfalso; apply Hbad; rewrite Hn; apply axiom_theorem.
    - apply andb_true_iff in Hn; destruct Hn as [Hcon Hts].
      apply sequent_eqb_spec in Hcon.
      destruct (rule_counter_step r w (eq_ind _ (fun j => ~ holds j w) Hbad _ Hcon))
        as [k [p [w' [Hk [Hfalse Hrank]]]]].
      destruct (targets_at g (node_judgment n) ts (rule_premises r) k p Hts Hk)
        as [j [Hj [Hbound Htarget]]].
      exists j,w',(premise_edge p); split.
      + exists n; split; [exact En|]. unfold node_edges; rewrite Ep; cbn.
        eapply combine_premise; eauto.
      + split; [exact Hbound|]. split; [now rewrite Htarget|].
        rewrite Hlabel,Hcon,Htarget; exact Hrank.
    - destruct (rule_premises r) as [|p [|q ps]] eqn:Eps;
        cbn -[Nat.ltb] in Hn;
        try (rewrite andb_false_r in Hn; discriminate).
      repeat rewrite andb_true_iff in Hn.
      destruct Hn as [[[Hcon Hneq] Hb] [[Hbound Heq] Hedge]].
      apply sequent_eqb_spec in Hcon; apply sequent_eqb_spec in Heq.
      destruct (rule_counter_step r w (eq_ind _ (fun j => ~ holds j w) Hbad _ Hcon))
        as [[|k] [p' [w' [Hk [Hfalse Hrank]]]]]; rewrite Eps in Hk; cbn in Hk.
      2: { destruct k; discriminate. }
      inversion Hk; subst p'. exists target,w',(premise_edge p); split.
      + exists n; split; [exact En|]. unfold node_edges; rewrite Ep,Eps; cbn; now left.
      + split; [now apply Nat.ltb_lt|]. split; [now rewrite Heq|].
        rewrite Hlabel,Hcon,Heq; exact Hrank.
  Defined.

  Lemma false_path g (Hclosed : structural_check g = true) fuel i w :
    i < List.length (graph_nodes g) -> ~ holds (label_at g i) w ->
    has_path_of_length g fuel i = true.
  Proof.
    revert i w; induction fuel as [|fuel IH]; intros i w Hi Hbad; cbn.
    - now apply Nat.ltb_lt.
    - destruct (closed_advance g Hclosed i w Hi Hbad) as [j [w' [e [Hedge [Hj [Hbad' Hr]]]]]].
      apply existsb_exists; exists j; split; [|eapply IH; eauto].
      destruct Hedge as [n [Hn He]]. unfold successors; rewrite Hn.
      apply in_map_iff; exists (j,e); auto.
  Qed.
  Lemma witness_at g tw ns start i n : witness_edges_from g tw start ns = true ->
    nth_error ns i = Some n ->
    forallb (edge_witnessb g tw (start+i)) (node_edges n) = true.
  Proof.
    revert start i; induction ns as [|a ns IH]; intros start [|i] H Hi;
      cbn in *; try discriminate; repeat rewrite andb_true_iff in H;
      destruct H as [[Ha He] Hr].
    - inversion Hi; subst; now rewrite Nat.add_0_r.
    - replace (start+S i) with (S start+i) by lia; eapply IH; eauto.
  Qed.
  Lemma witness_transitions g tw : witness_check g tw = true ->
    forall i j e, edge_at g i j e -> liveb g j = true -> trace_transition tw i j e.
  Proof.
    intros H i j e [n [Hn He]] Hlive.
    pose proof (witness_at g tw (graph_nodes g) 0 i n H Hn) as Hall.
    apply forallb_forall with (x:=(j,e)) in Hall; [|exact He].
    unfold edge_witnessb in Hall; cbn in Hall; rewrite Hlive in Hall.
    apply transition_reflect; exact Hall.
  Qed.
  Definition certify g tw (Hclosed : structural_check g = true)
    (Htw : witness_check g tw = true) : certificate.
  Proof.
    refine {| cert_graph := g; cert_witness := tw;
      cert_advance := closed_advance g Hclosed;
      cert_trace_transition := witness_transitions g tw Htw |}.
    - unfold structural_check in Hclosed; destruct (graph_nodes g) eqn:E;
        [discriminate|cbn; lia].
    - unfold structural_check in Hclosed; destruct (graph_nodes g) as [|root ns] eqn:E;
        [discriminate|].
      repeat rewrite andb_true_iff in Hclosed; destruct Hclosed as [[Hr _] _].
      unfold label_at,node_at; rewrite E; cbn; now apply sequent_eqb_spec.
    - intros i w Hi Hbad; unfold liveb; eapply false_path; eauto.
  Defined.
  Definition certify_checked g tw (H : raw_check g tw = true) : certificate.
  Proof.
    pose proof (proj1 (andb_true_iff _ _) H) as Houter.
    pose proof (proj1 (andb_true_iff _ _) (proj1 Houter)) as Hinner.
    exact (certify g tw (proj1 Hinner) (proj2 Houter)).
  Defined.
  Theorem checked_graph_sound g tw (H : raw_check g tw = true) : valid D.defs (graph_root g).
  Proof.
    apply FO.valid_bridge. apply (certificate_sound (certify_checked g tw H)). exact H.
  Qed.
End Certify.
