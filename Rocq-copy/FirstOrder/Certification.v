From Stdlib Require Import List Bool Arith Lia String Classical_Prop.

From CyclistRocq.FirstOrder Require Import Syntax Semantics Rules.

Import ListNotations.
Open Scope string_scope.

(** * Turning an executable graph into a semantic certificate

    [Cyclic.raw_check] is deliberately executable, whereas
    [Cyclic.certificate] contains the semantic evidence used by the generic
    well-founded descent proof.  LTL constructs that evidence by hand for its
    two example graphs.  An automatic prover cannot do that per result, so this
    module proves once that the relevant successful Boolean checks expose all
    local data needed to build the evidence.

    Nothing here changes the generic framework.  The lemmas inspect its public
    graph representation and use the [rule_counter_step] theorem already
    stored in every first-order rule instance. *)

Lemma pair_mem_spec pair pairs :
  Cyclic.pair_mem pair pairs = true <-> In pair pairs.
Proof.
  induction pairs as [|x xs IH]; simpl.
  - split; [discriminate|contradiction].
  - rewrite Bool.orb_true_iff, IH.
    unfold Cyclic.pair_eqb. destruct pair as [a b], x as [c d]; simpl.
    rewrite Bool.andb_true_iff, !Nat.eqb_eq.
    split.
    + intros [[-> ->] | Hin]; [now left|now right].
    + intros [Heq | Hin].
      * inversion Heq; subst. auto.
      * auto.
Qed.


Lemma all_nodes_wfb_from_nth g nodes start offset n :
  Cyclic.all_nodes_wfb_from g start nodes = true ->
  nth_error nodes offset = Some n ->
  Cyclic.node_wfb g (start + offset) n = true.
Proof.
  revert nodes start n. induction offset as [|offset IH];
    intros [|x xs] start n Hall Hnth; simpl in Hnth; try discriminate.
  - inversion Hnth; subst n. simpl in Hall.
    apply Bool.andb_true_iff in Hall as [Hnode _].
    replace (start + 0) with start by lia. exact Hnode.
  - simpl in Hall. apply Bool.andb_true_iff in Hall as [_ Htail].
    specialize (IH xs (S start) n Htail Hnth).
    replace (start + S offset) with (S start + offset) by lia. exact IH.
Qed.

Lemma structural_node_wfb g i n :
  Cyclic.structural_check g = true ->
  Cyclic.node_at g i = Some n ->
  Cyclic.node_wfb g i n = true.
Proof.
  destruct g as [root nodes]. unfold Cyclic.structural_check.
  destruct nodes as [|first rest]; [discriminate|].
  simpl. intros Hall Hnode.
  (* [&&] is left associative in Rocq: the checker is parsed as
     [(root_ok && nodes_ok) && reachable_ok]. *)
  apply Bool.andb_true_iff in Hall as [Hall _].
  apply Bool.andb_true_iff in Hall as [_ Hnodes].
  change (Cyclic.all_nodes_wfb_from
    {| Cyclic.graph_root := root; Cyclic.graph_nodes := first :: rest |}
    0 (first :: rest) = true) in Hnodes.
  unfold Cyclic.node_at in Hnode; simpl in Hnode.
  eapply all_nodes_wfb_from_nth with (start := 0) (offset := i);
    [exact Hnodes|exact Hnode].
Qed.

Lemma structural_root_bound g :
  Cyclic.structural_check g = true ->
  0 < List.length g.(Cyclic.graph_nodes).
Proof.
  destruct g as [root [|first rest]]; simpl; [discriminate|lia].
Qed.

Lemma structural_root_label g :
  Cyclic.structural_check g = true ->
  Cyclic.label_at g 0 = g.(Cyclic.graph_root).
Proof.
  destruct g as [root [|first rest]]; simpl; [discriminate|].
  intro H. apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [Hroot _].
  apply judgment_eqb_spec in Hroot. exact Hroot.
Qed.

(** The target and premise lists of an inference node are checked in
    lockstep.  This lemma recovers the target belonging to a selected premise
    index, including the exact target label and its bounds proof. *)
Lemma targets_wfb_nth g source targets premises k p :
  Cyclic.targets_wfb_from g source targets premises = true ->
  nth_error premises k = Some p ->
  { target : nat |
    nth_error targets k = Some target /\
    target < List.length g.(Cyclic.graph_nodes) /\
    Cyclic.label_at g target = p.(Cyclic.premise_judgment) }.
Proof.
  revert targets premises p. induction k as [|k IH];
    intros [|target targets] [|prem premises] p Hall Hprem;
    simpl in *; try discriminate.
  - inversion Hprem; subst prem.
    (* This four-way conjunction is parsed on the left as
       [(((bound && label) && edge_ok) && tail_ok)]. *)
    apply Bool.andb_true_iff in Hall as [Hall _].
    apply Bool.andb_true_iff in Hall as [Hall _].
    apply Bool.andb_true_iff in Hall as [Hbound Hlabel].
    apply Nat.ltb_lt in Hbound. apply judgment_eqb_spec in Hlabel.
    exists target. auto.
  - apply Bool.andb_true_iff in Hall as [_ Htail].
    specialize (IH targets premises p Htail Hprem).
    destruct IH as [chosen [Hchosen [Hbound' Hlabel']]].
    exists chosen. auto.
Qed.

Lemma nth_error_map_premise_edge premises k p :
  nth_error premises k = Some p ->
  nth_error (map Cyclic.premise_edge premises) k =
    Some p.(Cyclic.premise_edge).
Proof. intro H. now rewrite nth_error_map, H. Qed.

Lemma combine_nth_in {A B : Type} (xs : list A) (ys : list B) k x y :
  nth_error xs k = Some x -> nth_error ys k = Some y ->
  In (x, y) (combine xs ys).
Proof.
  revert xs ys x y. induction k as [|k IH];
    intros [|a xs] [|b ys] x y Hx Hy; simpl in *; try discriminate.
  - inversion Hx; inversion Hy; subst. now left.
  - right. eapply IH; eauto.
Qed.

Lemma node_edge_from_rule_nth g i n r targets k p target :
  Cyclic.node_at g i = Some n ->
  n.(Cyclic.node_payload) = Cyclic.RuleNode r targets ->
  nth_error r.(Cyclic.rule_premises) k = Some p ->
  nth_error targets k = Some target ->
  Cyclic.edge_at g i target p.(Cyclic.premise_edge).
Proof.
  intros Hnode Hpayload Hprem Htarget. exists n. split; [exact Hnode|].
  unfold Cyclic.node_edges. rewrite Hpayload. simpl.
  eapply combine_nth_in; [exact Htarget|].
  now apply nth_error_map_premise_edge.
Qed.

Lemma edge_at_successor g i j e :
  Cyclic.edge_at g i j e -> In j (Cyclic.successors g i).
Proof.
  intros [n [Hnode Hedge]]. unfold Cyclic.successors. rewrite Hnode.
  apply in_map with (f := @fst nat Cyclic.edge_info) in Hedge. exact Hedge.
Qed.

(** A successful structural check rules out a false dead end.  The proof has
    four cases, one for each node payload:

    - an open node contradicts [node_wfb];
    - an axiom node contradicts the axiom's semantic theorem;
    - a rule node uses the rule's stored countermodel theorem and the checked
      target list;
    - a backlink node uses the same countermodel theorem, but its only premise
      is connected to the explicitly stored companion node.

    This is the semantic bridge between an executable proof graph and the
    abstract [cert_advance] field required by [Cyclic.certificate]. *)
Lemma structurally_checked_advance g i w :
  Cyclic.structural_check g = true ->
  i < List.length g.(Cyclic.graph_nodes) ->
  ~ Cyclic.holds (Cyclic.label_at g i) w ->
  { j : nat &
    { w' : FirstOrderTheory.World &
      { e : Cyclic.edge_info |
        Cyclic.edge_at g i j e /\
        j < List.length g.(Cyclic.graph_nodes) /\
        ~ Cyclic.holds (Cyclic.label_at g j) w' /\
        Cyclic.respects_edge (Cyclic.label_at g i)
          (Cyclic.label_at g j) w w' e } } }.
Proof.
  intros Hstruct Hibound Hfalse.
  (* Destruct the executable lookup itself.  Using a propositional
     [exists n, ...] here would later attempt to eliminate a [Prop] proof to
     build the dependent witness in [Type], which Rocq intentionally forbids. *)
  destruct (Cyclic.node_at g i) as [n|] eqn:Hnode.
  2: {
    unfold Cyclic.node_at in Hnode.
    apply nth_error_None in Hnode. lia.
  }
  pose proof (structural_node_wfb g i n Hstruct Hnode) as Hwf.
  assert (Hsource : Cyclic.label_at g i = n.(Cyclic.node_judgment)).
  { unfold Cyclic.label_at. now rewrite Hnode. }
  destruct n.(Cyclic.node_payload) as [|a|r targets|r target]
    eqn:Hpayload.
  all: unfold Cyclic.node_wfb in Hwf; rewrite Hpayload in Hwf.
  - (* An accepted graph never contains an open node. *)
    discriminate Hwf.
  - (* A false axiom would contradict the theorem packaged in the axiom. *)
    apply judgment_eqb_spec in Hwf.
    exfalso. apply Hfalse. rewrite Hsource, Hwf.
    exact (a.(Cyclic.axiom_theorem) w).
  - (* Ordinary inference node. *)
    apply Bool.andb_true_iff in Hwf as [Hconclusion Htargets].
    apply judgment_eqb_spec in Hconclusion.
    assert (Hrulefalse : ~ Cyclic.holds r.(Cyclic.rule_conclusion) w).
    {
      intro Hholds. apply Hfalse.
      rewrite Hsource, Hconclusion. exact Hholds.
    }
    destruct (r.(Cyclic.rule_counter_step) w Hrulefalse)
      as [k [p [w' [Hpremise [Htargetfalse Hrespect]]]]].
    destruct (targets_wfb_nth g n.(Cyclic.node_judgment) targets
      r.(Cyclic.rule_premises) k p Htargets Hpremise)
      as [j [Htarget [Hjbound Hjlabel]]].
    exists j, w', p.(Cyclic.premise_edge).
    split.
    + eapply node_edge_from_rule_nth; eauto.
    + split; [exact Hjbound|]. split.
      * now rewrite Hjlabel.
      * rewrite Hsource, Hconclusion, Hjlabel. exact Hrespect.
  - (* Backlink node: the checker guarantees a unary premise at [target]. *)
    (* The backlink well-formedness test is a left-associated four-way
       conjunction.  Only its conclusion and unary-target components are
       needed here; the non-reflexivity and backlink-label tests remain part
       of the executable checker. *)
    apply Bool.andb_true_iff in Hwf as [Hwf Htargetcheck].
    apply Bool.andb_true_iff in Hwf as [Hwf _].
    apply Bool.andb_true_iff in Hwf as [Hconclusion _].
    apply judgment_eqb_spec in Hconclusion.
    destruct r.(Cyclic.rule_premises) as [|p ps] eqn:Hps;
      simpl in Htargetcheck; try discriminate.
    destruct ps as [|extra ps']; simpl in Htargetcheck; try discriminate.
    apply Bool.andb_true_iff in Htargetcheck as [Htargetcheck _].
    apply Bool.andb_true_iff in Htargetcheck as [Htargetbound Htargetlabel].
    apply Nat.ltb_lt in Htargetbound.
    apply judgment_eqb_spec in Htargetlabel.
    assert (Hrulefalse : ~ Cyclic.holds r.(Cyclic.rule_conclusion) w).
    {
      intro Hholds. apply Hfalse.
      rewrite Hsource, Hconclusion. exact Hholds.
    }
    destruct (r.(Cyclic.rule_counter_step) w Hrulefalse)
      as [k [chosen [w' [Hchosen [Htargetfalse Hrespect]]]]].
    rewrite Hps in Hchosen.
    destruct k as [|k]; simpl in Hchosen.
    2: destruct k; discriminate.
    inversion Hchosen; subst chosen.
    exists target, w', p.(Cyclic.premise_edge).
    split.
    + exists n. split; [exact Hnode|].
      unfold Cyclic.node_edges. rewrite Hpayload, Hps. simpl. now left.
    + split; [exact Htargetbound|]. split.
      * now rewrite Htargetlabel.
      * rewrite Hsource, Hconclusion, Htargetlabel. exact Hrespect.
Qed.

(** Repeatedly use [structurally_checked_advance] to construct a path of any
    requested finite length from a false node.  At length zero the current
    bounded node is already a path endpoint.  At successor length, the
    countermodel theorem chooses one false outgoing child and induction
    continues there. *)
Lemma false_has_path_of_length g fuel i w :
  Cyclic.structural_check g = true ->
  i < List.length g.(Cyclic.graph_nodes) ->
  ~ Cyclic.holds (Cyclic.label_at g i) w ->
  Cyclic.has_path_of_length g fuel i = true.
Proof.
  revert i w. induction fuel as [|fuel IH]; intros i w Hstruct Hibound Hfalse.
  - simpl. now apply Nat.ltb_lt.
  - simpl.
    destruct (structurally_checked_advance g i w Hstruct Hibound Hfalse)
      as [j [w' [e [Hedge [Hjbound [Hfalse' _]]]]]].
    apply existsb_exists. exists j. split.
    + now apply edge_at_successor with (e := e).
    + now apply (IH j w').
Qed.

(** [liveb] asks for a path whose length is exactly the number of stored
    nodes.  The preceding lemma therefore supplies precisely the certificate's
    liveness obligation. *)
Lemma structurally_checked_false_live g i w :
  Cyclic.structural_check g = true ->
  i < List.length g.(Cyclic.graph_nodes) ->
  ~ Cyclic.holds (Cyclic.label_at g i) w ->
  Cyclic.liveb g i = true.
Proof.
  intros Hstruct Hibound Hfalse. unfold Cyclic.liveb.
  now apply (false_has_path_of_length g
    (List.length g.(Cyclic.graph_nodes)) i w).
Qed.

(** Reflection for the small Boolean transition checker.  Keeping this proof
    separate makes the later witness argument read at the same abstraction
    level as [Cyclic.trace_transition]. *)
Lemma trace_transitionb_sound tw i j e :
  Cyclic.trace_transitionb tw i j e = true ->
  Cyclic.trace_transition tw i j e.
Proof.
  unfold Cyclic.trace_transitionb, Cyclic.trace_transition.
  destruct (Cyclic.witness_tag tw i) as [a|];
    destruct (Cyclic.witness_tag tw j) as [b|]; simpl.
  - intros H.
    apply Bool.andb_true_iff in H as [Hvalid Hstep].
    apply pair_mem_spec in Hvalid.
    apply Bool.orb_true_iff in Hstep as [Hprogress | Hpotential].
    + split; [exact Hvalid|]. left. now apply pair_mem_spec.
    + split; [exact Hvalid|]. right. now apply Nat.ltb_lt.
  - discriminate.
  - intros _. exact I.
  - intro H. now apply Nat.ltb_lt.
Qed.

(** Select the witness checks belonging to one node index.  As in
    [all_nodes_wfb_from_nth], [start] records the list index of the head and
    [offset] tells us how far to descend. *)
Lemma witness_edges_from_nth g tw nodes start offset n :
  Cyclic.witness_edges_from g tw start nodes = true ->
  nth_error nodes offset = Some n ->
  Cyclic.option_tag_wfb g tw (start + offset) = true /\
  forallb (Cyclic.edge_witnessb g tw (start + offset))
    (Cyclic.node_edges n) = true.
Proof.
  revert nodes start n. induction offset as [|offset IH];
    intros [|x xs] start n Hall Hnth; simpl in Hnth; try discriminate.
  - inversion Hnth; subst n. simpl in Hall.
    apply Bool.andb_true_iff in Hall as [Hhead _].
    apply Bool.andb_true_iff in Hhead as [Htag Hedges].
    replace (start + 0) with start by lia. auto.
  - simpl in Hall.
    apply Bool.andb_true_iff in Hall as [_ Htail].
    specialize (IH xs (S start) n Htail Hnth).
    replace (start + S offset) with (S start + offset) by lia. exact IH.
Qed.

(** A successful whole-graph witness check reflects to the propositional
    transition property on every edge whose target is live. *)
Lemma witness_check_transition g tw i j e :
  Cyclic.witness_check g tw = true ->
  Cyclic.edge_at g i j e ->
  Cyclic.liveb g j = true ->
  Cyclic.trace_transition tw i j e.
Proof.
  intros Hcheck [n [Hnode Hedge]] Hlive.
  unfold Cyclic.witness_check in Hcheck.
  unfold Cyclic.node_at in Hnode.
  destruct (witness_edges_from_nth g tw g.(Cyclic.graph_nodes) 0 i n
    Hcheck Hnode) as [_ Hedges].
  replace (0 + i) with i in Hedges by lia.
  apply forallb_forall with (x := (j, e)) in Hedges; [|exact Hedge].
  unfold Cyclic.edge_witnessb in Hedges. rewrite Hlive in Hedges.
  now apply trace_transitionb_sound.
Qed.

(** Package a graph only after *all* executable checks have returned [true].
    Notice that the relational trace checker is retained in the raw equation;
    the local witness provides the particular well-founded route consumed by
    the generic soundness proof. *)
Lemma raw_check_structural g tw :
  Cyclic.raw_check g tw = true -> Cyclic.structural_check g = true.
Proof.
  unfold Cyclic.raw_check. intro H.
  apply Bool.andb_true_iff in H as [H _].
  now apply Bool.andb_true_iff in H as [Hstruct _].
Qed.

Lemma raw_check_witness g tw :
  Cyclic.raw_check g tw = true -> Cyclic.witness_check g tw = true.
Proof.
  unfold Cyclic.raw_check. intro H.
  now apply Bool.andb_true_iff in H as [_ Hwitness].
Qed.

Definition certify_raw_check (g : Cyclic.graph) (tw : Cyclic.trace_witness)
    (Hcheck : Cyclic.raw_check g tw = true) : Cyclic.certificate.
Proof.
  refine
    {| Cyclic.cert_graph := g;
       Cyclic.cert_witness := tw;
       Cyclic.cert_root_bound :=
         structural_root_bound g (raw_check_structural g tw Hcheck);
       Cyclic.cert_root_label :=
         structural_root_label g (raw_check_structural g tw Hcheck);
       Cyclic.cert_false_live := _;
       Cyclic.cert_advance := _;
       Cyclic.cert_trace_transition := _ |}.
  - intros i w Hibound Hfalse.
    exact (structurally_checked_false_live g i w
      (raw_check_structural g tw Hcheck) Hibound Hfalse).
  - intros i w Hibound Hfalse.
    exact (structurally_checked_advance g i w
      (raw_check_structural g tw Hcheck) Hibound Hfalse).
  - intros i j e Hedge Hlive.
    exact (witness_check_transition g tw i j e
      (raw_check_witness g tw Hcheck) Hedge Hlive).
Defined.

Lemma certify_raw_check_check g tw Hcheck :
  Cyclic.check_certificate (certify_raw_check g tw Hcheck) = true.
Proof. exact Hcheck. Qed.

(** Public soundness theorem for computed graphs.  Search code only has to
    return data [g], [tw] and the decidable equation [raw_check g tw = true];
    all semantic validity then follows from this theorem and the unchanged
    generic cyclic framework. *)
Theorem raw_check_sound g tw :
  Cyclic.raw_check g tw = true ->
  Cyclic.Valid g.(Cyclic.graph_root).
Proof.
  intro Hcheck.
  apply (Cyclic.certificate_sound (certify_raw_check g tw Hcheck)).
  exact Hcheck.
Qed.

(** ** Acyclic certificates for theorem-backed leaves

    Search sometimes closes a node with a genuine object-logic axiom (for
    example identity or ex-falso).  The following one-node construction lets
    those leaves use the very same certificate interface as larger cyclic
    graphs.  It is also useful while testing rule generation independently of
    backlink discovery. *)
Definition empty_trace_witness : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := fun _ => None;
     Cyclic.witness_potential := fun _ => 0 |}.

Definition axiom_graph (a : Cyclic.axiom_instance) : Cyclic.graph :=
  {| Cyclic.graph_root := a.(Cyclic.axiom_conclusion);
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := a.(Cyclic.axiom_conclusion);
           Cyclic.node_payload := Cyclic.AxiomNode a |}] |}.

Lemma axiom_graph_raw_check a :
  Cyclic.raw_check (axiom_graph a) empty_trace_witness = true.
Proof.
  assert (Heq : judgment_eqb a.(Cyclic.axiom_conclusion)
    a.(Cyclic.axiom_conclusion) = true).
  { now apply judgment_eqb_spec. }
  assert (HeqT : FirstOrderTheory.judgment_eqb a.(Cyclic.axiom_conclusion)
    a.(Cyclic.axiom_conclusion) = true).
  { exact Heq. }
  assert (Hnode : Cyclic.node_wfb (axiom_graph a) 0
    {| Cyclic.node_judgment := a.(Cyclic.axiom_conclusion);
       Cyclic.node_payload := Cyclic.AxiomNode a |} = true).
  {
    unfold Cyclic.node_wfb, axiom_graph. simpl.
    exact HeqT.
  }
  unfold axiom_graph in Hnode.
  unfold Cyclic.raw_check, Cyclic.structural_check, axiom_graph,
    Cyclic.node_wfb, Cyclic.all_nodes_wfb_from, Cyclic.all_reachableb,
    Cyclic.reachable_fuel, Cyclic.expand_seen, Cyclic.successors,
    Cyclic.node_at, Cyclic.node_edges, Cyclic.relational_check,
    Cyclic.graph_path_fuel, Cyclic.base_relations_from,
    Relations.relational_trace_check, Relations.path_closure,
    Relations.path_close_once, Relations.path_set_eqb,
    Cyclic.witness_check, Cyclic.witness_edges_from,
    Cyclic.option_tag_wfb, Cyclic.liveb, Cyclic.has_path_of_length,
    empty_trace_witness.
  simpl.
  now rewrite HeqT, Hnode.
Qed.

Definition certify_axiom (a : Cyclic.axiom_instance) : Cyclic.certificate :=
  certify_raw_check (axiom_graph a) empty_trace_witness
    (axiom_graph_raw_check a).

Lemma certify_axiom_check a :
  Cyclic.check_certificate (certify_axiom a) = true.
Proof. exact (axiom_graph_raw_check a). Qed.
