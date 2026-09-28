From Stdlib Require Import List Bool Arith Lia String Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Wellfounded.Lexicographic_Product.
From Stdlib Require Import Wellfounded.Inverse_Image.
From Stdlib Require Import Arith.Wf_nat.

From CyclistRocq.Cyclic Require Import Relations.

Import ListNotations.
Open Scope string_scope.

Module Type THEORY.
  Parameter World : Type.
  Parameter Judgment : Type.

  (** The semantic sequent is shallow: it is literally a function into
      Rocq's [Prop]. *)
  Definition Sequent : Type := World -> Prop.

  (** Equality here is equality of reified graph labels.  The denotation is
      deliberately separate, so a judgment may denote a shallow function even
      though arbitrary functions cannot be compared by a Boolean checker. *)
  Parameter judgment_eqb : Judgment -> Judgment -> bool.
  Parameter backlink_eqb : Judgment -> Judgment -> bool.

  Parameter denote : Judgment -> Sequent.
  Parameter tags : Judgment -> list nat.

  (** A logic supplies the semantic value followed by each trace tag. *)
  Parameter rank : Judgment -> World -> nat -> nat.
End THEORY.

Module Make (T : THEORY).
  Definition Sequent : Type := T.Sequent.
  Definition sequent_of (j : T.Judgment) : Sequent := T.denote j.
  Definition holds (j : T.Judgment) (w : T.World) : Prop := T.denote j w.
  Definition Valid (j : T.Judgment) : Prop := forall w, holds j w.

  Definition tag_pair : Type := (nat * nat)%type.

  Definition pair_eqb (x y : tag_pair) : bool :=
    Nat.eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).

  Fixpoint pair_mem (x : tag_pair) (xs : list tag_pair) : bool :=
    match xs with
    | [] => false
    | y :: ys => pair_eqb x y || pair_mem x ys
    end.

  Record edge_info : Type := {
    edge_valid : list tag_pair;
    edge_progress : list tag_pair
  }.

  Definition identity_pairs (ts : list nat) : list tag_pair :=
    map (fun t => (t, t)) ts.

  Definition respects_edge
      (source target : T.Judgment) (w w' : T.World) (e : edge_info) : Prop :=
    (forall a b,
        In (a, b) e.(edge_valid) ->
        T.rank target w' b <= T.rank source w a) /\
    (forall a b,
        In (a, b) e.(edge_progress) ->
        T.rank target w' b < T.rank source w a).

  Record premise : Type := {
    premise_judgment : T.Judgment;
    premise_edge : edge_info
  }.

  Definition premises_valid (ps : list premise) : Prop :=
    forall p, In p ps -> Valid p.(premise_judgment).

  (** Besides the ordinary theorem, a cyclic rule records the standard local
      countermodel/trace obligation used in cyclic-proof soundness proofs. *)
  Record rule_instance : Type := {
    rule_name : string;
    rule_conclusion : T.Judgment;
    rule_premises : list premise;
    rule_theorem : premises_valid rule_premises -> Valid rule_conclusion;
    rule_counter_step :
      forall w, ~ holds rule_conclusion w ->
      { k : nat &
        { p : premise &
          { w' : T.World |
            nth_error rule_premises k = Some p /\
            ~ holds p.(premise_judgment) w' /\
            respects_edge rule_conclusion p.(premise_judgment) w w'
              p.(premise_edge) } } }
  }.

  Record axiom_instance : Type := {
    axiom_name : string;
    axiom_conclusion : T.Judgment;
    axiom_theorem : Valid axiom_conclusion
  }.

  Inductive node_kind : Type :=
  | OpenNode
  | AxiomNode (a : axiom_instance)
  | RuleNode (r : rule_instance) (targets : list nat)
  | BacklinkNode (r : rule_instance) (target : nat).

  Record node : Type := {
    node_judgment : T.Judgment;
    node_payload : node_kind
  }.

  Record graph : Type := {
    graph_root : T.Judgment;
    graph_nodes : list node
  }.

  Definition start_graph (root : T.Judgment) : graph :=
    {| graph_root := root;
       graph_nodes :=
         [{| node_judgment := root; node_payload := OpenNode |}] |}.

  Definition node_at (g : graph) (i : nat) : option node :=
    nth_error g.(graph_nodes) i.

  Definition label_at (g : graph) (i : nat) : T.Judgment :=
    match node_at g i with
    | Some n => n.(node_judgment)
    | None => g.(graph_root)
    end.

  Fixpoint replace_nth {A : Type} (i : nat) (x : A) (xs : list A)
    : option (list A) :=
    match i, xs with
    | 0, _ :: ys => Some (x :: ys)
    | S i', y :: ys =>
        match replace_nth i' x ys with
        | Some ys' => Some (y :: ys')
        | None => None
        end
    | _, _ => None
    end.

  Fixpoint fresh_ids (start count : nat) : list nat :=
    match count with
    | 0 => []
    | S count' => start :: fresh_ids (S start) count'
    end.

  Definition open_premise (p : premise) : node :=
    {| node_judgment := p.(premise_judgment);
       node_payload := OpenNode |}.

  Definition graph_add_axiom
      (g : graph) (i : nat) (a : axiom_instance) : option graph :=
    match node_at g i with
    | Some n =>
        match n.(node_payload) with
        | OpenNode =>
            if T.judgment_eqb n.(node_judgment) a.(axiom_conclusion) then
              match replace_nth i
                {| node_judgment := n.(node_judgment);
                   node_payload := AxiomNode a |}
                g.(graph_nodes) with
              | Some ns => Some {| graph_root := g.(graph_root);
                                   graph_nodes := ns |}
              | None => None
              end
            else None
        | _ => None
        end
    | None => None
    end.

  Definition graph_apply_rule
      (g : graph) (i : nat) (r : rule_instance) : option graph :=
    match node_at g i with
    | Some n =>
        match n.(node_payload) with
        | OpenNode =>
            if T.judgment_eqb n.(node_judgment) r.(rule_conclusion) then
              let first := List.length g.(graph_nodes) in
              let ids := fresh_ids first (List.length r.(rule_premises)) in
              let parent :=
                {| node_judgment := n.(node_judgment);
                   node_payload := RuleNode r ids |} in
              match replace_nth i parent g.(graph_nodes) with
              | Some ns =>
                  Some {| graph_root := g.(graph_root);
                          graph_nodes := List.app ns (map open_premise r.(rule_premises)) |}
              | None => None
              end
            else None
        | _ => None
        end
    | None => None
    end.

  Definition graph_add_backlink
      (g : graph) (i target : nat) (r : rule_instance) : option graph :=
    match node_at g i, node_at g target, r.(rule_premises) with
    | Some n, Some target_node, [p] =>
        match n.(node_payload) with
        | OpenNode =>
            if T.judgment_eqb n.(node_judgment) r.(rule_conclusion) &&
               T.judgment_eqb target_node.(node_judgment)
                 p.(premise_judgment) &&
               T.backlink_eqb n.(node_judgment)
                 target_node.(node_judgment) &&
               negb (Nat.eqb i target) then
              match replace_nth i
                {| node_judgment := n.(node_judgment);
                   node_payload := BacklinkNode r target |}
                g.(graph_nodes) with
              | Some ns => Some {| graph_root := g.(graph_root);
                                   graph_nodes := ns |}
              | None => None
              end
            else None
        | _ => None
        end
    | _, _, _ => None
    end.

  Inductive command : Type :=
  | CloseWith (i : nat) (a : axiom_instance)
  | ApplyRule (i : nat) (r : rule_instance)
  | AddBacklink (i target : nat) (r : rule_instance).

  Record build_state : Type := {
    built_graph : graph;
    build_ok : bool
  }.

  Definition begin_build (root : T.Judgment) : build_state :=
    {| built_graph := start_graph root; build_ok := true |}.

  Definition execute (st : build_state) (c : command) : build_state :=
    if negb st.(build_ok) then st else
    let result :=
      match c with
      | CloseWith i a => graph_add_axiom st.(built_graph) i a
      | ApplyRule i r => graph_apply_rule st.(built_graph) i r
      | AddBacklink i target r =>
          graph_add_backlink st.(built_graph) i target r
      end in
    match result with
    | Some g => {| built_graph := g; build_ok := true |}
    | None => {| built_graph := st.(built_graph); build_ok := false |}
    end.

  Definition run_script (root : T.Judgment) (script : list command)
    : build_state := fold_left execute script (begin_build root).

  Definition node_edges (n : node) : list (nat * edge_info) :=
    match n.(node_payload) with
    | RuleNode r targets =>
        combine targets (map premise_edge r.(rule_premises))
    | BacklinkNode r target =>
        match r.(rule_premises) with
        | [p] => [(target, p.(premise_edge))]
        | _ => []
        end
    | _ => []
    end.

  Definition successors (g : graph) (i : nat) : list nat :=
    match node_at g i with
    | Some n => map fst (node_edges n)
    | None => []
    end.

  Definition edge_at (g : graph) (i j : nat) (e : edge_info) : Prop :=
    exists n, node_at g i = Some n /\ In (j, e) (node_edges n).

  Definition tag_mem (t : nat) (ts : list nat) : bool :=
    existsb (Nat.eqb t) ts.

  Definition edge_info_wfb
      (source target : T.Judgment) (e : edge_info) : bool :=
    forallb
      (fun p => tag_mem (fst p) (T.tags source) &&
                tag_mem (snd p) (T.tags target))
      e.(edge_valid) &&
    forallb (fun p => pair_mem p e.(edge_valid)) e.(edge_progress).

  (** Check arity, target labels, and trace relations together. *)
  Fixpoint targets_wfb_from
      (g : graph) (source : T.Judgment)
      (targets : list nat) (ps : list premise) : bool :=
    match targets, ps with
    | [], [] => true
    | i :: is, p :: ps' =>
        Nat.ltb i (List.length g.(graph_nodes)) &&
        T.judgment_eqb (label_at g i) p.(premise_judgment) &&
        edge_info_wfb source p.(premise_judgment) p.(premise_edge) &&
        targets_wfb_from g source is ps'
    | _, _ => false
    end.

  Definition node_wfb (g : graph) (index : nat) (n : node) : bool :=
    match n.(node_payload) with
    | OpenNode => false
    | AxiomNode a =>
        T.judgment_eqb n.(node_judgment) a.(axiom_conclusion)
    | RuleNode r targets =>
        T.judgment_eqb n.(node_judgment) r.(rule_conclusion) &&
        targets_wfb_from g n.(node_judgment) targets r.(rule_premises)
    | BacklinkNode r target =>
        T.judgment_eqb n.(node_judgment) r.(rule_conclusion) &&
        negb (Nat.eqb index target) &&
        T.backlink_eqb n.(node_judgment) (label_at g target) &&
        match r.(rule_premises) with
        | [p] =>
            Nat.ltb target (List.length g.(graph_nodes)) &&
            T.judgment_eqb (label_at g target) p.(premise_judgment) &&
            edge_info_wfb n.(node_judgment) p.(premise_judgment)
              p.(premise_edge)
        | _ => false
        end
    end.

  Fixpoint all_nodes_wfb_from
      (g : graph) (index : nat) (ns : list node) : bool :=
    match ns with
    | [] => true
    | n :: ns' =>
        node_wfb g index n && all_nodes_wfb_from g (S index) ns'
    end.

  Definition expand_seen (g : graph) (seen : list nat) : list nat :=
    nodup Nat.eq_dec (List.app seen (List.concat (map (successors g) seen))).

  Fixpoint reachable_fuel (g : graph) (fuel : nat) (seen : list nat)
    : list nat :=
    match fuel with
    | 0 => seen
    | S fuel' => reachable_fuel g fuel' (expand_seen g seen)
    end.

  Definition all_reachableb (g : graph) : bool :=
    let reached := reachable_fuel g (List.length g.(graph_nodes)) [0] in
    forallb (fun i => existsb (Nat.eqb i) reached)
      (List.seq 0 (List.length g.(graph_nodes))).

  Definition structural_check (g : graph) : bool :=
    match g.(graph_nodes) with
    | [] => false
    | root :: _ =>
        T.judgment_eqb root.(node_judgment) g.(graph_root) &&
        all_nodes_wfb_from g 0 g.(graph_nodes) &&
        all_reachableb g
    end.

  Fixpoint path_of_edges
      (source : nat) (es : list (nat * edge_info)) : list path_relation :=
    match es with
    | [] => []
    | (target, e) :: es' =>
        let arcs :=
          map
            (fun p =>
               {| arc_source := fst p;
                  arc_target := snd p;
                  arc_slope :=
                    if pair_mem p e.(edge_progress)
                    then Decrease else Stay |})
            e.(edge_valid) in
        {| path_source := source;
           path_target := target;
           path_arcs := arcs |} :: path_of_edges source es'
    end.

  Fixpoint base_relations_from
      (index : nat) (ns : list node) : list path_relation :=
    match ns with
    | [] => []
    | n :: ns' =>
        List.app (path_of_edges index (node_edges n))
          (base_relations_from (S index) ns')
    end.

  Definition all_graph_tags (g : graph) : list nat :=
    nodup Nat.eq_dec (List.concat (map (fun n => T.tags n.(node_judgment))
                                       g.(graph_nodes))).

  Definition relation_fuel (g : graph) : nat :=
    let width := List.length (all_graph_tags g) in
    S (Nat.pow 3 (width * width)).

  Definition graph_path_fuel (g : graph) : nat :=
    let n := List.length g.(graph_nodes) in
    S (n * n * relation_fuel g).

  Definition relational_check (g : graph) : bool :=
    relational_trace_check (graph_path_fuel g) (relation_fuel g)
      (base_relations_from 0 g.(graph_nodes)).

  Fixpoint has_path_of_length (g : graph) (fuel i : nat) : bool :=
    match fuel with
    | 0 => Nat.ltb i (List.length g.(graph_nodes))
    | S fuel' => existsb (has_path_of_length g fuel') (successors g i)
    end.

  Definition liveb (g : graph) (i : nat) : bool :=
    has_path_of_length g (List.length g.(graph_nodes)) i.

  Record trace_witness : Type := {
    witness_tag : nat -> option nat;
    witness_potential : nat -> nat
  }.

  Definition option_tag_wfb (g : graph) (tw : trace_witness) (i : nat)
    : bool :=
    if liveb g i then
      match tw.(witness_tag) i with
      | None => true
      | Some t => tag_mem t (T.tags (label_at g i))
      end
    else true.

  Definition trace_transition
      (tw : trace_witness) (i j : nat) (e : edge_info) : Prop :=
    match tw.(witness_tag) i, tw.(witness_tag) j with
    | None, None => tw.(witness_potential) j < tw.(witness_potential) i
    | None, Some _ => True
    | Some _, None => False
    | Some a, Some b =>
        In (a, b) e.(edge_valid) /\
        (In (a, b) e.(edge_progress) \/
         tw.(witness_potential) j < tw.(witness_potential) i)
    end.

  Definition trace_transitionb
      (tw : trace_witness) (i j : nat) (e : edge_info) : bool :=
    match tw.(witness_tag) i, tw.(witness_tag) j with
    | None, None => Nat.ltb (tw.(witness_potential) j) (tw.(witness_potential) i)
    | None, Some _ => true
    | Some _, None => false
    | Some a, Some b =>
        pair_mem (a, b) e.(edge_valid) &&
        (pair_mem (a, b) e.(edge_progress) ||
         Nat.ltb (tw.(witness_potential) j) (tw.(witness_potential) i))
    end.

  Definition edge_witnessb
      (g : graph) (tw : trace_witness) (i : nat)
      (je : nat * edge_info) : bool :=
    let '(j, e) := je in
    if liveb g j then trace_transitionb tw i j e else true.

  Fixpoint witness_edges_from
      (g : graph) (tw : trace_witness) (i : nat) (ns : list node) : bool :=
    match ns with
    | [] => true
    | n :: ns' =>
        option_tag_wfb g tw i &&
        forallb (edge_witnessb g tw i) (node_edges n) &&
        witness_edges_from g tw (S i) ns'
    end.

  Definition witness_check (g : graph) (tw : trace_witness) : bool :=
    witness_edges_from g tw 0 g.(graph_nodes).

  Definition raw_check (g : graph) (tw : trace_witness) : bool :=
    structural_check g && relational_check g && witness_check g tw.

  (** A certificate keeps executable graph data and the semantic evidence that
      cannot be inspected by a Boolean program.  The latter is checked by the
      Rocq kernel when this record is constructed. *)
  Record certificate : Type := {
    cert_graph : graph;
    cert_witness : trace_witness;
    cert_root_bound : 0 < List.length cert_graph.(graph_nodes);
    cert_root_label : label_at cert_graph 0 = cert_graph.(graph_root);
    cert_false_live :
      forall i w,
        i < List.length cert_graph.(graph_nodes) ->
        ~ holds (label_at cert_graph i) w ->
        liveb cert_graph i = true;
    cert_advance :
      forall i w,
        i < List.length cert_graph.(graph_nodes) ->
        ~ holds (label_at cert_graph i) w ->
        { j : nat &
          { w' : T.World &
            { e : edge_info |
              edge_at cert_graph i j e /\
              j < List.length cert_graph.(graph_nodes) /\
              ~ holds (label_at cert_graph j) w' /\
              respects_edge (label_at cert_graph i) (label_at cert_graph j)
                w w' e } } };
    cert_trace_transition :
      forall i j e,
        edge_at cert_graph i j e ->
        liveb cert_graph j = true ->
        trace_transition cert_witness i j e
  }.

  Definition check_certificate (c : certificate) : bool :=
    raw_check c.(cert_graph) c.(cert_witness).

  Inductive descent_measure : Type :=
  | BeforeTrace (potential : nat)
  | FollowingTrace (semantic potential : nat).

  Definition encode_measure (m : descent_measure) : nat * (nat * nat) :=
    match m with
    | BeforeTrace p => (1, (p, 0))
    | FollowingTrace s p => (0, (s, p))
    end.

  Definition pair_lex : (nat * nat) -> (nat * nat) -> Prop :=
    slexprod nat nat lt lt.

  Definition encoded_lex :
      (nat * (nat * nat)) -> (nat * (nat * nat)) -> Prop :=
    slexprod nat (nat * nat) lt pair_lex.

  Definition measure_lt (x y : descent_measure) : Prop :=
    encoded_lex (encode_measure x) (encode_measure y).

  Lemma measure_lt_wf : well_founded measure_lt.
  Proof.
    unfold measure_lt.
    apply wf_inverse_image.
    unfold encoded_lex, pair_lex.
    apply wf_slexprod.
    - exact lt_wf.
    - apply wf_slexprod; exact lt_wf.
  Qed.

  Definition combined_measure
      (c : certificate) (i : nat) (w : T.World) : descent_measure :=
    match c.(cert_witness).(witness_tag) i with
    | None => BeforeTrace (c.(cert_witness).(witness_potential) i)
    | Some t =>
        FollowingTrace (T.rank (label_at c.(cert_graph) i) w t)
          (c.(cert_witness).(witness_potential) i)
    end.

  Lemma certificate_step_decreases
      (c : certificate) (i : nat) (w : T.World)
      (Hi : i < List.length c.(cert_graph).(graph_nodes))
      (Hfalse : ~ holds (label_at c.(cert_graph) i) w) :
    { j : nat &
      { w' : T.World |
        j < List.length c.(cert_graph).(graph_nodes) /\
        ~ holds (label_at c.(cert_graph) j) w' /\
        measure_lt (combined_measure c j w') (combined_measure c i w) } }.
  Proof.
    destruct (c.(cert_advance) i w Hi Hfalse)
      as [j [w' [e [Hedge [Hj [Hfalse' Hrespect]]]]]].
    pose proof (c.(cert_false_live) j w' Hj Hfalse') as Hlive.
    pose proof (c.(cert_trace_transition) i j e Hedge Hlive) as Htrace.
    exists j, w'.
    split; [exact Hj|].
    split; [exact Hfalse'|].
    destruct Hrespect as [Hvalid Hprogress].
    unfold combined_measure, trace_transition in *.
    destruct (witness_tag (cert_witness c) i) as [a|] eqn:Hti;
      destruct (witness_tag (cert_witness c) j) as [b|] eqn:Htj;
      simpl in *.
    - destruct Htrace as [Hab [Hprog | Hpot]].
      + specialize (Hprogress a b Hprog).
        unfold measure_lt, encoded_lex, pair_lex; simpl.
        apply right_slex. apply left_slex. exact Hprogress.
      + specialize (Hvalid a b Hab).
        unfold measure_lt, encoded_lex, pair_lex; simpl.
        apply right_slex.
        destruct (proj1 (Nat.lt_eq_cases _ _) Hvalid) as [Hlt | Heq].
        * apply left_slex. exact Hlt.
        * rewrite Heq. apply right_slex. exact Hpot.
    - contradiction.
    - unfold measure_lt, encoded_lex, pair_lex; simpl.
      apply left_slex. lia.
    - unfold measure_lt, encoded_lex, pair_lex; simpl.
      apply right_slex. apply left_slex. exact Htrace.
  Qed.

  Theorem certificate_sound (c : certificate) :
    check_certificate c = true -> Valid c.(cert_graph).(graph_root).
  Proof.
    intros _ w.
    apply NNPP; intro Hfalse.
    set (P := fun m : descent_measure =>
      forall i w,
        i < List.length c.(cert_graph).(graph_nodes) ->
        combined_measure c i w = m ->
        ~ holds (label_at c.(cert_graph) i) w -> False).
    assert (Hall : forall m, P m).
    {
      apply (well_founded_induction_type measure_lt_wf P).
      intros m IH i world Hi Hm Hbad.
      destruct (certificate_step_decreases c i world Hi Hbad)
        as [j [w' [Hj [Hbad' Hdecr]]]].
      rewrite Hm in Hdecr.
      eapply (IH (combined_measure c j w') Hdecr j w').
      - exact Hj.
      - reflexivity.
      - exact Hbad'.
    }
    eapply (Hall (combined_measure c 0 w) 0 w).
    - exact c.(cert_root_bound).
    - reflexivity.
    - rewrite c.(cert_root_label). exact Hfalse.
  Qed.

  Ltac finish_cyclic_certificate cert :=
    apply (certificate_sound cert); vm_compute; reflexivity.
End Make.
