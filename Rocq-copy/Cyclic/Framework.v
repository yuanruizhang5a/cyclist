From Stdlib Require Import List Bool Arith Lia String Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Wellfounded.Lexicographic_Product.
From Stdlib Require Import Wellfounded.Inverse_Image.
From Stdlib Require Import Arith.Wf_nat.

From CyclistRocq.Cyclic Require Import Relations.

Import ListNotations.
Open Scope string_scope.

(** Interface that each object logic must implement before the generic cyclic
    machinery can be instantiated. *)
Module Type THEORY.
  (** [World] is the type of semantic states in which judgments are evaluated.
      [Judgment] is the reified, executable syntax stored at graph nodes. *)
  Parameter World : Type.
  Parameter Judgment : Type.

  (** The semantic sequent is shallow: it is literally a function into
      Rocq's [Prop]. *)
  Definition Sequent : Type := World -> Prop.

  (** Exact Boolean comparison of reified graph labels, used when a rule or
      axiom is installed at a node.  Denotation remains separate because
      arbitrary semantic functions cannot be compared by a Boolean checker. *)
  Parameter judgment_eqb : Judgment -> Judgment -> bool.

  (** Boolean comparison used for backlinks; a theory may deliberately ignore
      trace annotations here while still comparing the logical contents. *)
  Parameter backlink_eqb : Judgment -> Judgment -> bool.

  (** [denote] interprets reified syntax as a semantic predicate. *)
  Parameter denote : Judgment -> Sequent.

  (** [tags] lists the trace identifiers available in a judgment. *)
  Parameter tags : Judgment -> list nat.

  (** A logic supplies the semantic value followed by each trace tag. *)
  Parameter rank : Judgment -> World -> nat -> nat.
End THEORY.

(** Build the executable graph machinery and generic soundness theorem for an
    object logic satisfying [THEORY]. *)
Module Make (T : THEORY).
  (** Re-export the theory's semantic-sequent type inside the generated
      framework module. *)
  Definition Sequent : Type := T.Sequent.

  (** Interpret a reified judgment as its shallow semantic sequent. *)
  Definition sequent_of (j : T.Judgment) : Sequent := T.denote j.

  (** State that a judgment holds at one particular semantic world. *)
  Definition holds (j : T.Judgment) (w : T.World) : Prop := T.denote j w.

  (** A judgment is valid when it holds in every semantic world. *)
  Definition Valid (j : T.Judgment) : Prop := forall w, holds j w.

  (** A pair [(a,b)] routes source tag [a] to target tag [b]. *)
  Definition tag_pair : Type := (nat * nat)%type.

  (** Executable equality for tag pairs. *)
  Definition pair_eqb (x y : tag_pair) : bool :=
    Nat.eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).

  (** Decide whether a tag pair occurs in a list of pairs. *)
  Fixpoint pair_mem (x : tag_pair) (xs : list tag_pair) : bool :=
    match xs with
    | [] => false
    | y :: ys => pair_eqb x y || pair_mem x ys
    end.

  (** Trace information attached to one graph edge.  [edge_valid] contains all
      permitted tag continuations, while [edge_progress] marks the subset that
      must strictly decrease its semantic rank. *)
  Record edge_info : Type := {
    edge_valid : list tag_pair;
    edge_progress : list tag_pair
  }.

  (** Construct the identity trace relation on a list of tags. *)
  Definition identity_pairs (ts : list nat) : list tag_pair :=
    map (fun t => (t, t)) ts.

  (** Semantic interpretation of an edge relation between two worlds: valid
      pairs cannot increase rank and progressing pairs must decrease it. *)
  Definition respects_edge
      (source target : T.Judgment) (w w' : T.World) (e : edge_info) : Prop :=
    (forall a b,
        In (a, b) e.(edge_valid) ->
        T.rank target w' b <= T.rank source w a) /\
    (forall a b,
        In (a, b) e.(edge_progress) ->
        T.rank target w' b < T.rank source w a).

  (** A rule premise consists of its target judgment and the trace relation on
      the edge leading to it. *)
  Record premise : Type := {
    premise_judgment : T.Judgment;
    premise_edge : edge_info
  }.

  (** State that every judgment in a list of premises is semantically valid. *)
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

  (** An axiom instance packages a node label together with a kernel-checked
      proof that the label is valid. *)
  Record axiom_instance : Type := {
    axiom_name : string;
    axiom_conclusion : T.Judgment;
    axiom_theorem : Valid axiom_conclusion
  }.

  (** The four possible states of a proof-graph node.  Inference nodes point to
      all premises; backlink nodes point to one already present companion. *)
  Inductive node_kind : Type :=
  | OpenNode
  | AxiomNode (a : axiom_instance)
  | RuleNode (r : rule_instance) (targets : list nat)
  | BacklinkNode (r : rule_instance) (target : nat).

  (** A graph node pairs its reified judgment label with its proof payload. *)
  Record node : Type := {
    node_judgment : T.Judgment;
    node_payload : node_kind
  }.

  (** A proof graph records the intended root label and an index-addressed list
      of nodes. *)
  Record graph : Type := {
    graph_root : T.Judgment;
    graph_nodes : list node
  }.

  (** Start a graph with one open node at index zero. *)
  Definition start_graph (root : T.Judgment) : graph :=
    {| graph_root := root;
       graph_nodes :=
         [{| node_judgment := root; node_payload := OpenNode |}] |}.

  (** Safely retrieve the node at an index. *)
  Definition node_at (g : graph) (i : nat) : option node :=
    nth_error g.(graph_nodes) i.

  (** Retrieve a node label, falling back to the graph root for an invalid
      index.  Bounds checks ensure this fallback is not accepted as an edge. *)
  Definition label_at (g : graph) (i : nat) : T.Judgment :=
    match node_at g i with
    | Some n => n.(node_judgment)
    | None => g.(graph_root)
    end.

  (** Functional list update that fails when the requested index is absent. *)
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

  (** Generate [count] consecutive fresh node indices beginning at [start]. *)
  Fixpoint fresh_ids (start count : nat) : list nat :=
    match count with
    | 0 => []
    | S count' => start :: fresh_ids (S start) count'
    end.

  (** Turn a rule premise into a newly created open proof node. *)
  Definition open_premise (p : premise) : node :=
    {| node_judgment := p.(premise_judgment);
       node_payload := OpenNode |}.

  (** Close an open node with a matching axiom instance. *)
  (*
    `graph_add_axiom g i a` tries to close open node `i` in graph `g` using axiom `a`.
      It succeeds only when:

      - node `i` exists;
      - node `i` is open;
      - its judgment matches the axiom’s conclusion.

      On success, it replaces the open node with `AxiomNode a` and returns `Some updated_graph`. Otherwise, it returns `None`.
  *)
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

  (** Replace a matching open node by an inference node and append one fresh
      open node for each premise of the rule. *)
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

  (** Close a matching open node by a non-reflexive backlink to an existing
      node, using a unary rule instance to justify the backlink edge. *)
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

  (** Immutable graph-building commands exposed by the script interface. *)
  Inductive command : Type :=
  | CloseWith (i : nat) (a : axiom_instance)
  | ApplyRule (i : nat) (r : rule_instance)
  | AddBacklink (i target : nat) (r : rule_instance).

  (** Script execution state: the latest graph plus a sticky success flag. *)
  Record build_state : Type := {
    built_graph : graph;
    build_ok : bool
  }.

  (** Initialize successful script execution at a fresh root graph. *)
  Definition begin_build (root : T.Judgment) : build_state :=
    {| built_graph := start_graph root; build_ok := true |}.

  (** Execute one command.  Once a command fails, [build_ok] remains false and
      later commands leave the state unchanged. *)
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

  (** Execute a list of graph-building commands from a new root. *)
  Definition run_script (root : T.Judgment) (script : list command)
    : build_state := fold_left execute script (begin_build root).

  (** Enumerate a node's outgoing targets together with their edge relations. *)
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

  (** Return only the target indices of a node's outgoing edges. *)
  Definition successors (g : graph) (i : nat) : list nat :=
    match node_at g i with
    | Some n => map fst (node_edges n)
    | None => []
    end.

  (** Propositional evidence that a particular labelled edge occurs in the
      graph. *)
  Definition edge_at (g : graph) (i j : nat) (e : edge_info) : Prop :=
    exists n, node_at g i = Some n /\ In (j, e) (node_edges n).

  (** Decide membership of a trace tag in a list of tags. *)
  Definition tag_mem (t : nat) (ts : list nat) : bool :=
    existsb (Nat.eqb t) ts.

  (** Check that all edge endpoints are tags of their respective judgments and
      that every progressing pair is also a valid pair. *)
  Definition edge_info_wfb
      (source target : T.Judgment) (e : edge_info) : bool :=
    forallb
      (fun p => tag_mem (fst p) (T.tags source) &&
                tag_mem (snd p) (T.tags target))
      e.(edge_valid) &&
    forallb (fun p => pair_mem p e.(edge_valid)) e.(edge_progress).

  (** Check rule targets and premises in lockstep: arity, bounds, labels, and
      edge trace information must all agree. *)
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

  (** Check the local structural invariants appropriate to one node kind. *)
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

  (** Check every node while supplying its list index to [node_wfb]. *)
  Fixpoint all_nodes_wfb_from
      (g : graph) (index : nat) (ns : list node) : bool :=
    match ns with
    | [] => true
    | n :: ns' =>
        node_wfb g index n && all_nodes_wfb_from g (S index) ns'
    end.

  (** Perform one breadth-style reachability expansion from the accumulated
      set of node indices. *)
  Definition expand_seen (g : graph) (seen : list nat) : list nat :=
    nodup Nat.eq_dec (List.app seen (List.concat (map (successors g) seen))).

  (** Iterate reachability expansion for a caller-supplied amount of fuel. *)
  Fixpoint reachable_fuel (g : graph) (fuel : nat) (seen : list nat)
    : list nat :=
    match fuel with
    | 0 => seen
    | S fuel' => reachable_fuel g fuel' (expand_seen g seen)
    end.

  (** Check that every stored node is reachable from root index zero. *)
  Definition all_reachableb (g : graph) : bool :=
    let reached := reachable_fuel g (List.length g.(graph_nodes)) [0] in
    forallb (fun i => existsb (Nat.eqb i) reached)
      (List.seq 0 (List.length g.(graph_nodes))).

  (** Check root consistency, local node well-formedness, and whole-graph
      reachability. *)
  Definition structural_check (g : graph) : bool :=
    match g.(graph_nodes) with
    | [] => false
    | root :: _ =>
        T.judgment_eqb root.(node_judgment) g.(graph_root) &&
        all_nodes_wfb_from g 0 g.(graph_nodes) &&
        all_reachableb g
    end.

  (** Convert outgoing graph edges into the single-edge path relations consumed
      by the relational trace checker. *)
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

  (** Collect the base path relation for every edge of every graph node. *)
  Fixpoint base_relations_from
      (index : nat) (ns : list node) : list path_relation :=
    match ns with
    | [] => []
    | n :: ns' =>
        List.app (path_of_edges index (node_edges n))
          (base_relations_from (S index) ns')
    end.

  (** Collect and deduplicate every trace tag occurring in the graph. *)
  Definition all_graph_tags (g : graph) : list nat :=
    nodup Nat.eq_dec (List.concat (map (fun n => T.tags n.(node_judgment))
                                       g.(graph_nodes))).

  (** Choose enough fuel to saturate a finite relation over the graph's tag
      space. *)
  Definition relation_fuel (g : graph) : nat :=
    let width := List.length (all_graph_tags g) in
    S (Nat.pow 3 (width * width)).

  (** Choose enough fuel to saturate paths over graph nodes and tag relations. *)
  Definition graph_path_fuel (g : graph) : nat :=
    let n := List.length g.(graph_nodes) in
    S (n * n * relation_fuel g).

  (** Run the executable global trace-condition checker on all graph edges. *)
  Definition relational_check (g : graph) : bool :=
    relational_trace_check (graph_path_fuel g) (relation_fuel g)
      (base_relations_from 0 g.(graph_nodes)).

  (** Decide whether a path of exactly [fuel] edges begins at node [i], with a
      bounded graph node as its endpoint. *)
  Fixpoint has_path_of_length (g : graph) (fuel i : nat) : bool :=
    match fuel with
    | 0 => Nat.ltb i (List.length g.(graph_nodes))
    | S fuel' => existsb (has_path_of_length g fuel') (successors g i)
    end.

  (** A node is live when a path at least as long as the number of graph nodes
      starts there; in a finite graph this witnesses access to a cycle. *)
  Definition liveb (g : graph) (i : nat) : bool :=
    has_path_of_length g (List.length g.(graph_nodes)) i.

  (** A finite routing witness chooses an optional followed tag and an auxiliary
      natural-valued potential at every node index. *)
  Record trace_witness : Type := {
    witness_tag : nat -> option nat;
    witness_potential : nat -> nat
  }.

  (** For live nodes, check that a witness's selected tag—when present—actually
      belongs to the node label. *)
  Definition option_tag_wfb (g : graph) (tw : trace_witness) (i : nat)
    : bool :=
    if liveb g i then
      match tw.(witness_tag) i with
      | None => true
      | Some t => tag_mem t (T.tags (label_at g i))
      end
    else true.

  (** Propositional transition rule for the witness.  Before trace selection the
      auxiliary potential descends; afterward the selected valid pair must
      either progress semantically or descend in auxiliary potential. *)
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

  (** Executable Boolean counterpart of [trace_transition]. *)
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

  (** Check the witness on one outgoing edge whose target is live; edges into
      non-live regions impose no infinite-trace obligation. *)
  Definition edge_witnessb
      (g : graph) (tw : trace_witness) (i : nat)
      (je : nat * edge_info) : bool :=
    let '(j, e) := je in
    if liveb g j then trace_transitionb tw i j e else true.

  (** Check witness tags and all outgoing witness transitions node by node. *)
  Fixpoint witness_edges_from
      (g : graph) (tw : trace_witness) (i : nat) (ns : list node) : bool :=
    match ns with
    | [] => true
    | n :: ns' =>
        option_tag_wfb g tw i &&
        forallb (edge_witnessb g tw i) (node_edges n) &&
        witness_edges_from g tw (S i) ns'
    end.

  (** Run the executable witness check over the complete node list. *)
  Definition witness_check (g : graph) (tw : trace_witness) : bool :=
    witness_edges_from g tw 0 g.(graph_nodes).

  (** Combine structural, relational, and finite-witness checks. *)
  Definition raw_check (g : graph) (tw : trace_witness) : bool :=
    structural_check g && relational_check g && witness_check g tw.

  (** A certificate keeps executable graph data and the semantic evidence that
      cannot be inspected by a Boolean program.  The latter is checked by the
      Rocq kernel when this record is constructed. *)
  Record certificate : Type := {
    (** Executable graph data being certified. *)
    cert_graph : graph;

    (** Finite tag-routing and auxiliary-potential data for that graph. *)
    cert_witness : trace_witness;

    (** Evidence that root index zero exists. *)
    cert_root_bound : 0 < List.length cert_graph.(graph_nodes);

    (** Evidence that node zero carries the declared graph-root judgment. *)
    cert_root_label : label_at cert_graph 0 = cert_graph.(graph_root);

    (** A false node must be live, so countermodel following cannot terminate
        in an axiom or another finite dead end. *)
    cert_false_live :
      forall i w,
        i < List.length cert_graph.(graph_nodes) ->
        ~ holds (label_at cert_graph i) w ->
        liveb cert_graph i = true;
    (** From every false node, select a false successor and semantic world such
        that the chosen edge's rank constraints are respected. *)
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
    (** Every edge leading into a live region obeys the supplied finite trace
        witness. *)
    cert_trace_transition :
      forall i j e,
        edge_at cert_graph i j e ->
        liveb cert_graph j = true ->
        trace_transition cert_witness i j e
  }.

  (** Apply all executable checks to the graph and witness stored in a
      certificate. *)
  Definition check_certificate (c : certificate) : bool :=
    raw_check c.(cert_graph) c.(cert_witness).

  (** The two phases of the well-founded descent argument: before a semantic
      trace is selected, and while a selected trace is being followed. *)
  Inductive descent_measure : Type :=
  | BeforeTrace (potential : nat)
  | FollowingTrace (semantic potential : nat).

  (** Encode the phase-specific measure into nested natural-number pairs.  The
      leading component makes entering [FollowingTrace] a strict decrease. *)
  Definition encode_measure (m : descent_measure) : nat * (nat * nat) :=
    match m with
    | BeforeTrace p => (1, (p, 0))
    | FollowingTrace s p => (0, (s, p))
    end.

  (** Strict lexicographic order on the semantic and auxiliary potentials. *)
  Definition pair_lex : (nat * nat) -> (nat * nat) -> Prop :=
    slexprod nat nat lt lt.

  (** Outer lexicographic order combining trace phase with [pair_lex]. *)
  Definition encoded_lex :
      (nat * (nat * nat)) -> (nat * (nat * nat)) -> Prop :=
    slexprod nat (nat * nat) lt pair_lex.

  (** Pull the nested lexicographic order back to [descent_measure]. *)
  Definition measure_lt (x y : descent_measure) : Prop :=
    encoded_lex (encode_measure x) (encode_measure y).

  (** The combined descent order is well founded because it is built entirely
      from lexicographic products of the well-founded order on naturals. *)
  Lemma measure_lt_wf : well_founded measure_lt.
  Proof.
    unfold measure_lt.
    apply wf_inverse_image.
    unfold encoded_lex, pair_lex.
    apply wf_slexprod.
    - exact lt_wf.
    - apply wf_slexprod; exact lt_wf.
  Qed.

  (** Compute the measure at a node and world.  Before tag selection it uses
      only the finite witness potential; afterward it combines semantic rank
      with that potential. *)
  Definition combined_measure
      (c : certificate) (i : nat) (w : T.World) : descent_measure :=
    match c.(cert_witness).(witness_tag) i with
    | None => BeforeTrace (c.(cert_witness).(witness_potential) i)
    | Some t =>
        FollowingTrace (T.rank (label_at c.(cert_graph) i) w t)
          (c.(cert_witness).(witness_potential) i)
    end.

  (** Following the certificate's chosen countermodel successor strictly
      decreases the combined measure while preserving falsity. *)
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

  (** An accepted proof-carrying certificate establishes semantic validity of
      its root by excluding an infinite descent in [measure_lt]. *)
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

  (** Convenience tactic: apply generic certificate soundness and discharge
      the executable checker equation by evaluation. *)
  Ltac finish_cyclic_certificate cert :=
    apply (certificate_sound cert); vm_compute; reflexivity.
End Make.
