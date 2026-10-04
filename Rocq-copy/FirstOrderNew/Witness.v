From Stdlib Require Import List Bool Arith Lia.
From CyclistRocq.FirstOrderNew Require Export Certification.
Import ListNotations.
Open Scope list_scope.
Open Scope nat_scope.

(** Synthesis for the framework's conservative fixed-per-node trace format.
    All executable operations inspect labels, outgoing edge data, and indices;
    rule theorems and semantic countersteps are never inspected or invoked.
    Some-tag choices are tried before None, one node at a time. There is no
    Cartesian product of complete assignments. *)
Module Make (D : Adapter.DEFINITION_ENV).
  Module Proof := Certification.Certify D.
  Module FO := Proof.FO.
  Module C := FO.Cyclic.

  (** Dynamic programming for paths of EXACTLY [fuel] edges, including dangling
      targets (whose lookup is false). This avoids enumerating paths in a
      branching DAG. The proof below identifies it with the framework liveb. *)
  Fixpoint path_flags (g : C.graph) fuel : list bool :=
    let n := List.length g.(C.graph_nodes) in
    match fuel with
    | 0 => map (fun i => i <? n) (seq 0 n)
    | S fuel' => let previous := path_flags g fuel' in
      map (fun i => existsb (fun j => nth j previous false) (C.successors g i)) (seq 0 n)
    end.
  Definition cached_liveness g := path_flags g (List.length g.(C.graph_nodes)).

  Lemma local_seq_at start len i : i < len -> nth_error (seq start len) i = Some (start+i).
  Proof.
    revert start len; induction i as [|i IH]; intros start [|len] H; cbn; try lia.
    - now rewrite Nat.add_0_r.
    - replace (start+S i) with (S start+i) by lia; apply IH; lia.
  Qed.
  Lemma bool_map_seq_at (f : nat -> bool) n i : i < n ->
    nth i (map f (seq 0 n)) false = f i.
  Proof.
    intro H; apply nth_error_nth; rewrite nth_error_map, (local_seq_at 0 n i H).
    now rewrite Nat.add_0_l.
  Qed.
  Lemma path_flags_length g fuel : List.length (path_flags g fuel) = List.length g.(C.graph_nodes).
  Proof. destruct fuel; cbn [path_flags]; rewrite length_map, length_seq; reflexivity. Qed.
  Lemma outside_has_no_path g fuel i : List.length g.(C.graph_nodes) <= i ->
    C.has_path_of_length g fuel i = false.
  Proof.
    intro H; destruct fuel as [|fuel].
    - cbn [C.has_path_of_length]; apply Nat.ltb_ge; exact H.
    - cbn [C.has_path_of_length]; unfold C.successors, C.node_at.
      assert (nth_error g.(C.graph_nodes) i = None) as E by (apply nth_error_None; exact H).
      rewrite E; reflexivity.
  Qed.
  Lemma existsb_same {A} (f h : A -> bool) xs :
    (forall x, f x = h x) -> existsb f xs = existsb h xs.
  Proof. intro H; induction xs; cbn; [reflexivity|now rewrite H, IHxs]. Qed.
  Lemma forallb_same {A} (f h : A -> bool) xs :
    (forall x, f x = h x) -> forallb f xs = forallb h xs.
  Proof. intro H; induction xs; cbn; [reflexivity|now rewrite H, IHxs]. Qed.
  Lemma path_flags_at g fuel i : nth i (path_flags g fuel) false = C.has_path_of_length g fuel i.
  Proof.
    revert i; induction fuel as [|fuel IH]; intro i;
      destruct (lt_dec i (List.length g.(C.graph_nodes))) as [Hlt|Hge].
    - cbn [path_flags]. rewrite bool_map_seq_at by exact Hlt; reflexivity.
    - rewrite nth_overflow by (rewrite path_flags_length; lia).
      symmetry; apply outside_has_no_path; lia.
    - cbn [path_flags]; rewrite bool_map_seq_at by exact Hlt.
      cbn [C.has_path_of_length]; apply existsb_same; exact IH.
    - rewrite nth_overflow by (rewrite path_flags_length; lia).
      symmetry; apply outside_has_no_path; lia.
  Qed.
  Lemma cached_liveness_at g i : nth i (cached_liveness g) false = C.liveb g i.
  Proof. apply path_flags_at. Qed.

  Record indexed_edge := {
    edge_source : nat;
    edge_target : nat;
    edge_trace : C.edge_info
  }.
  Fixpoint edges_from index (nodes : list C.node) : list indexed_edge := match nodes with
    | [] => []
    | node::rest => map (fun je => {| edge_source := index;
        edge_target := fst je; edge_trace := snd je |}) (C.node_edges node) ++
        edges_from (S index) rest end.
  Record graph_cache := {
    cached_graph : C.graph;
    cached_live : list bool;
    cached_edges : list indexed_edge
  }.
  Definition prepare_graph g :=
    let live := cached_liveness g in
    {| cached_graph := g; cached_live := live;
       cached_edges := filter (fun e => nth e.(edge_target) live false)
         (edges_from 0 g.(C.graph_nodes)) |}.
  Definition cache_correct cache := forall i,
    nth i cache.(cached_live) false = C.liveb cache.(cached_graph) i.
  Lemma prepare_graph_correct g : cache_correct (prepare_graph g).
  Proof. intro i; apply cached_liveness_at. Qed.

  (** nth_error distinguishes an assigned None from an unassigned endpoint. *)
  Definition known_endpoints_ok (assignment : list (option nat)) e :=
    match nth_error assignment e.(edge_source),nth_error assignment e.(edge_target) with
    | Some (Some a),Some (Some b) => C.pair_mem (a,b) e.(edge_trace).(C.edge_valid)
    | Some (Some _),Some None => false
    | _,_ => true end.
  Definition strict_pairs (assignment : list (option nat)) edges := flat_map (fun e =>
    match nth_error assignment e.(edge_source),nth_error assignment e.(edge_target) with
    | Some None,Some None => [(e.(edge_source),e.(edge_target))]
    | Some (Some a),Some (Some b) =>
      if C.pair_mem (a,b) e.(edge_trace).(C.edge_progress) then []
      else [(e.(edge_source),e.(edge_target))]
    | _,_ => [] end) edges.

  (** A strict arc i -> j requires potential(i) >= potential(j)+1.
      Each synchronous round incorporates one more strict-path edge. There are
      n rounds for a completed n-node assignment; a strict cycle never satisfies
      all resulting inequalities and is rejected. Prefix pruning uses k rounds
      for the k currently assigned nodes. *)
  Definition relax_once (strict : list (nat * nat)) (potentials : list nat) :=
    map (fun i => fold_right (fun ij bound =>
      if Nat.eqb i (fst ij) then Nat.max (S (nth (snd ij) potentials 0)) bound else bound)
      (nth i potentials 0) strict) (seq 0 (List.length potentials)).
  Fixpoint relax rounds strict potentials := match rounds with
    | 0 => potentials | S rounds' => relax rounds' strict (relax_once strict potentials) end.
  Definition potentials_for n strict := match strict with
    | [] => repeat 0 n | _ => relax n strict (repeat 0 n) end.
  Definition strict_potentials_ok strict potentials := forallb
    (fun ij => nth (snd ij) potentials 0 <? nth (fst ij) potentials 0) strict.
  Definition prefix_ok cache assignment :=
    forallb (known_endpoints_ok assignment) cache.(cached_edges) &&
    let strict := strict_pairs assignment cache.(cached_edges) in
    strict_potentials_ok strict (potentials_for (List.length assignment) strict).
  Definition node_choices cache index : list (option nat) :=
    if nth index cache.(cached_live) false then
      map (@Some nat) (FO.Theory.tags (C.label_at cache.(cached_graph) index)) ++ [None]
    else [None].

  (** Memoized evaluation of exactly C.witness_check, not a weaker acceptor. *)
  Definition memo_tag_wfb g live (tw : C.trace_witness) i :=
    if nth i live false then match tw.(C.witness_tag) i with
      | None => true | Some t => C.tag_mem t (FO.Theory.tags (C.label_at g i)) end
    else true.
  Definition memo_edge_witnessb live (tw : C.trace_witness) i je :=
    let '(j,e) := je in
    if nth j live false then C.trace_transitionb tw i j e else true.
  Fixpoint memo_witness_edges_from g live tw index (nodes : list C.node) := match nodes with
    | [] => true
    | node::rest => memo_tag_wfb g live tw index &&
        forallb (memo_edge_witnessb live tw index) (C.node_edges node) &&
        memo_witness_edges_from g live tw (S index) rest end.
  Definition memo_witness_check cache tw :=
    memo_witness_edges_from cache.(cached_graph) cache.(cached_live) tw 0
      cache.(cached_graph).(C.graph_nodes).
  Lemma memo_witness_edges_correct g live tw index nodes :
    (forall i, nth i live false = C.liveb g i) ->
    memo_witness_edges_from g live tw index nodes = C.witness_edges_from g tw index nodes.
  Proof.
    intro H; revert index; induction nodes as [|node nodes IH]; intro index; cbn; [reflexivity|].
    unfold memo_tag_wfb, C.option_tag_wfb; rewrite H, IH.
    assert (forallb (memo_edge_witnessb live tw index) (C.node_edges node) =
      forallb (C.edge_witnessb g tw index) (C.node_edges node)) as E.
    { apply forallb_same; intros [j e]. unfold memo_edge_witnessb, C.edge_witnessb; cbn.
      now rewrite H. }
    now rewrite E.
  Qed.
  Lemma memo_witness_check_correct cache tw : cache_correct cache ->
    memo_witness_check cache tw = C.witness_check cache.(cached_graph) tw.
  Proof. apply memo_witness_edges_correct. Qed.
  Definition materialize assignment potentials : C.trace_witness :=
    {| C.witness_tag := fun i => nth i assignment None;
       C.witness_potential := fun i => nth i potentials 0 |}.
  Definition checked_candidate cache assignment : option C.trace_witness :=
    let strict := strict_pairs assignment cache.(cached_edges) in
    let tw := materialize assignment
      (potentials_for (List.length cache.(cached_graph).(C.graph_nodes)) strict) in
    if memo_witness_check cache tw then Some tw else None.
  Lemma checked_candidate_sound cache assignment tw : cache_correct cache ->
    checked_candidate cache assignment = Some tw -> C.witness_check cache.(cached_graph) tw = true.
  Proof.
    intros Hcache; unfold checked_candidate.
    destruct (memo_witness_check cache _) eqn:E; [|discriminate].
    intro H; inversion H; subst tw.
    rewrite <- memo_witness_check_correct by exact Hcache; exact E.
  Qed.

  (** The second component counts actual attempted node choices. Failed
      prefixes consume no work below that prefix. The nested loop is structural
      on the node's finite choices; recursive DFS is structural on node fuel. *)
  Fixpoint choose_first {A B} (f : A -> option B * nat) xs : option B * nat := match xs with
    | [] => (None,0)
    | x::rest => let '(result,work) := f x in match result with
      | Some found => (Some found,S work)
      | None => let '(later,later_work) := choose_first f rest in
                (later,S (work + later_work)) end end.
  Lemma choose_first_some {A B} (f : A -> option B * nat) xs found :
    fst (choose_first f xs) = Some found -> exists x, In x xs /\ fst (f x) = Some found.
  Proof.
    induction xs as [|x xs IH]; cbn; [discriminate|].
    destruct (f x) as [[value|] work] eqn:E; cbn.
    - intro H; inversion H; subst value; exists x; split; [now left|now rewrite E].
    - destruct (choose_first f xs) as [later count] eqn:F; cbn.
      intro H; destruct (IH H) as [y [Hy Ey]]; exists y; auto.
  Qed.
  Fixpoint search_assignments fuel cache index assignment : option C.trace_witness * nat :=
    match fuel with
    | 0 => (checked_candidate cache assignment,0)
    | S fuel' => choose_first (fun choice =>
        let assignment' := assignment ++ [choice] in
        if prefix_ok cache assignment' then search_assignments fuel' cache (S index) assignment'
        else (None,0)) (node_choices cache index)
    end.
  Lemma search_assignments_sound fuel cache index assignment tw : cache_correct cache ->
    fst (search_assignments fuel cache index assignment) = Some tw ->
    C.witness_check cache.(cached_graph) tw = true.
  Proof.
    revert index assignment; induction fuel as [|fuel IH]; intros index assignment Hcache Hfound.
    - exact (checked_candidate_sound cache assignment tw Hcache Hfound).
    - apply choose_first_some in Hfound; destruct Hfound as [choice [_ Hfound]].
      change (fst (if prefix_ok cache (assignment ++ [choice]) then
        search_assignments fuel cache (S index) (assignment ++ [choice]) else (None,0)) = Some tw)
        in Hfound.
      destruct (prefix_ok cache (assignment ++ [choice]));
        [eapply IH; [exact Hcache|exact Hfound]|discriminate].
  Qed.
  Definition find_witness_stats (g : C.graph) : option C.trace_witness * nat :=
    search_assignments (List.length g.(C.graph_nodes)) (prepare_graph g) 0 [].
  Definition find_witness (g : C.graph) : option C.trace_witness := fst (find_witness_stats g).
  Theorem find_witness_sound g tw : find_witness g = Some tw -> C.witness_check g tw = true.
  Proof.
    intro H; exact (search_assignments_sound (List.length g.(C.graph_nodes))
      (prepare_graph g) 0 [] tw (prepare_graph_correct g) H).
  Qed.
  Definition partial_check g := match find_witness g with Some _ => true | None => false end.
  Theorem partial_check_sound g : partial_check g = true ->
    exists tw, find_witness g = Some tw /\ C.witness_check g tw = true.
  Proof.
    unfold partial_check; destruct (find_witness g) as [tw|] eqn:E; [|discriminate].
    intros _; exists tw; split; [reflexivity|now apply find_witness_sound].
  Qed.
End Make.
