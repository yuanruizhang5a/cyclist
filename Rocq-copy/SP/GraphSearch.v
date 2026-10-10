From Stdlib Require Import List Bool Arith String.

From CyclistRocq.SP Require Import
  Syntax Semantics Rules Certification RuleGeneration.

Import ListNotations.
Open Scope string_scope.

(** * Fuel-bounded graph exploration *)

Fixpoint first_open_from (index : nat) (nodes : list Cyclic.node)
    : option nat :=
  match nodes with
  | [] => None
  | node :: rest =>
      match node.(Cyclic.node_payload) with
      | Cyclic.OpenNode => Some index
      | _ => first_open_from (S index) rest
      end
  end.

Definition first_open (g : Cyclic.graph) : option nat :=
  first_open_from 0 g.(Cyclic.graph_nodes).

Definition graph_closedb (g : Cyclic.graph) : bool :=
  match first_open g with None => true | Some _ => false end.

Definition option_graph_to_list (g : option Cyclic.graph) : list Cyclic.graph :=
  match g with Some graph => [graph] | None => [] end.

Definition axiom_successors g index goal : list Cyclic.graph :=
  match generate_axiom goal with
  | Some axiom => option_graph_to_list (Cyclic.graph_add_axiom g index axiom)
  | None => []
  end.

Definition backlink_successor g index target goal : list Cyclic.graph :=
  option_graph_to_list
    (Cyclic.graph_add_backlink g index target (exact_backlink_rule goal)).

Definition backlink_successors g index goal : list Cyclic.graph :=
  List.concat (map (fun target => backlink_successor g index target goal)
    (List.seq 0 index)).

Definition rule_successors g index goal : list Cyclic.graph :=
  List.concat (map (fun rule =>
    option_graph_to_list (Cyclic.graph_apply_rule g index rule))
    (generate_rules goal)).

(** Axioms have highest priority, followed by exact backlinks and ordinary
    rules.  Unsupported generators contribute the empty list. *)
Definition expand_graph (g : Cyclic.graph) : list Cyclic.graph :=
  match first_open g with
  | None => []
  | Some index =>
      match Cyclic.node_at g index with
      | None => []
      | Some node =>
          let goal := node.(Cyclic.node_judgment) in
          axiom_successors g index goal ++
          backlink_successors g index goal ++
          rule_successors g index goal
      end
  end.

(** Finite witness generation.  The deterministic witness is cheap and
    handles acyclic graphs.  If it fails, bounded enumeration covers every
    node-local tag choice and every potential up to the graph size. *)
Definition nth_with_default {A : Type} (default : A) (xs : list A) (n : nat)
    : A := match nth_error xs n with Some x => x | None => default end.

Definition witness_from_lists
    (tags : list (option nat)) (potentials : list nat) : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := nth_with_default None tags;
     Cyclic.witness_potential := nth_with_default 0 potentials |}.

Definition empty_trace_witness' : Cyclic.trace_witness :=
  witness_from_lists [] [].

Fixpoint choose_lists {A : Type} (choices : list (list A)) : list (list A) :=
  match choices with
  | [] => [[]]
  | options :: rest =>
      List.concat (map (fun option =>
        map (fun suffix => option :: suffix) (choose_lists rest)) options)
  end.

Definition node_tag_choices (node : Cyclic.node) : list (option nat) :=
  None :: map (@Some nat) (judgment_tags node.(Cyclic.node_judgment)).

Definition graph_tag_assignments (g : Cyclic.graph)
    : list (list (option nat)) :=
  choose_lists (map node_tag_choices g.(Cyclic.graph_nodes)).

Definition graph_potential_assignments (g : Cyclic.graph) : list (list nat) :=
  let values := List.seq 0 (S (List.length g.(Cyclic.graph_nodes))) in
  choose_lists (map (fun _ => values) g.(Cyclic.graph_nodes)).

Definition heuristic_tag (g : Cyclic.graph) (index : nat) : option nat :=
  if Cyclic.liveb g index then
    match judgment_tags (Cyclic.label_at g index) with
    | tag :: _ => Some tag
    | [] => None
    end
  else None.

Definition heuristic_witness (g : Cyclic.graph) : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := heuristic_tag g;
     Cyclic.witness_potential := fun _ => 0 |}.

Definition enumerated_witnesses (g : Cyclic.graph) : list Cyclic.trace_witness :=
  List.concat (map (fun tags =>
    map (fun potentials => witness_from_lists tags potentials)
      (graph_potential_assignments g))
    (graph_tag_assignments g)).

Definition witness_candidates (g : Cyclic.graph) : list Cyclic.trace_witness :=
  [empty_trace_witness'; heuristic_witness g] ++ enumerated_witnesses g.

Record checked_graph : Type := {
  checked_graph_data : Cyclic.graph;
  checked_graph_witness : Cyclic.trace_witness;
  checked_graph_equation :
    Cyclic.raw_check checked_graph_data checked_graph_witness = true
}.

Definition check_graph_with_witness (g : Cyclic.graph) (tw : Cyclic.trace_witness)
    : option checked_graph.
Proof.
  destruct (Cyclic.raw_check g tw) eqn:Hcheck.
  - exact (Some
      {| checked_graph_data := g;
         checked_graph_witness := tw;
         checked_graph_equation := Hcheck |}).
  - exact None.
Defined.

Fixpoint try_witnesses (g : Cyclic.graph) (ws : list Cyclic.trace_witness)
    : option checked_graph :=
  match ws with
  | [] => None
  | w :: rest =>
      match check_graph_with_witness g w with
      | Some checked => Some checked
      | None => try_witnesses g rest
      end
  end.

Definition check_closed_graph (g : Cyclic.graph) : option checked_graph :=
  if graph_closedb g then try_witnesses g (witness_candidates g) else None.

(** Search and certification are integrated: a syntactically closed graph
    that fails global progress or witness checking is skipped, and exploration
    continues with the remaining successors. *)
Fixpoint bounded_graph_search_from (fuel : nat) (g : Cyclic.graph)
    : option checked_graph :=
  match check_closed_graph g with
  | Some checked => Some checked
  | None =>
      match fuel with
      | 0 => None
      | S fuel' =>
          let fix try_graphs (graphs : list Cyclic.graph) : option checked_graph :=
            match graphs with
            | [] => None
            | next :: rest =>
                match bounded_graph_search_from fuel' next with
                | Some checked => Some checked
                | None => try_graphs rest
                end
            end in
          try_graphs (expand_graph g)
      end
  end.

Definition bounded_graph_search (fuel : nat) (root : judgment)
    : option checked_graph :=
  bounded_graph_search_from fuel (Cyclic.start_graph root).

Definition certify_searched_graph (fuel : nat) (root : judgment)
    : option Cyclic.certificate :=
  match bounded_graph_search fuel root with
  | Some checked =>
      Some (certify_raw_check checked.(checked_graph_data)
        checked.(checked_graph_witness) checked.(checked_graph_equation))
  | None => None
  end.

Example open_graph_is_not_accepted j :
  check_closed_graph (Cyclic.start_graph j) = None.
Proof. reflexivity. Qed.
