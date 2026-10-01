From Stdlib Require Import List Bool Arith Lia String.

From CyclistRocq.FirstOrder Require Import
  Syntax Semantics Rules Automation Certification RuleGeneration.

Import ListNotations.
Open Scope string_scope.

(** * Total bounded exploration of cyclic proof graphs

    The generic framework already supplies immutable graph-building
    operations.  This module only chooses which verified operation to try.
    Every graph is rechecked after search; an accidental bug in this explorer
    can therefore cause incompleteness, but cannot turn an invalid graph into a
    theorem.

    Search expands the first open node.  Earlier indices have consequently
    already been closed, so exact backlinks always point to closed ancestors.
    The expansion order follows the OCaml priority among the rule families
    currently ported: axiom, backlink, propositional rules, right unfolding,
    and left unfolding. *)

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

Definition option_graph_to_list (candidate : option Cyclic.graph)
    : list Cyclic.graph :=
  match candidate with Some g => [g] | None => [] end.

(** ** Explicit preparation of non-exact backlinks

    The generic framework intentionally accepts only exact backlink labels.
    As in the OCaml [dobackl] routine, search therefore inserts ordinary
    weakening and substitution nodes first.  The helpers below merely detect
    those situations; the returned transformations are the theorem-backed
    rules from [Rules.v]. *)

Definition atom_search_terms (a : atom) : list term :=
  match a with
  | Eq x y | Neq x y => [x; y]
  | Pred _ _ args => args
  end.

Definition product_search_terms (p : product) : list term :=
  List.concat (map atom_search_terms p).

Definition formula_search_terms (f : formula) : list term :=
  List.concat (map product_search_terms f).

Definition judgment_search_terms (j : judgment) : list term :=
  (formula_search_terms j.(judgment_sequent).(antecedent) ++
   formula_search_terms j.(judgment_sequent).(succedent))%list.

Definition subst_judgment (s : substitution) (j : judgment) : judgment :=
  mk_judgment j.(judgment_definitions)
    (subst_sequent s j.(judgment_sequent)).

(** Recheck the whole judgment after term matching.  The matcher sees only a
    flattened term list, so this guard verifies predicate names, tags,
    connectives, definitions, and list shape as well. *)
Definition checked_judgment_match (pattern target : judgment)
    : option substitution :=
  match match_terms (judgment_search_terms pattern)
    (judgment_search_terms target) with
  | Some s =>
      if judgment_eqb (subst_judgment s pattern) target then Some s else None
  | None => None
  end.

Definition substitution_rule_to_ancestor
    (current ancestor : judgment) : option Cyclic.rule_instance.
Proof.
  destruct (checked_judgment_match ancestor current) as [s|] eqn:Hmatch;
    [|exact None].
  destruct s as [|binding rest]; [exact None|].
  set (whole := binding :: rest).
  destruct (free_substitutionb whole) eqn:Hfree; [|exact None].
  exact (Some (general_free_substitution_rule
    ancestor.(judgment_definitions) ancestor.(judgment_sequent)
    whole Hfree)).
Defined.

(** Try to view the current singleton antecedent as
    [instantiated_ancestor_product ++ extra].  Matching is performed against
    the prefix of the current product having the ancestor's length. *)
Definition weakening_rule_to_ancestor
    (current ancestor : judgment) : option Cyclic.rule_instance :=
  match current.(judgment_sequent).(antecedent),
        ancestor.(judgment_sequent).(antecedent) with
  | [big], [pattern] =>
      let small := firstn (List.length pattern) big in
      let extra := skipn (List.length pattern) big in
      match extra with
      | [] => None
      | _ :: _ =>
          let projected := mk_judgment current.(judgment_definitions)
            (mk_sequent [small] current.(judgment_sequent).(succedent)) in
          match checked_judgment_match ancestor projected with
          | Some _ => Some (prefix_weakening_rule
              current.(judgment_definitions) small extra
              current.(judgment_sequent).(succedent))
          | None => None
          end
      end
  | _, _ => None
  end.

Definition prepared_backlink_successor
    (g : Cyclic.graph) (open_index target : nat) (goal : judgment)
    : list Cyclic.graph :=
  match Cyclic.node_at g target with
  | None => []
  | Some ancestor_node =>
      let ancestor := ancestor_node.(Cyclic.node_judgment) in
      (match substitution_rule_to_ancestor goal ancestor with
       | Some rule => option_graph_to_list
           (Cyclic.graph_apply_rule g open_index rule)
       | None => []
       end ++
       match weakening_rule_to_ancestor goal ancestor with
       | Some rule => option_graph_to_list
           (Cyclic.graph_apply_rule g open_index rule)
       | None => []
       end)%list
  end.

Definition prepared_backlink_successors
    (g : Cyclic.graph) (open_index : nat) (goal : judgment)
    : list Cyclic.graph :=
  List.concat (map (fun target =>
    prepared_backlink_successor g open_index target goal)
    (List.seq 0 open_index)).

(** Generate exact backlink successors to indices [0 .. open_index-1].
    [graph_add_backlink] independently checks label agreement,
    non-reflexivity, unary arity, and target bounds. *)
Definition backlink_successor
    (g : Cyclic.graph) (open_index target : nat) (goal : judgment)
    : list Cyclic.graph :=
  option_graph_to_list
    (Cyclic.graph_add_backlink g open_index target
      (exact_backlink_rule goal)).

Definition backlink_successors
    (g : Cyclic.graph) (open_index : nat) (goal : judgment)
    : list Cyclic.graph :=
  List.concat (map (fun target =>
    backlink_successor g open_index target goal)
    (List.seq 0 open_index)).

Definition rule_successors
    (g : Cyclic.graph) (open_index : nat) (goal : judgment)
    : list Cyclic.graph :=
  List.concat (map (fun rule =>
    option_graph_to_list (Cyclic.graph_apply_rule g open_index rule))
    (generate_rules goal)).

(** One ordered expansion.  The axiom branch is placed first, followed by
    backlinks and then ordinary inference rules. *)
Definition expand_graph (g : Cyclic.graph) : list Cyclic.graph :=
  match first_open g with
  | None => []
  | Some open_index =>
      match Cyclic.node_at g open_index with
      | None => []                 (* impossible for a well-built graph *)
      | Some node =>
          let goal := node.(Cyclic.node_judgment) in
          let axiom_graphs :=
            match generate_axiom goal with
            | Some ax => option_graph_to_list
                (Cyclic.graph_add_axiom g open_index ax)
            | None => []
            end in
          let simplification_graphs :=
            match simplification_candidate goal with
            | Some rule => option_graph_to_list
                (Cyclic.graph_apply_rule g open_index rule)
            | None => []
            end in
          (axiom_graphs ++
           simplification_graphs ++
           backlink_successors g open_index goal ++
           prepared_backlink_successors g open_index goal ++
           rule_successors g open_index goal)%list
      end
  end.

Fixpoint find_closed_graph (frontier : list Cyclic.graph)
    : option Cyclic.graph :=
  match frontier with
  | [] => None
  | g :: rest =>
      if graph_closedb g then Some g else find_closed_graph rest
  end.

(** [bounded_frontier_search fuel frontier] performs at most [fuel] graph
    expansion layers.  A closed graph is checked before consuming fuel, so a
    zero bound still recognizes a closed frontier item. *)
Fixpoint bounded_frontier_search
    (fuel : nat) (frontier : list Cyclic.graph) : option Cyclic.graph :=
  match find_closed_graph frontier with
  | Some g => Some g
  | None =>
      match fuel with
      | 0 => None
      | S fuel' =>
          bounded_frontier_search fuel'
            (List.concat (map expand_graph frontier))
      end
  end.

(** Priority-preserving depth-first search.  The local [try_successors]
    recursion consumes the finite successor list, while every recursive graph
    call receives the strictly smaller [fuel'].  This is the Gallina analogue
    of the inner DFS used by the original iterative-deepening prover. *)
Fixpoint bounded_depth_first_search (fuel : nat) (g : Cyclic.graph)
    : option Cyclic.graph :=
  if graph_closedb g then Some g else
  match fuel with
  | 0 => None
  | S fuel' =>
      let fix try_successors (successors : list Cyclic.graph)
          : option Cyclic.graph :=
        match successors with
        | [] => None
        | next :: rest =>
            match bounded_depth_first_search fuel' next with
            | Some closed => Some closed
            | None => try_successors rest
            end
        end in
      try_successors (expand_graph g)
  end.

Definition bounded_graph_search (fuel : nat) (root : judgment)
    : option Cyclic.graph :=
  bounded_depth_first_search fuel (Cyclic.start_graph root).

(** ** Finite trace-witness enumeration

    A closed graph is still not a proof.  The global relational trace check
    and the finite routing witness must accept it.  The all-[None], all-zero
    witness is tried first and suffices for acyclic proof trees.  Cyclic graphs
    additionally enumerate node-local tags and potentials bounded by the
    graph size.  Exhaustion is bounded non-success, never a validity claim. *)

Fixpoint choose_lists {A : Type} (choices : list (list A)) : list (list A) :=
  match choices with
  | [] => [[]]
  | xs :: rest =>
      List.concat (map (fun x =>
        map (fun suffix => x :: suffix) (choose_lists rest)) xs)
  end.

Definition nth_with_default {A : Type} (default : A) (xs : list A) (i : nat)
    : A :=
  match nth_error xs i with Some x => x | None => default end.

Definition witness_from_lists
    (tags : list (option nat)) (potentials : list nat)
    : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := nth_with_default None tags;
     Cyclic.witness_potential := nth_with_default 0 potentials |}.

Definition node_tag_choices (node : Cyclic.node) : list (option nat) :=
  None :: map (@Some nat)
    (judgment_tags node.(Cyclic.node_judgment)).

Definition graph_tag_assignments (g : Cyclic.graph)
    : list (list (option nat)) :=
  choose_lists (map node_tag_choices g.(Cyclic.graph_nodes)).

Definition graph_potential_assignments (g : Cyclic.graph)
    : list (list nat) :=
  let values := List.seq 0 (S (List.length g.(Cyclic.graph_nodes))) in
  choose_lists (map (fun _ => values) g.(Cyclic.graph_nodes)).

(** Choose the first syntactic tag at every live node.  Left unfolding places
    the retagged recursive body before the contracted copy, so this follows the
    progressing trace used by the original first-order proofs.  Dead nodes may
    safely select no tag because witness obligations ignore edges entering
    finite dead regions. *)
Definition heuristic_tag_at (g : Cyclic.graph) (i : nat) : option nat :=
  if Cyclic.liveb g i then
    match judgment_tags (Cyclic.label_at g i) with
    | tag :: _ => Some tag
    | [] => None
    end
  else None.

Definition heuristic_tags (g : Cyclic.graph) : list (option nat) :=
  map (heuristic_tag_at g) (List.seq 0 (List.length g.(Cyclic.graph_nodes))).

(** Required source potential for one live edge, assuming the target
    potentials from the preceding relaxation round.  A progressing selected
    pair needs no auxiliary descent; a non-progressing pair needs one more
    than its target. *)
Definition edge_required_potential
    (g : Cyclic.graph) (tags : list (option nat)) (old : list nat)
    (source : nat) (target_edge : nat * Cyclic.edge_info) : nat :=
  let '(target, edge) := target_edge in
  if Cyclic.liveb g target then
    match nth_with_default None tags source,
          nth_with_default None tags target with
    | None, None => S (nth_with_default 0 old target)
    | None, Some _ => 0
    | Some _, None => S (List.length g.(Cyclic.graph_nodes))
    | Some a, Some b =>
        if Cyclic.pair_mem (a, b) edge.(Cyclic.edge_progress)
        then 0
        else S (nth_with_default 0 old target)
    end
  else 0.

Definition max_list_default (values : list nat) : nat :=
  fold_right Nat.max 0 values.

Definition relaxed_node_potential
    (g : Cyclic.graph) (tags : list (option nat)) (old : list nat)
    (source : nat) : nat :=
  match Cyclic.node_at g source with
  | None => 0
  | Some node =>
      max_list_default
        (map (edge_required_potential g tags old source)
          (Cyclic.node_edges node))
  end.

Definition relax_trace_potentials
    (g : Cyclic.graph) (tags : list (option nat)) (old : list nat) : list nat :=
  map (relaxed_node_potential g tags old)
    (List.seq 0 (List.length g.(Cyclic.graph_nodes))).

Fixpoint iterate_trace_potentials
    (rounds : nat) (g : Cyclic.graph) (tags : list (option nat))
    (old : list nat) : list nat :=
  match rounds with
  | 0 => old
  | S rounds' =>
      iterate_trace_potentials rounds' g tags
        (relax_trace_potentials g tags old)
  end.

Definition heuristic_trace_witness (g : Cyclic.graph) : Cyclic.trace_witness :=
  let tags := heuristic_tags g in
  let zeros := repeat 0 (List.length g.(Cyclic.graph_nodes)) in
  let potentials := iterate_trace_potentials
    (S (List.length g.(Cyclic.graph_nodes))) g tags zeros in
  witness_from_lists tags potentials.

(** The complete finite enumeration is deliberately kept separate from the
    cheap candidates.  Constructing this list can be expensive: it is the
    Cartesian product of all tag choices and all bounded potential choices.
    Keeping it behind an explicit fallback below lets Gallina reduce the
    common successful case without first materialising that product. *)
Definition exhaustive_witness_candidates
    (g : Cyclic.graph) : list Cyclic.trace_witness :=
  List.concat (map (fun tags =>
    map (witness_from_lists tags) (graph_potential_assignments g))
    (graph_tag_assignments g)).

(** This list is useful for inspection and tests.  The heuristic comes first
    because cyclic proofs normally need selected trace tags, whereas the
    empty witness is chiefly useful for acyclic graphs. *)
Definition witness_candidates (g : Cyclic.graph) : list Cyclic.trace_witness :=
  heuristic_trace_witness g :: empty_trace_witness ::
  exhaustive_witness_candidates g.

Record checked_graph (g : Cyclic.graph) : Type := {
  checked_witness : Cyclic.trace_witness;
  checked_raw_equation : Cyclic.raw_check g checked_witness = true
}.

Definition check_witness_candidate
    (g : Cyclic.graph) (tw : Cyclic.trace_witness)
    : option (checked_graph g).
Proof.
  destruct (Cyclic.raw_check g tw) eqn:Hcheck.
  - exact (Some {| checked_witness := tw;
                   checked_raw_equation := Hcheck |}).
  - exact None.
Defined.

Fixpoint find_checked_witness
    (g : Cyclic.graph) (candidates : list Cyclic.trace_witness)
    : option (checked_graph g) :=
  match candidates with
  | [] => None
  | tw :: rest =>
      match check_witness_candidate g tw with
      | Some checked => Some checked
      | None => find_checked_witness g rest
      end
  end.

(** Try the inexpensive, deterministic witnesses before beginning exhaustive
    enumeration.  This definition spells out the short circuit rather than
    merely relying on laziness of a list expression.  Consequently, when the
    heuristic succeeds, neither the empty candidate nor the exponentially
    larger complete candidate space needs to be evaluated.

    Soundness never relies on the heuristic: every returned value contains
    the equation produced by [Cyclic.raw_check].  A poor heuristic can only
    make search slower or return [None]; it cannot manufacture a proof. *)
Definition find_graph_witness (g : Cyclic.graph) : option (checked_graph g) :=
  match check_witness_candidate g (heuristic_trace_witness g) with
  | Some checked => Some checked
  | None =>
      match check_witness_candidate g empty_trace_witness with
      | Some checked => Some checked
      | None => find_checked_witness g (exhaustive_witness_candidates g)
      end
  end.

Definition certify_searched_graph (fuel : nat) (root : judgment)
    : option { g : Cyclic.graph & checked_graph g } :=
  match bounded_graph_search fuel root with
  | None => None
  | Some g =>
      match find_graph_witness g with
      | None => None
      | Some checked => Some (existT _ g checked)
      end
  end.

(** Regression: this goal requires [L.Or] followed by two independently
    generated identity closures.  It is deliberately unrelated to the named
    benchmark table. *)
Definition graph_search_regression_goal : judgment :=
  mk_judgment []
    (mk_sequent
      [[Eq (Const 0) (Const 0)]; [Eq (Const 1) (Const 1)]]
      [[]]).

Example graph_search_builds_and_checks_a_nontrivial_tree :
  match certify_searched_graph 4
    (normalize_judgment graph_search_regression_goal) with
  | Some _ => true
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.
