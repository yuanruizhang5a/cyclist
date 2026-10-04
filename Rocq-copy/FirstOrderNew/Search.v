From Stdlib Require Import List Bool Arith String Lia.
From CyclistRocq.FirstOrderNew Require Export RuleGeneration.
Import ListNotations.
Open Scope list_scope.
Open Scope nat_scope.

(** No graph representation or global trace checker is assumed. The caller
    supplies immutable graph operations. The compiler is the ONLY way to turn
    a raw descriptor into a native inference; unknown descriptors return None.
    apply_application must insert the certified application's actual premises
    in order, returning their indices. close_exact performs only an EXACT
    backlink; the preparatory Weaken/Subst applications are interpreted here. *)
Record search_api (d : definitions) (State : Type) := {
  node_label : State -> nat -> option sequent;
  node_indices : State -> list nat;
  generate_rules : State -> nat -> sequent -> rule_menu;
  compile_descriptor : forall j, rule_descriptor -> option (certified_application d j);
  apply_application : forall j, State -> nat -> certified_application d j ->
    option (list nat * State);
  close_exact : State -> nat -> nat -> trace_edge -> option State;
  partial_trace_check : State -> bool;
  final_accept : State -> bool
}.
Arguments node_label {d State} _ _ _.
Arguments node_indices {d State} _ _.
Arguments generate_rules {d State} _ _ _ _.
Arguments compile_descriptor {d State} _ _ _.
Arguments apply_application {d State} _ _ _ _ _.
Arguments close_exact {d State} _ _ _ _ _.
Arguments partial_trace_check {d State} _ _.
Arguments final_accept {d State} _ _.

Definition graph_labels {d State} (api : search_api d State) s := flat_map
  (fun i => match node_label api s i with Some j => [(i,j)] | None => [] end)
  (node_indices api s).
Definition generated_source_menu {d State} (api : search_api d State) limits s i j :=
  source_rule_menu limits d i j (graph_labels api s).
Definition with_source_generation {d State} limits (api : search_api d State)
    : search_api d State :=
  {| node_label := node_label api; node_indices := node_indices api;
     generate_rules := generated_source_menu api limits;
     compile_descriptor := compile_descriptor api;
     apply_application := apply_application api; close_exact := close_exact api;
     partial_trace_check := partial_trace_check api; final_accept := final_accept api |}.
Definition application_matches p (a : application) :=
  sequent_eqb p.(proposal_conclusion) a.(conclusion) &&
  eqb_of_dec (list_eq_dec sequent_eq_dec) p.(proposal_premises)
    (map premise_label a.(premises)).
Lemma application_matches_spec p a : application_matches p a = true ->
  p.(proposal_conclusion) = a.(conclusion) /\
  p.(proposal_premises) = map premise_label a.(premises).
Proof.
  unfold application_matches; rewrite andb_true_iff.
  intros [Hj Hps]; apply sequent_eqb_spec in Hj;
    apply eqb_of_dec_spec in Hps; auto.
Qed.

Definition checked_apply {d State} (api : search_api d State) s i p :=
  match node_label api s i with
  | Some j => if sequent_eqb j p.(proposal_conclusion) then
    match compile_descriptor api j p.(proposal_descriptor) with
    | Some ca => if application_matches p (certified_rule d j ca) then
      match apply_application api j s i ca with
      | Some (indices,s') =>
        if Nat.eqb (List.length indices) (List.length p.(proposal_premises)) &&
           partial_trace_check api s' then Some (indices,s') else None
      | None => None end
      else None
    | None => None end
    else None
  | None => None end.

Fixpoint prepare_backlink {d State} (api : search_api d State)
    (steps : list rule_proposal) s i : option (nat * State) := match steps with
  | [] => Some (i,s)
  | p::steps' => match checked_apply api s i p with
    | Some ([child],s') => prepare_backlink api steps' s' child
    | _ => None end end.
Definition exact_backlink_edgeb j edge :=
  Nat.eqb (List.length edge.(progressing)) 0 &&
  forallb (fun ab => Nat.eqb (fst ab) (snd ab) &&
    existsb (Nat.eqb (fst ab)) (trace_tags j)) edge.(continuations).
Definition checked_backlink {d State} (api : search_api d State) s i b
    : option (list nat * State) :=
  if Nat.eqb i b.(backlink_target_index) then None else
  match node_label api s i,node_label api s b.(backlink_target_index) with
  | Some source,Some target =>
    if sequent_eqb source b.(backlink_source) &&
       sequent_eqb target b.(backlink_target) then
      match prepare_backlink api b.(backlink_preparation) s i with
      | Some (leaf,s') =>
        if Nat.eqb leaf b.(backlink_target_index) then None else
        match node_label api s' leaf,node_label api s' b.(backlink_target_index) with
        | Some j,Some k => if sequent_eqb j k &&
                               exact_backlink_edgeb k b.(backlink_exact_edge) then
            match close_exact api s' leaf b.(backlink_target_index)
                                  b.(backlink_exact_edge) with
            | Some s'' => if partial_trace_check api s'' then Some ([],s'') else None
            | None => None end
            else None
        | _,_ => None end
      | None => None end
    else None
  | _,_ => None end.

(** Program fuel bounds macro execution independently of DFS depth. It bounds
    nesting, not the number of siblings: both are finite reified lists. *)
Fixpoint execute_program {d State} (api : search_api d State) fuel s i p
    : option (list nat * State) := match fuel with
  | 0 => None
  | S fuel' => match p with
    | ProgramOpen j => match node_label api s i with
      | Some k => if sequent_eqb j k then Some ([i],s) else None
      | None => None end
    | ProgramBacklink b => checked_backlink api s i b
    | ProgramApply proposal children => match checked_apply api s i proposal with
      | Some (indices,s') =>
        (fix visit (ps : list rule_program) (ns : list nat) (state : State)
            : option (list nat * State) := match ps,ns with
          | [],[] => Some ([],state)
          | p'::ps',n::ns' => match execute_program api fuel' state n p' with
            | Some (front,state') => match visit ps' ns' state' with
              | Some (rest,state'') => Some (front ++ rest,state'')
              | None => None end
            | None => None end
          | _,_ => None end) children indices s'
      | None => None end
    end end.

Inductive unknown_reason := FuelExhausted | DepthExhausted | NoCandidate
  | AcceptanceRejected | IterationsExhausted.
Inductive search_result (State : Type) :=
| Found (state : State) (depth : nat)
| Unknown (reason : unknown_reason).
Arguments Found {State} _ _.
Arguments Unknown {State} _.

Record pending_goal := { pending_index : nat; pending_depth : nat }.
Record search_branch (State : Type) := {
  branch_state : State;
  branch_pending : list pending_goal
}.
Arguments branch_state {State} _.
Arguments branch_pending {State} _.
Definition child_goals depth indices := map
  (fun i => {| pending_index := i; pending_depth := depth |}) indices.

(** Axioms close at depth zero. Rule programs, including macro-compositions,
    cost one search-depth unit, matching the source distinction between graph
    depth and search depth. Failed graph/trace/certification checks are simply
    refused candidates. The first nonempty executable greedy family commits. *)
Definition executable_programs {d State} (api : search_api d State)
    program_fuel s i ps := flat_map
  (fun p => option_list (execute_program api program_fuel s i p)) ps.
Definition node_successors {d State} (api : search_api d State)
    program_fuel s i j :=
  let menu := generate_rules api s i j in
  let axes := filter (fun step => Nat.eqb (List.length (fst step)) 0)
    (executable_programs api program_fuel s i menu.(menu_axioms)) in
  match axes with
  | a::_ => [(false,a)]
  | [] => match executable_programs api program_fuel s i menu.(menu_simplifications) with
    | a::_ => [(true,a)]
    | [] => map (fun a => (true,a))
        (executable_programs api program_fuel s i menu.(menu_choices))
    end end.

(** Explicit DFS stack makes totality immediate and allows backtracking after
    FINAL acceptance rejection. Thus a raw closed graph rejected by the global
    checker does not hide later certified candidates. Every stack pop consumes
    fuel, including rejected complete graphs. Exhaustion never means falsity. *)
Fixpoint dfs_stack {d State} (api : search_api d State)
    fuel program_fuel depth_limit (stack : list (search_branch State))
    : search_result State := match fuel with
  | 0 => Unknown FuelExhausted
  | S fuel' => match stack with
    | [] => Unknown NoCandidate
    | branch::rest => match branch.(branch_pending) with
      | [] => if final_accept api branch.(branch_state)
          then Found branch.(branch_state) depth_limit
          else dfs_stack api fuel' program_fuel depth_limit rest
      | goal::goals => match node_label api branch.(branch_state) goal.(pending_index) with
        | None => dfs_stack api fuel' program_fuel depth_limit rest
        | Some j =>
          let steps := node_successors api program_fuel branch.(branch_state)
                         goal.(pending_index) j in
          let admissible := filter (fun step =>
            negb (fst step) || (0 <? goal.(pending_depth))) steps in
          let branches := map (fun (step : bool * (list nat * State)) =>
            let '(cost,(indices,state')) := step in
            {| branch_state := state';
               branch_pending := child_goals
                 (if cost then Nat.pred goal.(pending_depth) else goal.(pending_depth))
                 indices ++ goals |}) admissible in
          dfs_stack api fuel' program_fuel depth_limit (branches ++ rest)
        end end
    end end.
Definition bounded_dfs {d State} (api : search_api d State)
    fuel program_fuel depth initial root :=
  dfs_stack api fuel program_fuel depth
    [{| branch_state := initial;
        branch_pending := [{| pending_index := root; pending_depth := depth |}] |}].

Fixpoint iterative_deepening {d State} (api : search_api d State)
    iterations fuel_per_depth program_fuel start_depth maximum_depth initial root :=
  match iterations with
  | 0 => Unknown IterationsExhausted
  | S iterations' => if maximum_depth <? start_depth then Unknown DepthExhausted else
    match bounded_dfs api fuel_per_depth program_fuel start_depth initial root with
    | Found state depth => Found state depth
    | Unknown _ => iterative_deepening api iterations' fuel_per_depth program_fuel
        (S start_depth) maximum_depth initial root end
  end.
Definition iddfs {d State} (api : search_api d State)
    fuel_per_depth program_fuel start_depth maximum_depth initial root :=
  iterative_deepening api (S (maximum_depth - start_depth)) fuel_per_depth
    program_fuel start_depth maximum_depth initial root.
Definition source_iddfs {d State} limits (api : search_api d State)
    fuel_per_depth program_fuel start_depth maximum_depth initial root :=
  iddfs (with_source_generation limits api) fuel_per_depth program_fuel
    start_depth maximum_depth initial root.

(** Independent candidate/acceptance boundary. candidate_dfs uses exactly the
    same algorithm but exposes completed agendas by replacing only final_accept.
    Neither raw output nor local certification entails global cyclic validity. *)
Definition raw_api {d State} (api : search_api d State) : search_api d State :=
  {| node_label := node_label api; node_indices := node_indices api;
     generate_rules := generate_rules api; compile_descriptor := compile_descriptor api;
     apply_application := apply_application api; close_exact := close_exact api;
     partial_trace_check := partial_trace_check api; final_accept := fun _ => true |}.
Definition candidate_dfs {d State} (api : search_api d State)
    fuel program_fuel depth initial root :=
  bounded_dfs (raw_api api) fuel program_fuel depth initial root.
Definition candidate_iddfs {d State} (api : search_api d State)
    fuel_per_depth program_fuel start_depth maximum_depth initial root :=
  iddfs (raw_api api) fuel_per_depth program_fuel start_depth maximum_depth initial root.
Definition accept_candidate {d State} (api : search_api d State) r := match r with
  | Found state depth => if final_accept api state then Found state depth
                        else Unknown AcceptanceRejected
  | Unknown reason => Unknown reason end.

Theorem dfs_stack_accepted d State (api : search_api d State)
    fuel program_fuel depth stack state found_depth :
  dfs_stack api fuel program_fuel depth stack = Found state found_depth ->
  final_accept api state = true.
Proof.
  revert stack; induction fuel as [|fuel IH]; intros stack H; [discriminate|].
  destruct stack as [|[s goals] rest]; cbn in H; [discriminate|].
  destruct goals as [|g goals].
  - destruct (final_accept api s) eqn:E.
    + inversion H; subst; exact E.
    + eapply IH; exact H.
  - destruct (node_label api s (pending_index g)); eapply IH; exact H.
Qed.
Theorem bounded_dfs_accepted d State (api : search_api d State)
    fuel program_fuel depth initial root state found_depth :
  bounded_dfs api fuel program_fuel depth initial root = Found state found_depth ->
  final_accept api state = true.
Proof. apply dfs_stack_accepted. Qed.
Theorem iterative_deepening_accepted d State (api : search_api d State)
    iterations fuel program_fuel start maximum initial root state found_depth :
  iterative_deepening api iterations fuel program_fuel start maximum initial root =
    Found state found_depth -> final_accept api state = true.
Proof.
  revert start; induction iterations as [|n IH]; intros start H; [discriminate|].
  change ((if maximum <? start then Unknown DepthExhausted else
    match bounded_dfs api fuel program_fuel start initial root with
    | Found s depth => Found s depth
    | Unknown _ => iterative_deepening api n fuel program_fuel (S start)
        maximum initial root end) = Found state found_depth) in H.
  destruct (maximum <? start); [discriminate|].
  destruct (bounded_dfs api fuel program_fuel start initial root) as [s depth|why] eqn:E.
  - inversion H; subst; eapply bounded_dfs_accepted; exact E.
  - eapply IH; exact H.
Qed.
Theorem accepted_search_contract d State (api : search_api d State)
    (P : State -> Prop) (accept_sound : forall s, final_accept api s = true -> P s)
    fuel program_fuel start maximum initial root state found_depth :
  iddfs api fuel program_fuel start maximum initial root = Found state found_depth -> P state.
Proof. intro H; apply accept_sound; eapply iterative_deepening_accepted; exact H. Qed.
Corollary accepted_search_validity d State (api : search_api d State) j
    (accept_sound : forall s, final_accept api s = true -> valid d j)
    fuel program_fuel start maximum initial root state found_depth :
  iddfs api fuel program_fuel start maximum initial root = Found state found_depth -> valid d j.
Proof. apply (accepted_search_contract d State api (fun _ => valid d j) accept_sound). Qed.
Lemma accept_candidate_contract d State (api : search_api d State) r s depth :
  accept_candidate api r = Found s depth -> final_accept api s = true.
Proof.
  destruct r as [state n|why]; cbn; [|discriminate].
  destruct (final_accept api state) eqn:E; [|discriminate].
  intro H; inversion H; subst; exact E.
Qed.
