From Stdlib Require Import List Bool Arith.
From CyclistRocq.FirstOrderNew Require Export Search.
Import ListNotations.
Open Scope list_scope.
Open Scope nat_scope.

(** A work item retains unexecuted PROGRAM DATA, not a list of applied graphs.
    Greedy families commit after the first executable qualifying program;
    choices retain the original immutable state for backtracking. *)
Inductive lazy_work (State : Type) :=
| GoalWork (state : State) (pending : list pending_goal)
| AxiomsWork (state : State) (current : pending_goal) (remaining : list pending_goal)
    (axioms simplifications choices : list rule_program)
| SimplificationsWork (state : State) (current : pending_goal) (remaining : list pending_goal)
    (simplifications choices : list rule_program)
| ChoicesWork (state : State) (current : pending_goal) (remaining : list pending_goal)
    (programs : list rule_program).
Arguments GoalWork {State} _ _.
Arguments AxiomsWork {State} _ _ _ _ _ _.
Arguments SimplificationsWork {State} _ _ _ _ _.
Arguments ChoicesWork {State} _ _ _ _.

Inductive lazy_family := AxiomFamily | SimplificationFamily | ChoiceFamily.
Record lazy_attempt (State : Type) := {
  attempt_family : lazy_family;
  attempt_index : nat;
  attempt_program : rule_program;
  attempt_result : option (list nat * State)
}.
Arguments attempt_family {State} _.
Arguments attempt_index {State} _.
Arguments attempt_program {State} _.
Arguments attempt_result {State} _.
Inductive lazy_transition (State : Type) :=
| LazyFinish (result : search_result State)
| LazyContinue (work : list (lazy_work State))
| LazyExecuted (attempt : lazy_attempt State) (work : list (lazy_work State)).
Arguments LazyFinish {State} _.
Arguments LazyContinue {State} _.
Arguments LazyExecuted {State} _ _.

(** Each transition executes at most ONE macro. The normal runner discards
    diagnostics immediately; the optional traced runner is solely for observing
    demand and debugging. It is not used by lazy_bounded_dfs/lazy_iddfs. *)
Definition lazy_step {d State} (api : search_api d State) macrofuel depth
    (stack : list (lazy_work State)) : lazy_transition State := match stack with
  | [] => LazyFinish (Unknown NoCandidate)
  | GoalWork state [] :: rest =>
    if final_accept api state then LazyFinish (Found state depth) else LazyContinue rest
  | GoalWork state (current::remaining) :: rest =>
    match node_label api state current.(pending_index) with
    | None => LazyContinue rest
    | Some j => let menu := generate_rules api state current.(pending_index) j in
      LazyContinue (AxiomsWork state current remaining menu.(menu_axioms)
        menu.(menu_simplifications) menu.(menu_choices) :: rest)
    end
  | AxiomsWork state current remaining [] simplifications choices :: rest =>
    match current.(pending_depth) with
    | 0 => LazyContinue rest
    | S _ => LazyContinue (SimplificationsWork state current remaining simplifications choices :: rest)
    end
  | AxiomsWork state current remaining (program::programs) simplifications choices :: rest =>
    let execution := execute_program api macrofuel state current.(pending_index) program in
    let next := match execution with
      | Some ([],state') => GoalWork state' remaining :: rest
      | _ => AxiomsWork state current remaining programs simplifications choices :: rest end in
    LazyExecuted {| attempt_family := AxiomFamily; attempt_index := current.(pending_index);
                    attempt_program := program; attempt_result := execution |} next
  | SimplificationsWork state current remaining programs choices :: rest =>
    match current.(pending_depth) with
    | 0 => LazyContinue rest
    | S child_depth => match programs with
      | [] => LazyContinue (ChoicesWork state current remaining choices :: rest)
      | program::programs' =>
        let execution := execute_program api macrofuel state current.(pending_index) program in
        let next := match execution with
          | Some (indices,state') => GoalWork state'
              (child_goals child_depth indices ++ remaining) :: rest
          | None => SimplificationsWork state current remaining programs' choices :: rest end in
        LazyExecuted {| attempt_family := SimplificationFamily; attempt_index := current.(pending_index);
                        attempt_program := program; attempt_result := execution |} next
      end
    end
  | ChoicesWork state current remaining programs :: rest =>
    match current.(pending_depth) with
    | 0 => LazyContinue rest
    | S child_depth => match programs with
      | [] => LazyContinue rest
      | program::programs' =>
        let execution := execute_program api macrofuel state current.(pending_index) program in
        let continuation := ChoicesWork state current remaining programs' :: rest in
        let next := match execution with
          | Some (indices,state') => GoalWork state'
              (child_goals child_depth indices ++ remaining) :: continuation
          | None => continuation end in
        LazyExecuted {| attempt_family := ChoiceFamily; attempt_index := current.(pending_index);
                        attempt_program := program; attempt_result := execution |} next
      end
    end
  end.

(** One fuel unit per work-stack transition, including administrative/failure
    transitions and final acceptance probes. Macrofuel independently bounds the
    existing checked execute_program interpreter. No costed macro is compiled or
    applied at depth zero; axioms remain eligible there. *)
Fixpoint lazy_dfs_stack {d State} (api : search_api d State) fuel macrofuel depth stack
    : search_result State := match fuel with
  | 0 => Unknown FuelExhausted
  | S fuel' => match lazy_step api macrofuel depth stack with
    | LazyFinish result => result
    | LazyContinue next | LazyExecuted _ next => lazy_dfs_stack api fuel' macrofuel depth next
    end end.
Definition lazy_initial_work {State} (initial : State) root depth :=
  [GoalWork initial [{| pending_index := root; pending_depth := depth |}]].
Definition lazy_bounded_dfs {d State} (api : search_api d State)
    fuel macrofuel depth initial root :=
  lazy_dfs_stack api fuel macrofuel depth (lazy_initial_work initial root depth).
Fixpoint lazy_iterative_deepening {d State} (api : search_api d State)
    iterations fuel_per_depth macrofuel firstdepth lastdepth initial root := match iterations with
  | 0 => Unknown IterationsExhausted
  | S iterations' => if lastdepth <? firstdepth then Unknown DepthExhausted else
    match lazy_bounded_dfs api fuel_per_depth macrofuel firstdepth initial root with
    | Found state depth => Found state depth
    | Unknown _ => lazy_iterative_deepening api iterations' fuel_per_depth macrofuel
        (S firstdepth) lastdepth initial root end
  end.
Definition lazy_iddfs {d State} (api : search_api d State)
    fuel_per_depth macrofuel firstdepth lastdepth initial root :=
  lazy_iterative_deepening api (S (lastdepth-firstdepth)) fuel_per_depth macrofuel
    firstdepth lastdepth initial root.

Lemma lazy_step_accepted d State (api : search_api d State) macrofuel depth stack state found_depth :
  lazy_step api macrofuel depth stack = LazyFinish (Found state found_depth) ->
  final_accept api state = true.
Proof.
  destruct stack as [|work rest]; [discriminate|].
  destruct work as [s pending|s current remaining axes simps choices|
    s current remaining simps choices|s current remaining choices].
  - destruct pending as [|current remaining]; cbn [lazy_step].
    + destruct (final_accept api s) eqn:E; [intro H; inversion H; subst; exact E|discriminate].
    + destruct (node_label api s (pending_index current)); discriminate.
  - destruct axes as [|p ps]; cbn [lazy_step];
      [destruct (pending_depth current); discriminate|discriminate].
  - cbn [lazy_step]; destruct (pending_depth current); [discriminate|].
    destruct simps; discriminate.
  - cbn [lazy_step]; destruct (pending_depth current); [discriminate|].
    destruct choices; discriminate.
Qed.
Theorem lazy_dfs_stack_accepted d State (api : search_api d State)
    fuel macrofuel depth stack state found_depth :
  lazy_dfs_stack api fuel macrofuel depth stack = Found state found_depth ->
  final_accept api state = true.
Proof.
  revert stack; induction fuel as [|fuel IH]; intros stack H; [discriminate|].
  cbn [lazy_dfs_stack] in H.
  destruct (lazy_step api macrofuel depth stack) as [result|next|attempt next] eqn:E.
  - subst result; eapply lazy_step_accepted; exact E.
  - eapply IH; exact H.
  - eapply IH; exact H.
Qed.
Theorem lazy_bounded_dfs_accepted d State (api : search_api d State)
    fuel macrofuel depth initial root state found_depth :
  lazy_bounded_dfs api fuel macrofuel depth initial root = Found state found_depth ->
  final_accept api state = true.
Proof. apply lazy_dfs_stack_accepted. Qed.
Theorem lazy_iterative_deepening_accepted d State (api : search_api d State)
    iterations fuel macrofuel firstdepth lastdepth initial root state found_depth :
  lazy_iterative_deepening api iterations fuel macrofuel firstdepth lastdepth initial root =
    Found state found_depth -> final_accept api state = true.
Proof.
  revert firstdepth; induction iterations as [|n IH]; intros firstdepth H; [discriminate|].
  change ((if lastdepth <? firstdepth then Unknown DepthExhausted else
    match lazy_bounded_dfs api fuel macrofuel firstdepth initial root with
    | Found s depth => Found s depth
    | Unknown _ => lazy_iterative_deepening api n fuel macrofuel (S firstdepth)
        lastdepth initial root end) = Found state found_depth) in H.
  destruct (lastdepth <? firstdepth); [discriminate|].
  destruct (lazy_bounded_dfs api fuel macrofuel firstdepth initial root) as [s depth|reason] eqn:E.
  - inversion H; subst; eapply lazy_bounded_dfs_accepted; exact E.
  - eapply IH; exact H.
Qed.
Theorem lazy_iddfs_accepted d State (api : search_api d State)
    fuel macrofuel firstdepth lastdepth initial root state found_depth :
  lazy_iddfs api fuel macrofuel firstdepth lastdepth initial root = Found state found_depth ->
  final_accept api state = true.
Proof. apply lazy_iterative_deepening_accepted. Qed.
Theorem lazy_accepted_search_contract d State (api : search_api d State) (P : State -> Prop)
    (accept_sound : forall s, final_accept api s = true -> P s)
    fuel macrofuel firstdepth lastdepth initial root state found_depth :
  lazy_iddfs api fuel macrofuel firstdepth lastdepth initial root = Found state found_depth -> P state.
Proof. intro H; apply accept_sound; eapply lazy_iddfs_accepted; exact H. Qed.

(** Optional bounded observation of exactly the SAME transitions. The production
    entry points above do not retain attempted graphs or execution history. *)
Fixpoint lazy_dfs_stack_traced {d State} (api : search_api d State) fuel macrofuel depth stack
    : search_result State * list (lazy_attempt State) := match fuel with
  | 0 => (Unknown FuelExhausted,[])
  | S fuel' => match lazy_step api macrofuel depth stack with
    | LazyFinish result => (result,[])
    | LazyContinue next => lazy_dfs_stack_traced api fuel' macrofuel depth next
    | LazyExecuted attempt next =>
      let '(result,attempts) := lazy_dfs_stack_traced api fuel' macrofuel depth next in
      (result,attempt::attempts)
    end end.
Definition lazy_bounded_dfs_traced {d State} (api : search_api d State)
    fuel macrofuel depth initial root :=
  lazy_dfs_stack_traced api fuel macrofuel depth (lazy_initial_work initial root depth).
Lemma lazy_trace_preserves_result d State (api : search_api d State) fuel macrofuel depth stack :
  fst (lazy_dfs_stack_traced api fuel macrofuel depth stack) = lazy_dfs_stack api fuel macrofuel depth stack.
Proof.
  revert stack; induction fuel as [|fuel IH]; intro stack; [reflexivity|].
  cbn [lazy_dfs_stack_traced lazy_dfs_stack].
  destruct (lazy_step api macrofuel depth stack); [reflexivity|apply IH|].
  destruct (lazy_dfs_stack_traced api fuel macrofuel depth work) as [result attempts] eqn:E.
  specialize (IH work); rewrite E in IH; exact IH.
Qed.
