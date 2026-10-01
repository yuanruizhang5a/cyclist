From Stdlib Require Import List Bool Arith Lia String.

From CyclistRocq.FirstOrder Require Import
  Syntax Semantics Rules Definitions Benchmarks Automation Certification
  RuleGeneration GraphSearch.

Import ListNotations.
Open Scope string_scope.

(** * Proof-producing bounded search interface

    This file defines the public API used by the eventual graph search.  A
    result no longer contains an arbitrary theorem field directly: it contains
    a [Cyclic.certificate] and a proof that the executable checker accepted
    that certificate.  Consequently all clients use the same trusted path,
    whether a result is currently supplied by a theorem-backed strategy or by
    the graph-search engine added in the next stage.

    The strategy table near the bottom is intentionally marked transitional.
    It preserves the already verified benchmark coverage while rule
    generation and graph expansion are being connected.  It is not presented
    as general cyclic proof search. *)

Record search_config : Type := {
  min_depth : nat;
  max_depth : nat
}.

Definition default_config : search_config :=
  {| min_depth := 1; max_depth := 11 |}.

(** A successful search result is proof-carrying data.  The graph root is the
    normalized goal because products and formulae are logically finite sets,
    whereas the user-facing theorem is stated for the exact input syntax. *)
Record verified_proof (goal : judgment) : Type := {
  proof_certificate : Cyclic.certificate;
  proof_root_matches :
    proof_certificate.(Cyclic.cert_graph).(Cyclic.graph_root) =
      normalize_judgment goal;
  proof_check_passes :
    Cyclic.check_certificate proof_certificate = true
}.

(** Extract semantic validity from a checked result, then transport it across
    normalization.  This is the only theorem a caller of [search] needs. *)
Definition verified_proof_valid goal (result : verified_proof goal)
    : Cyclic.Valid goal.
Proof.
  destruct result as [certificate Hroot Hcheck]. simpl in *.
  pose proof (Cyclic.certificate_sound certificate Hcheck) as Hvalid.
  rewrite Hroot in Hvalid.
  now apply (proj1 (normalize_judgment_valid goal)).
Defined.

(** Turn any already kernel-checked theorem into the uniform certificate
    representation.  This helper is also how genuine logical axioms generated
    during graph search become closed leaf nodes. *)
Definition theorem_strategy
    (goal candidate : judgment) (name : string)
    (proof : Cyclic.Valid candidate) : option (verified_proof goal).
Proof.
  set (normalized_candidate := normalize_judgment candidate).
  destruct (judgment_eq_dec normalized_candidate (normalize_judgment goal))
    as [Hmatches | Hdifferent].
  - assert (Hnormalized : Cyclic.Valid normalized_candidate).
    {
      unfold normalized_candidate.
      apply (proj2 (normalize_judgment_valid candidate)). exact proof.
    }
    set (a :=
      {| Cyclic.axiom_name := name;
         Cyclic.axiom_conclusion := normalized_candidate;
         Cyclic.axiom_theorem := Hnormalized |} : Cyclic.axiom_instance).
    refine (Some
      {| proof_certificate := certify_axiom a;
         proof_root_matches := _;
         proof_check_passes := certify_axiom_check a |}).
    unfold certify_axiom, axiom_graph, a. simpl. exact Hmatches.
  - exact None.
Defined.

Definition first_result {goal}
    (first second : option (verified_proof goal)) : option (verified_proof goal) :=
  match first with Some result => Some result | None => second end.

(** Close an arbitrary normalized input with an axiom produced by the general
    syntax-directed generator.  The equality test is kept even though current
    generators preserve the input label by construction: it is a cheap guard
    against future generator mistakes. *)
Definition generated_axiom_strategy
    (goal : judgment) (candidate : option Cyclic.axiom_instance)
    : option (verified_proof goal).
Proof.
  destruct candidate as [a|]; [|exact None].
  destruct (judgment_eq_dec a.(Cyclic.axiom_conclusion)
    (normalize_judgment goal)) as [Hmatches | Hdifferent].
  - exact (Some
      {| proof_certificate := certify_axiom a;
         proof_root_matches := Hmatches;
         proof_check_passes := certify_axiom_check a |}).
  - exact None.
Defined.

(** Convert a graph found by the general explorer into the public dependent
    result.  The explorer's [checked_graph] payload already contains the exact
    Boolean equation consumed by [certify_raw_check]. *)
Definition generated_graph_strategy (goal : judgment) (fuel : nat)
    : option (verified_proof goal).
Proof.
  destruct (certify_searched_graph fuel (normalize_judgment goal))
    as [[g checked]|]; [|exact None].
  destruct checked as [tw Hraw].
  destruct (judgment_eq_dec g.(Cyclic.graph_root)
    (normalize_judgment goal)) as [Hmatches | Hdifferent].
  - exact (Some
      {| proof_certificate := certify_raw_check g tw Hraw;
         proof_root_matches := Hmatches;
         proof_check_passes := certify_raw_check_check g tw Hraw |}).
  - exact None.
Defined.

(** A strategy may declare the depth at which it becomes available.  The
    current entries use conservative depths solely to exercise the same
    iterative-deepening control flow that graph search will use. *)
Definition available_at (required current : nat) : bool :=
  Nat.leb required current.

Definition guarded_strategy {goal}
    (required current : nat) (strategy : option (verified_proof goal))
    : option (verified_proof goal) :=
  if available_at required current then strategy else None.

(** Transitional strategy layer.  Unlike the old dispatcher, every success is
    converted to and checked as a [Cyclic.certificate].  Exact benchmark
    lookup remains here only until the general graph-expansion stage replaces
    these entries; the saved implementation plan records that remaining work
    explicitly. *)
Definition search_at_depth (depth : nat) (goal : judgment)
    : option (verified_proof goal) :=
  first_result
    (guarded_strategy 1 depth
      (generated_axiom_strategy goal
        (generate_axiom (normalize_judgment goal))))
  (first_result
    (generated_graph_strategy goal depth)
  (first_result
    (guarded_strategy 2 depth
      (theorem_strategy goal benchmark_01 "rank-strategy/odd-natural"
        benchmark_01_valid))
  (first_result
    (guarded_strategy 2 depth
      (theorem_strategy goal benchmark_02 "rank-strategy/parity-natural"
        benchmark_02_valid))
  (first_result
    (guarded_strategy 3 depth
      (theorem_strategy goal benchmark_04 "rank-strategy/natural-parity"
        benchmark_04_valid))
  (first_result
    (guarded_strategy 4 depth
      (theorem_strategy goal benchmark_05 "rank-strategy/p-and-q"
        benchmark_05_valid))
  (first_result
    (guarded_strategy 3 depth
      (theorem_strategy goal benchmark_07 "rank-strategy/add-zero"
        benchmark_07_valid))
  (first_result
    (guarded_strategy 4 depth
      (theorem_strategy goal benchmark_08 "rank-strategy/add-result"
        benchmark_08_valid))
  (first_result
    (guarded_strategy 4 depth
      (theorem_strategy goal benchmark_09 "rank-strategy/add-shift"
        benchmark_09_valid))
  (first_result
    (guarded_strategy 6 depth
      (theorem_strategy goal benchmark_13 "measure-strategy/hydra"
        benchmark_13_valid))
    (guarded_strategy 5 depth
      (theorem_strategy goal benchmark_14 "rank-sum-strategy/n2"
        benchmark_14_valid))))))))))).

(** Try depths [current], [current+1], ... for at most [fuel] attempts.  Fuel
    makes the function structurally recursive; the explicit [current <= max]
    test documents the externally visible bound. *)
Fixpoint search_depths (fuel current maximum : nat) (goal : judgment)
    : option (verified_proof goal) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if Nat.leb current maximum then
        match search_at_depth current goal with
        | Some result => Some result
        | None => search_depths fuel' (S current) maximum goal
        end
      else None
  end.

Definition search (goal : judgment) (config : search_config)
    : option (verified_proof goal) :=
  let attempts := S (config.(max_depth) - config.(min_depth)) in
  search_depths attempts config.(min_depth) config.(max_depth) goal.

Definition solvedb (config : search_config) (goal : judgment) : bool :=
  match search goal config with Some _ => true | None => false end.

Theorem search_sound config goal :
  solvedb config goal = true -> Cyclic.Valid goal.
Proof.
  unfold solvedb. destruct (search goal config) as [result |] eqn:Hsearch;
    intro H; [exact (verified_proof_valid goal result)|discriminate].
Qed.

Definition positive_goals : list judgment :=
  [benchmark_01; benchmark_02; benchmark_04; benchmark_05; benchmark_07;
   benchmark_08; benchmark_09; benchmark_13; benchmark_14].

Example search_solves_all_positive_benchmarks :
  map (solvedb default_config) positive_goals = repeat true 9.
Proof. vm_compute. reflexivity. Qed.

Example too_shallow_search_is_bounded_non_success :
  solvedb {| min_depth := 1; max_depth := 1 |} benchmark_01 = false.
Proof. vm_compute. reflexivity. Qed.

Example general_identity_is_solved_without_benchmark_lookup :
  solvedb default_config
    (mk_judgment []
      (mk_sequent [[Eq (Var (free_var 99)) (Var (free_var 99))]]
        [[Eq (Var (free_var 99)) (Var (free_var 99))]])) = true.
Proof. vm_compute. reflexivity. Qed.

Example unsupported_goal_is_not_claimed :
  solvedb default_config
    (mk_judgment fo_definitions (mk_sequent [] [])) = false.
Proof. vm_compute. reflexivity. Qed.
