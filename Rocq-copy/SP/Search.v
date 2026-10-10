From Stdlib Require Import List Bool Arith String.

From CyclistRocq.SP Require Import
  Syntax Semantics Rules Certification RuleGeneration GraphSearch
  Definitions Benchmarks.

Import ListNotations.
Open Scope string_scope.

(** * Public proof-producing search API *)

Record search_config : Type := {
  min_depth : nat;
  max_depth : nat
}.

Definition default_config : search_config :=
  {| min_depth := 1; max_depth := 8 |}.

Record verified_proof (goal : judgment) : Type := {
  proof_certificate : Cyclic.certificate;
  proof_root_matches :
    proof_certificate.(Cyclic.cert_graph).(Cyclic.graph_root) =
      normalize_judgment goal;
  proof_check_passes : Cyclic.check_certificate proof_certificate = true
}.

Definition verified_proof_valid goal (proof : verified_proof goal)
    : Cyclic.Valid goal.
Proof.
  destruct proof as [certificate Hroot Hcheck]. simpl in *.
  pose proof (Cyclic.certificate_sound certificate Hcheck) as Hvalid.
  unfold normalize_judgment in Hroot. now rewrite Hroot in Hvalid.
Defined.

Definition generated_graph_strategy (goal : judgment) (depth : nat)
    : option (verified_proof goal).
Proof.
  destruct (bounded_graph_search depth (normalize_judgment goal))
    as [[g tw Hraw]|]; [|exact None].
  set (certificate := certify_raw_check g tw Hraw).
  destruct (judgment_eq_dec g.(Cyclic.graph_root) (normalize_judgment goal))
    as [Hroot | Hdifferent].
  - exact (Some
      {| proof_certificate := certificate;
         proof_root_matches := Hroot;
         proof_check_passes := certify_raw_check_check g tw Hraw |}).
  - exact None.
Defined.

Definition search_at_depth (depth : nat) (goal : judgment)
    : option (verified_proof goal) :=
  generated_graph_strategy goal depth.

Fixpoint search_depths (fuel current maximum : nat) (goal : judgment)
    : option (verified_proof goal) :=
  match fuel with
  | 0 => None
  | S remaining =>
      if Nat.leb current maximum then
        match search_at_depth current goal with
        | Some proof => Some proof
        | None => search_depths remaining (S current) maximum goal
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
  unfold solvedb. destruct (search goal config) as [proof|]; intro H.
  - exact (verified_proof_valid goal proof).
  - discriminate.
Qed.

Example general_identity_search :
  solvedb {| min_depth := 1; max_depth := 1 |}
    (mk_judgment [] (mk_sequent (singleton_formula emp)
      (singleton_formula emp))) = true.
Proof. vm_compute. reflexivity. Qed.

Example general_clause_introduction_search :
  solvedb {| min_depth := 1; max_depth := 1 |}
    benchmark_base_19_1 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem benchmark_base_19_search_valid : Cyclic.Valid benchmark_base_19_1.
Proof.
  apply (search_sound {| min_depth := 1; max_depth := 1 |}).
  vm_compute. reflexivity.
Qed.

Example unsupported_open_goal_is_bounded_non_success :
  solvedb {| min_depth := 0; max_depth := 0 |}
    benchmark_base_01_1 = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions search_sound.
Print Assumptions benchmark_base_19_search_valid.
