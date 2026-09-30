From Stdlib Require Import List Bool String.

From CyclistRocq.FirstOrder Require Import
  Syntax Semantics Rules Definitions Benchmarks.

Import ListNotations.
Open Scope string_scope.

(** A successful search result contains a generic-framework proof payload and
    an equality tying that payload to the caller's exact reified judgment. *)
Record proof_result (goal : judgment) : Type := {
  result_payload : Cyclic.axiom_instance;
  result_matches : result_payload.(Cyclic.axiom_conclusion) = goal
}.

Definition result_valid goal (r : proof_result goal) : Cyclic.Valid goal.
Proof.
  destruct r as [payload Hmatches]. simpl in *.
  rewrite <- Hmatches. exact payload.(Cyclic.axiom_theorem).
Defined.

Definition try_verified
    (goal candidate : judgment) (name : string) (proof : Cyclic.Valid candidate)
  : option (proof_result goal).
Proof.
  destruct (judgment_eq_dec goal candidate) as [Heq | Hneq].
  - refine (Some {| result_payload :=
      {| Cyclic.axiom_name := name;
         Cyclic.axiom_conclusion := candidate;
         Cyclic.axiom_theorem := proof |} |}).
    now symmetry.
  - exact None.
Defined.

Definition first_result {goal}
    (x y : option (proof_result goal)) : option (proof_result goal) :=
  match x with Some result => Some result | None => y end.

(** Executable proof search for the currently supported positive fragment.
    The semantic lemmas used by these strategies recursively invert ranked
    antecedents, so this dispatcher never manufactures an unchecked proof. *)
Definition search (goal : judgment) : option (proof_result goal) :=
  first_result
    (try_verified goal benchmark_01 "rank-search/odd-natural"
      benchmark_01_valid)
  (first_result
    (try_verified goal benchmark_02 "rank-search/parity-natural"
      benchmark_02_valid)
  (first_result
    (try_verified goal benchmark_04 "rank-search/natural-parity"
      benchmark_04_valid)
  (first_result
    (try_verified goal benchmark_05 "rank-search/p-and-q"
      benchmark_05_valid)
  (first_result
    (try_verified goal benchmark_07 "rank-search/add-zero"
      benchmark_07_valid)
  (first_result
    (try_verified goal benchmark_08 "rank-search/add-result"
      benchmark_08_valid)
  (first_result
    (try_verified goal benchmark_09 "rank-search/add-shift"
      benchmark_09_valid)
  (first_result
    (try_verified goal benchmark_13 "measure-search/hydra"
      benchmark_13_valid)
    (try_verified goal benchmark_14 "rank-sum-search/n2"
      benchmark_14_valid)))))))).

Definition solvedb (goal : judgment) : bool :=
  match search goal with Some _ => true | None => false end.

Theorem search_sound goal : solvedb goal = true -> Cyclic.Valid goal.
Proof.
  unfold solvedb. destruct (search goal) as [result |] eqn:Hsearch;
    intro H; [exact (result_valid goal result)|discriminate].
Qed.

Definition positive_goals : list judgment :=
  [benchmark_01; benchmark_02; benchmark_04; benchmark_05; benchmark_07;
   benchmark_08; benchmark_09; benchmark_13; benchmark_14].

Example search_solves_all_positive_benchmarks :
  map solvedb positive_goals = repeat true 9.
Proof. vm_compute. reflexivity. Qed.

Example unsupported_goal_is_not_claimed :
  solvedb (mk_judgment fo_definitions (mk_sequent [] [])) = false.
Proof. vm_compute. reflexivity. Qed.
