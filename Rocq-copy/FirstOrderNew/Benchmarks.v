From Stdlib Require Import List Bool String Arith.
From CyclistRocq.FirstOrderNew Require Export Input SourceDefinitions.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** Data-only acceptance targets: importing this file neither invokes search
    nor asserts that a proof was found.  Each AST is the complete parser output
    from the original active benchmark, including variable order and tags.
    The environment is exactly the supplied closed source library. *)
Module Env.
  Definition defs : definitions := closed_source_definitions.
End Env.

Record benchmark_case := {
  benchmark_name : string;
  benchmark_input : string;
  benchmark_goal : sequent
}.

Definition odd_implies_natural := {|
  antecedent := [[Pred 0 "O" [x]]]; succedent := [[Pred 1 "N" [x]]] |}.
Definition even_or_odd_implies_natural := {|
  antecedent := [[Pred 0 "E" [x]]; [Pred 1 "O" [x]]];
  succedent := [[Pred 2 "N" [x]]] |}.
Definition natural_implies_odd_or_even := {|
  antecedent := [[Pred 0 "N" [x]]];
  succedent := [[Pred 1 "O" [x]]; [Pred 2 "E" [x]]] |}.
Definition naturals_imply_q := {|
  antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]]];
  succedent := [[Pred 2 "Q" [x; y]]] |}.
Definition addition_zero_right := {|
  antecedent := [[Pred 0 "N" [x]]]; succedent := [[Pred 1 "ADD" [x; zero; x]]] |}.
Definition addition_preserves_natural := {|
  antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]; Pred 2 "ADD" [x; y; z]]];
  succedent := [[Pred 3 "N" [z]]] |}.
Definition addition_successor_right := {|
  antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]; Pred 2 "ADD" [x; y; z]]];
  succedent := [[Pred 3 "ADD" [x; successor y; successor z]]] |}.
(** Source spelling encounters [y] before [x] in these final two inputs, hence
    source y is Free 0 ([SourceDefinitions.x]) and source x is Free 1. *)
Definition naturals_imply_hydra := {|
  antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]]];
  succedent := [[Pred 2 "H" [y; x]]] |}.
Definition naturals_imply_n2 := {|
  antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]]];
  succedent := [[Pred 2 "N2" [y; x]]] |}.

Definition active_benchmarks : list benchmark_case := [
  {| benchmark_name := "01-odd-even.tst";
     benchmark_input := "O(x) |- N(x)"; benchmark_goal := odd_implies_natural |};
  {| benchmark_name := "02-even-or-odd.tst";
     benchmark_input := "E(x) \/ O(x) |- N(x)";
     benchmark_goal := even_or_odd_implies_natural |};
  {| benchmark_name := "04-n-is-even-or-odd.tst";
     benchmark_input := "N(x) |- O(x) \/ E(x)";
     benchmark_goal := natural_implies_odd_or_even |};
  {| benchmark_name := "05-p-and-q.tst";
     benchmark_input := "N(x) & N(y) |- Q(x,y)"; benchmark_goal := naturals_imply_q |};
  {| benchmark_name := "07-a-plus-zero.tst";
     benchmark_input := "N(x) |- ADD(x,0,x)"; benchmark_goal := addition_zero_right |};
  {| benchmark_name := "08-sum-is-nat.tst";
     benchmark_input := "N(x) & N(y) & ADD(x,y,z) |- N(z)";
     benchmark_goal := addition_preserves_natural |};
  {| benchmark_name := "09-a-plus-b-plus-one.tst";
     benchmark_input := "N(x) & N(y) & ADD(x,y,z) |- ADD(x,s(y),s(z))";
     benchmark_goal := addition_successor_right |};
  {| benchmark_name := "13-2-hydra.tst";
     benchmark_input := "N(y) & N(x) |- H(x, y)"; benchmark_goal := naturals_imply_hydra |};
  {| benchmark_name := "14-two-n-is-n2.tst";
     benchmark_input := "N(y) & N(x) |- N2(x,y)"; benchmark_goal := naturals_imply_n2 |}].

Definition active_benchmark_names := map benchmark_name active_benchmarks.
Definition active_benchmark_inputs := map benchmark_input active_benchmarks.
Definition active_benchmark_goals := map benchmark_goal active_benchmarks.
Definition named_benchmark_goals := map (fun b => (benchmark_name b, benchmark_goal b)) active_benchmarks.
Definition benchmark_transcripts := map
  (fun b => (benchmark_name b, parse_sequent Env.defs (benchmark_input b))) active_benchmarks.
(** All nine are positive acceptance targets, not a report of measured success. *)
Definition benchmark_acceptance_targets := active_benchmark_names.
Definition benchmark_input_validb b := match parse_sequent Env.defs (benchmark_input b) with
  | Ok j => sequent_eqb j (benchmark_goal b) && sequent_wfb Env.defs j
  | Error _ => false end.
Definition benchmark_inputs_validb := forallb benchmark_input_validb active_benchmarks.

Example active_suite_contains_all_nine_targets : List.length active_benchmarks = 9.
Proof. reflexivity. Qed.
Example active_suite_preserves_complete_parsed_AST :
  map (parse_sequent Env.defs) active_benchmark_inputs = map (@Ok sequent) active_benchmark_goals.
Proof. lazy; reflexivity. Qed.
Example active_suite_inputs_are_validated : benchmark_inputs_validb = true.
Proof. lazy; reflexivity. Qed.
Example benchmark_environment_is_original_closed_source : Env.defs = closed_source_definitions.
Proof. reflexivity. Qed.

Lemma benchmark_input_validb_sound b : benchmark_input_validb b = true ->
  parse_sequent Env.defs (benchmark_input b) = Ok (benchmark_goal b) /\
  sequent_wfb Env.defs (benchmark_goal b) = true.
Proof.
  unfold benchmark_input_validb.
  destruct (parse_sequent Env.defs (benchmark_input b)) as [j|e] eqn:E; [|discriminate].
  rewrite andb_true_iff; intros [Hj Hwf]; apply sequent_eqb_spec in Hj; subst j; auto.
Qed.
Theorem every_active_benchmark_has_validated_transcript b : In b active_benchmarks ->
  parse_sequent Env.defs (benchmark_input b) = Ok (benchmark_goal b) /\
  sequent_wfb Env.defs (benchmark_goal b) = true.
Proof.
  intro Hin; apply benchmark_input_validb_sound.
  pose proof active_suite_inputs_are_validated as H.
  unfold benchmark_inputs_validb in H; apply forallb_forall with (x:=b) in H; auto.
Qed.

(** Uniform, unevaluated execution harness.  Once the certified engine is
    available, instantiate [Certificate] with [Prover.proved] and [prove_goal]
    with [Prover.prove limits].  No benchmark name is inspected, and no default
    goal replaces a parser failure.  Defining this harness performs no runs. *)
Record benchmark_run (Certificate : sequent -> Type) := {
  benchmark_run_case : benchmark_case;
  benchmark_run_result : option (Certificate (benchmark_goal benchmark_run_case))
}.
Arguments benchmark_run_case {Certificate} _.
Arguments benchmark_run_result {Certificate} _.
Definition run_benchmark {Certificate : sequent -> Type}
  (prove_goal : forall j, option (Certificate j)) b : benchmark_run Certificate := {|
  benchmark_run_case := b; benchmark_run_result := prove_goal (benchmark_goal b) |}.
Definition run_cases {Certificate : sequent -> Type}
  (prove_goal : forall j, option (Certificate j)) cases := map (run_benchmark prove_goal) cases.
Definition run_benchmark_suite {Certificate : sequent -> Type}
  (prove_goal : forall j, option (Certificate j)) := run_cases prove_goal active_benchmarks.
Definition benchmark_run_summary {Certificate} (run : benchmark_run Certificate) :=
  (benchmark_name (benchmark_run_case run),
    match benchmark_run_result run with Some _ => true | None => false end).
Definition summarize_benchmark_runs {Certificate} (runs : list (benchmark_run Certificate)) :=
  map benchmark_run_summary runs.
