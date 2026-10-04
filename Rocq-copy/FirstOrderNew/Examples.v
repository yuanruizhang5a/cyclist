From Stdlib Require Import List Bool String Arith.
From CyclistRocq.FirstOrderNew Require Import Benchmarks.
From CyclistRocq.FirstOrderNew Require Import CertifiedSearch.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** Exact example inputs, followed by generic certified engine executions.
    Parsing checks below are separate from proof-search success. *)
Definition equality_identity_goal : sequent := {|
  antecedent := [[Eq x y]]; succedent := [[Eq x y]] |}.
Definition natural_zero_goal : sequent := {|
  antecedent := [[]]; succedent := [[Pred 0 "N" [zero]]] |}.
Definition cyclic_odd_goal : sequent := Benchmarks.odd_implies_natural.

Example equality_example_has_exact_input :
  parse_sequent Benchmarks.Env.defs "x=y |- x=y" = Ok equality_identity_goal.
Proof. lazy; reflexivity. Qed.
Example natural_zero_example_has_exact_input :
  parse_sequent Benchmarks.Env.defs "true |- N(0)" = Ok natural_zero_goal.
Proof. lazy; reflexivity. Qed.
Example cyclic_odd_example_is_first_source_target :
  parse_sequent Benchmarks.Env.defs "O(x) |- N(x)" = Ok cyclic_odd_goal.
Proof. lazy; reflexivity. Qed.

(** A custom three-clause library has no N/E/O predicate names.  Its universal
    entry head and explicit constructor-equality guard differ from the source suite.
    Generic rule generation must inspect these supplied clauses. *)
Definition renamed_modified_definitions : definitions := [
  mk_clause "Tally" [zero] [];
  mk_clause "Tally" [successor x] [Pred 19 "Tally" [x]];
  mk_clause "Entry" [x] [Eq x (successor y); Pred 23 "Tally" [y]]].
Module RenamedEnv.
  Definition defs : definitions := renamed_modified_definitions.
End RenamedEnv.
Definition renamed_modified_goal : sequent := {|
  antecedent := [[Pred 0 "Entry" [x]]]; succedent := [[Pred 1 "Tally" [x]]] |}.
Definition renamed_zero_goal : sequent := {|
  antecedent := [[]]; succedent := [[Pred 0 "Tally" [zero]]] |}.

Example renamed_environment_is_well_formed : definitions_wfb RenamedEnv.defs = true.
Proof. lazy; reflexivity. Qed.
Example renamed_modified_input_has_exact_AST :
  parse_sequent RenamedEnv.defs "Entry(x) |- Tally(x)" = Ok renamed_modified_goal.
Proof. lazy; reflexivity. Qed.
Example renamed_zero_input_has_exact_AST :
  parse_sequent RenamedEnv.defs "true |- Tally(0)" = Ok renamed_zero_goal.
Proof. lazy; reflexivity. Qed.
Example renamed_predicate_family_is_supplied_by_environment :
  map clause_name RenamedEnv.defs = ["Tally"; "Tally"; "Entry"].
Proof. reflexivity. Qed.

(** The common runner is usable with both independently instantiated provers. *)
Definition source_example_cases : list benchmark_case := [
  {| benchmark_name := "equality-identity"; benchmark_input := "x=y |- x=y";
     benchmark_goal := equality_identity_goal |};
  {| benchmark_name := "natural-zero-right-unfold"; benchmark_input := "true |- N(0)";
     benchmark_goal := natural_zero_goal |};
  {| benchmark_name := "cyclic-odd-implies-natural"; benchmark_input := "O(x) |- N(x)";
     benchmark_goal := cyclic_odd_goal |}].
Definition renamed_example_cases : list benchmark_case := [
  {| benchmark_name := "renamed-modified-entry"; benchmark_input := "Entry(x) |- Tally(x)";
     benchmark_goal := renamed_modified_goal |};
  {| benchmark_name := "renamed-zero-right-unfold"; benchmark_input := "true |- Tally(0)";
     benchmark_goal := renamed_zero_goal |}].

Example source_examples_all_preserve_parsed_inputs :
  map (fun b => parse_sequent Benchmarks.Env.defs (benchmark_input b)) source_example_cases =
  map (fun b => Ok (benchmark_goal b)) source_example_cases.
Proof. lazy; reflexivity. Qed.
Example renamed_examples_all_preserve_parsed_inputs :
  map (fun b => parse_sequent RenamedEnv.defs (benchmark_input b)) renamed_example_cases =
  map (fun b => Ok (benchmark_goal b)) renamed_example_cases.
Proof. lazy; reflexivity. Qed.

Module Prover := CertifiedSearch.Make Benchmarks.Env.
Module RenamedProver := CertifiedSearch.Make RenamedEnv.

(** The SAME budgets and generic solver are used for every target.  These
    limits keep candidate generation bounded independently of graph checking. *)
Definition example_search_limits : search_limits := {|
  generation_budget := {| matching_fuel := 16; simplification_steps := 16;
    candidate_limit := 16; combination_limit := 8 |};
  search_fuel := 200; macro_fuel := 64; first_depth := 1; last_depth := 7 |}.

Definition equality_identity_search := Prover.search_graph example_search_limits equality_identity_goal.
Definition natural_zero_search := Prover.search_graph example_search_limits natural_zero_goal.
Definition cyclic_odd_search := Prover.search_graph example_search_limits cyclic_odd_goal.
Definition renamed_modified_search := RenamedProver.search_graph example_search_limits renamed_modified_goal.
Definition renamed_zero_search := RenamedProver.search_graph example_search_limits renamed_zero_goal.

(** Instrumentation preserves Unknown reasons.  For Found graphs the payload
    reports (node count, reachable-cycle flag), followed by the search depth.
    The flag uses the witness module's dynamic-programming liveness cache. *)
Definition summarize_source_search (r : Search.search_result Prover.C.graph) := match r with
  | Search.Found g depth => Search.Found
      (List.length (Prover.C.graph_nodes g), existsb (fun b => b) (Prover.W.cached_liveness g)) depth
  | Search.Unknown why => Search.Unknown why end.
Definition summarize_renamed_search (r : Search.search_result RenamedProver.C.graph) := match r with
  | Search.Found g depth => Search.Found
      (List.length (RenamedProver.C.graph_nodes g), existsb (fun b => b) (RenamedProver.W.cached_liveness g)) depth
  | Search.Unknown why => Search.Unknown why end.
Definition source_example_search_summaries := map
  (fun b => (benchmark_name b,
    summarize_source_search (Prover.search_graph example_search_limits (benchmark_goal b)))) source_example_cases.
Definition renamed_example_search_summaries := map
  (fun b => (benchmark_name b,
    summarize_renamed_search (RenamedProver.search_graph example_search_limits (benchmark_goal b)))) renamed_example_cases.

(** Freeze EVERY actual raw-search output with VM evaluation.  Each snapshot
    stores its graph and depth, paired with an equality to the generic search
    result.  In particular, projecting a transcript below never executes search
    through [source_found_result] or [renamed_found_result].  Full relational
    checking still uses [lazy], independently of raw-search snapshots. *)
Local Ltac record_found_search search :=
  let result := eval vm_compute in search in
  lazymatch result with
  | Search.Found ?g ?depth => exists (g,depth); vm_compute; reflexivity
  | Search.Unknown ?why => fail 1 "example search returned Unknown" why
  end.

Definition source_search_foundb (r : Search.search_result Prover.C.graph) := match r with
  | Search.Found _ _ => true | Search.Unknown _ => false end.
Definition renamed_search_foundb (r : Search.search_result RenamedProver.C.graph) := match r with
  | Search.Found _ _ => true | Search.Unknown _ => false end.
Definition source_found_result r (H : source_search_foundb r = true) :
  {gd : Prover.C.graph * nat | r = Search.Found (fst gd) (snd gd)}.
Proof. destruct r as [g depth|why]; [exists (g,depth); reflexivity|discriminate]. Defined.
Definition renamed_found_result r (H : renamed_search_foundb r = true) :
  {gd : RenamedProver.C.graph * nat | r = Search.Found (fst gd) (snd gd)}.
Proof. destruct r as [g depth|why]; [exists (g,depth); reflexivity|discriminate]. Defined.

Definition equality_identity_transcript : {gd : Prover.C.graph * nat |
  equality_identity_search = Search.Found (fst gd) (snd gd)}.
Proof. record_found_search equality_identity_search. Defined.
Definition natural_zero_transcript : {gd : Prover.C.graph * nat |
  natural_zero_search = Search.Found (fst gd) (snd gd)}.
Proof. record_found_search natural_zero_search. Defined.
Definition cyclic_odd_transcript : {gd : Prover.C.graph * nat |
  cyclic_odd_search = Search.Found (fst gd) (snd gd)}.
Proof. record_found_search cyclic_odd_search. Defined.
Definition renamed_modified_transcript : {gd : RenamedProver.C.graph * nat |
  renamed_modified_search = Search.Found (fst gd) (snd gd)}.
Proof. record_found_search renamed_modified_search. Defined.
Definition renamed_zero_transcript : {gd : RenamedProver.C.graph * nat |
  renamed_zero_search = Search.Found (fst gd) (snd gd)}.
Proof. record_found_search renamed_zero_search. Defined.

Example equality_identity_raw_found : source_search_foundb equality_identity_search = true.
Proof. rewrite (proj2_sig equality_identity_transcript); reflexivity. Qed.
Example natural_zero_raw_found : source_search_foundb natural_zero_search = true.
Proof. rewrite (proj2_sig natural_zero_transcript); reflexivity. Qed.
Example renamed_modified_raw_found : renamed_search_foundb renamed_modified_search = true.
Proof. rewrite (proj2_sig renamed_modified_transcript); reflexivity. Qed.
Example renamed_zero_raw_found : renamed_search_foundb renamed_zero_search = true.
Proof. rewrite (proj2_sig renamed_zero_transcript); reflexivity. Qed.

Definition equality_identity_graph := fst (proj1_sig equality_identity_transcript).
Definition natural_zero_graph := fst (proj1_sig natural_zero_transcript).
Definition cyclic_odd_graph := fst (proj1_sig cyclic_odd_transcript).
Definition renamed_modified_graph := fst (proj1_sig renamed_modified_transcript).
Definition renamed_zero_graph := fst (proj1_sig renamed_zero_transcript).

Example source_search_node_counts :
  (List.length (Prover.C.graph_nodes equality_identity_graph),
   List.length (Prover.C.graph_nodes natural_zero_graph),
   List.length (Prover.C.graph_nodes cyclic_odd_graph)) = (1,3,18).
Proof. vm_compute; reflexivity. Qed.
Example renamed_search_node_counts :
  (List.length (RenamedProver.C.graph_nodes renamed_modified_graph),
   List.length (RenamedProver.C.graph_nodes renamed_zero_graph)) = (9,3).
Proof. vm_compute; reflexivity. Qed.
Example cyclic_example_really_has_a_cycle :
  existsb (fun b => b) (Prover.W.cached_liveness cyclic_odd_graph) = true.
Proof. vm_compute; reflexivity. Qed.
Example source_search_depths :
  (snd (proj1_sig equality_identity_transcript), snd (proj1_sig natural_zero_transcript),
   snd (proj1_sig cyclic_odd_transcript)) = (1,1,3).
Proof. vm_compute; reflexivity. Qed.
Example renamed_search_depths :
  (snd (proj1_sig renamed_modified_transcript), snd (proj1_sig renamed_zero_transcript)) = (1,1).
Proof. vm_compute; reflexivity. Qed.

Definition source_finish_succeeded j g := match Prover.finish_proof j g with
  | Some _ => true | None => false end.
Definition renamed_finish_succeeded j g := match RenamedProver.finish_proof j g with
  | Some _ => true | None => false end.

(** The finish gate includes the unchanged framework's [C.raw_check], not just
    structural/routing acceptance.  Lazy evaluation avoids materializing its
    exponential default relational fuel before the checker needs it. *)
Example equality_identity_full_check :
  source_finish_succeeded equality_identity_goal equality_identity_graph = true.
Proof. lazy; reflexivity. Qed.
Example natural_zero_full_check :
  source_finish_succeeded natural_zero_goal natural_zero_graph = true.
Proof. lazy; reflexivity. Qed.
Example cyclic_odd_full_check :
  source_finish_succeeded cyclic_odd_goal cyclic_odd_graph = true.
Proof. lazy; reflexivity. Qed.
Example renamed_modified_full_check :
  renamed_finish_succeeded renamed_modified_goal renamed_modified_graph = true.
Proof. lazy; reflexivity. Qed.
Example renamed_zero_full_check :
  renamed_finish_succeeded renamed_zero_goal renamed_zero_graph = true.
Proof. lazy; reflexivity. Qed.

(** Reify ONLY the witness returned by the engine's synthesis, never a manually
    supplied assignment.  Certificate fields below share the staged graph and
    opaque check theorem, so ordinary type conversion need not rerun finish. *)
Local Ltac record_found_witness finder :=
  let result := eval vm_compute in finder in
  lazymatch result with
  | Some ?tw => exact tw
  | None => fail 1 "engine witness synthesis returned None"
  end.
Definition equality_identity_witness : Prover.C.trace_witness.
Proof. record_found_witness (Prover.W.find_witness equality_identity_graph). Defined.
Definition natural_zero_witness : Prover.C.trace_witness.
Proof. record_found_witness (Prover.W.find_witness natural_zero_graph). Defined.
Definition cyclic_odd_witness : Prover.C.trace_witness.
Proof. record_found_witness (Prover.W.find_witness cyclic_odd_graph). Defined.
Definition renamed_modified_witness : RenamedProver.C.trace_witness.
Proof. record_found_witness (RenamedProver.W.find_witness renamed_modified_graph). Defined.
Definition renamed_zero_witness : RenamedProver.C.trace_witness.
Proof. record_found_witness (RenamedProver.W.find_witness renamed_zero_graph). Defined.

Example equality_identity_witness_found :
  Prover.W.find_witness equality_identity_graph = Some equality_identity_witness.
Proof. vm_compute; reflexivity. Qed.
Example natural_zero_witness_found :
  Prover.W.find_witness natural_zero_graph = Some natural_zero_witness.
Proof. vm_compute; reflexivity. Qed.
Example cyclic_odd_witness_found :
  Prover.W.find_witness cyclic_odd_graph = Some cyclic_odd_witness.
Proof. vm_compute; reflexivity. Qed.
Example renamed_modified_witness_found :
  RenamedProver.W.find_witness renamed_modified_graph = Some renamed_modified_witness.
Proof. vm_compute; reflexivity. Qed.
Example renamed_zero_witness_found :
  RenamedProver.W.find_witness renamed_zero_graph = Some renamed_zero_witness.
Proof. vm_compute; reflexivity. Qed.

Lemma source_finish_raw_check j g tw : Prover.W.find_witness g = Some tw ->
  source_finish_succeeded j g = true -> Prover.C.raw_check g tw = true.
Proof.
  intros Htw Hfinish; unfold source_finish_succeeded, Prover.finish_proof in Hfinish.
  destruct (Bool.bool_dec (sequent_eqb (Prover.C.graph_root g) j) true); [|discriminate].
  rewrite Htw in Hfinish.
  destruct (Bool.bool_dec (Prover.C.raw_check g tw) true); [assumption|discriminate].
Qed.
Lemma renamed_finish_raw_check j g tw : RenamedProver.W.find_witness g = Some tw ->
  renamed_finish_succeeded j g = true -> RenamedProver.C.raw_check g tw = true.
Proof.
  intros Htw Hfinish; unfold renamed_finish_succeeded, RenamedProver.finish_proof in Hfinish.
  destruct (Bool.bool_dec (sequent_eqb (RenamedProver.C.graph_root g) j) true); [|discriminate].
  rewrite Htw in Hfinish.
  destruct (Bool.bool_dec (RenamedProver.C.raw_check g tw) true); [assumption|discriminate].
Qed.

Example equality_identity_root : Prover.C.graph_root equality_identity_graph = equality_identity_goal.
Proof. vm_compute; reflexivity. Qed.
Example natural_zero_root : Prover.C.graph_root natural_zero_graph = natural_zero_goal.
Proof. vm_compute; reflexivity. Qed.
Example cyclic_odd_root : Prover.C.graph_root cyclic_odd_graph = cyclic_odd_goal.
Proof. vm_compute; reflexivity. Qed.
Example renamed_modified_root : RenamedProver.C.graph_root renamed_modified_graph = renamed_modified_goal.
Proof. vm_compute; reflexivity. Qed.
Example renamed_zero_root : RenamedProver.C.graph_root renamed_zero_graph = renamed_zero_goal.
Proof. vm_compute; reflexivity. Qed.

Definition equality_identity_certificate : Prover.proved equality_identity_goal := {|
  Prover.proof_graph := equality_identity_graph; Prover.proof_witness := equality_identity_witness;
  Prover.proof_checks := source_finish_raw_check _ _ _ equality_identity_witness_found equality_identity_full_check;
  Prover.proof_root := equality_identity_root |}.
Definition natural_zero_certificate : Prover.proved natural_zero_goal := {|
  Prover.proof_graph := natural_zero_graph; Prover.proof_witness := natural_zero_witness;
  Prover.proof_checks := source_finish_raw_check _ _ _ natural_zero_witness_found natural_zero_full_check;
  Prover.proof_root := natural_zero_root |}.
Definition cyclic_odd_certificate : Prover.proved cyclic_odd_goal := {|
  Prover.proof_graph := cyclic_odd_graph; Prover.proof_witness := cyclic_odd_witness;
  Prover.proof_checks := source_finish_raw_check _ _ _ cyclic_odd_witness_found cyclic_odd_full_check;
  Prover.proof_root := cyclic_odd_root |}.
Definition renamed_modified_certificate : RenamedProver.proved renamed_modified_goal := {|
  RenamedProver.proof_graph := renamed_modified_graph; RenamedProver.proof_witness := renamed_modified_witness;
  RenamedProver.proof_checks := renamed_finish_raw_check _ _ _ renamed_modified_witness_found renamed_modified_full_check;
  RenamedProver.proof_root := renamed_modified_root |}.
Definition renamed_zero_certificate : RenamedProver.proved renamed_zero_goal := {|
  RenamedProver.proof_graph := renamed_zero_graph; RenamedProver.proof_witness := renamed_zero_witness;
  RenamedProver.proof_checks := renamed_finish_raw_check _ _ _ renamed_zero_witness_found renamed_zero_full_check;
  RenamedProver.proof_root := renamed_zero_root |}.

(** Soundness uses only the generic certified-prover theorem.  Each certificate
    above packages an actual-search graph, the synthesized witness, the proven
    full finish gate, and the preserved original root. *)
Theorem equality_identity_valid : valid Benchmarks.Env.defs equality_identity_goal.
Proof. exact (Prover.proved_sound _ equality_identity_certificate). Qed.
Theorem natural_zero_valid : valid Benchmarks.Env.defs natural_zero_goal.
Proof. exact (Prover.proved_sound _ natural_zero_certificate). Qed.
Theorem cyclic_odd_valid : valid Benchmarks.Env.defs cyclic_odd_goal.
Proof. exact (Prover.proved_sound _ cyclic_odd_certificate). Qed.
Theorem renamed_modified_valid : valid RenamedEnv.defs renamed_modified_goal.
Proof. exact (RenamedProver.proved_sound _ renamed_modified_certificate). Qed.
Theorem renamed_zero_valid : valid RenamedEnv.defs renamed_zero_goal.
Proof. exact (RenamedProver.proved_sound _ renamed_zero_certificate). Qed.
