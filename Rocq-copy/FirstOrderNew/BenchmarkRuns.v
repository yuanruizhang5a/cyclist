From Stdlib Require Import List Bool Arith String Lia.
From CyclistRocq.FirstOrderNew Require Import CertifiedSearch Benchmarks.
From CyclistRocq.Cyclic Require Import Relations.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Printing Depth 8.

(** Current lazy_iddfs/fast_source_menu executions of all original targets.
    Found statistics are raw results; the explicitly constructed certificates
    below additionally prove the FULL frozen raw_check and original root.
    Historical measurements are labelled separately in BenchmarkReport.md.

    Every runner accepts an arbitrary goal/limits. Goal names occur only in
    data/reporting, never in compiler or search dispatch. Timing observations
    are external wall-clock measurements, not computations inside Rocq. *)
Module Prover := CertifiedSearch.Make Benchmarks.Env.

Definition initial_benchmark_limits : search_limits := {|
  generation_budget := {| candidate_limit := 16; combination_limit := 8;
    simplification_steps := 16; matching_fuel := 32 |};
  search_fuel := 2000; macro_fuel := 64; first_depth := 1; last_depth := 11 |}.

(** Deliberately small regression profile. Lazy fuel now counts work-stack
    transitions, not the old eager DFS pop count. *)
Definition quick_benchmark_limits : search_limits := {|
  generation_budget := {| candidate_limit := 4; combination_limit := 2;
    simplification_steps := 16; matching_fuel := 32 |};
  search_fuel := 20; macro_fuel := 64; first_depth := 3; last_depth := 3 |}.

(** Generic single-depth profiles, used unchanged across the original goals. *)
Definition focused_benchmark_limits fuel depth : search_limits := {|
  generation_budget := initial_benchmark_limits.(generation_budget);
  search_fuel := fuel; macro_fuel := 64; first_depth := depth; last_depth := depth |}.

Inductive raw_run_summary :=
| RawFound (depth nodes backlinks maximum_node_trace_count : nat)
| RawUnknown (reason : Search.unknown_reason).

Definition backlink_node n := match n.(Prover.C.node_payload) with
  | Prover.C.BacklinkNode _ _ => true | _ => false end.
Definition summarize_raw (r : Search.search_result Prover.C.graph) := match r with
  | Search.Found g depth =>
      RawFound depth (List.length g.(Prover.C.graph_nodes))
        (List.length (filter backlink_node g.(Prover.C.graph_nodes)))
        (fold_right Nat.max 0 (map (fun n => List.length
          (trace_tags n.(Prover.C.node_judgment))) g.(Prover.C.graph_nodes)))
  | Search.Unknown reason => RawUnknown reason end.

(** The checker exponent uses the UNION of IDs, not the maximum count of
    predicates at a node. This helper counts that union without constructing
    relation_fuel, graph_path_fuel, or invoking C.relational_check. *)
Definition raw_graph_tag_width (r : Search.search_result Prover.C.graph) := match r with
  | Search.Found g _ => Some (List.length (Prover.C.all_graph_tags g))
  | Search.Unknown _ => None end.
Definition run_raw limits j := summarize_raw (Prover.search_graph limits j).
Definition run_raw_with_width limits j :=
  let r := Prover.search_graph limits j in (summarize_raw r, raw_graph_tag_width r).
Definition run_raw_suite limits := map
  (fun b => (benchmark_name b, run_raw limits (benchmark_goal b))) active_benchmarks.
Definition run_full_suite limits :=
  run_benchmark_suite (Prover.prove limits).

Lemma every_profile_preserves_all_acceptance_targets limits :
  map fst (run_raw_suite limits) = benchmark_acceptance_targets.
Proof. reflexivity. Qed.

(** Current compact results. No C.raw_check/default relational fuel uses VM. *)
Example focused_01_raw_found :
  run_raw_with_width (focused_benchmark_limits 2000 3) odd_implies_natural =
  (RawFound 3 18 1 3, Some 3).
Proof. Time vm_compute; reflexivity. Qed.
Example focused_04_raw_found :
  run_raw_with_width (focused_benchmark_limits 2000 3) natural_implies_odd_or_even =
  (RawFound 3 15 1 2, Some 2).
Proof. Time vm_compute; reflexivity. Qed.
Example focused_07_raw_found :
  run_raw_with_width (focused_benchmark_limits 2000 3) addition_zero_right =
  (RawFound 3 14 1 2, Some 2).
Proof. Time vm_compute; reflexivity. Qed.

Example focused_02_raw_found :
  run_raw_with_width (focused_benchmark_limits 2000 4) even_or_odd_implies_natural =
  (RawFound 4 37 2 3, Some 3).
Proof. Time vm_compute; reflexivity. Qed.
Example focused_09_raw_found :
  run_raw_with_width (focused_benchmark_limits 2000 3) addition_successor_right =
  (RawFound 3 43 1 5, Some 5).
Proof. Time vm_compute; reflexivity. Qed.
Example focused_14_raw_found :
  run_raw_with_width (focused_benchmark_limits 2000 3) naturals_imply_n2 =
  (RawFound 3 25 1 4, Some 4).
Proof. Time vm_compute; reflexivity. Qed.

Example quick_01_raw_found :
  run_raw quick_benchmark_limits odd_implies_natural = RawFound 3 18 1 3.
Proof. Time vm_compute; reflexivity. Qed.
Example quick_02_raw_unknown :
  run_raw quick_benchmark_limits even_or_odd_implies_natural = RawUnknown Search.IterationsExhausted.
Proof. Time vm_compute; reflexivity. Qed.
Example quick_04_raw_found :
  run_raw quick_benchmark_limits natural_implies_odd_or_even = RawFound 3 15 1 2.
Proof. Time vm_compute; reflexivity. Qed.
Example quick_05_raw_unknown :
  run_raw quick_benchmark_limits naturals_imply_q = RawUnknown Search.IterationsExhausted.
Proof. Time vm_compute; reflexivity. Qed.
Example quick_07_raw_found :
  run_raw quick_benchmark_limits addition_zero_right = RawFound 3 14 1 2.
Proof. Time vm_compute; reflexivity. Qed.
Example quick_08_raw_unknown :
  run_raw quick_benchmark_limits addition_preserves_natural = RawUnknown Search.IterationsExhausted.
Proof. Time vm_compute; reflexivity. Qed.
Example quick_09_raw_unknown :
  run_raw quick_benchmark_limits addition_successor_right = RawUnknown Search.IterationsExhausted.
Proof. Time vm_compute; reflexivity. Qed.
Example quick_13_raw_unknown :
  run_raw quick_benchmark_limits naturals_imply_hydra = RawUnknown Search.IterationsExhausted.
Proof. Time vm_compute; reflexivity. Qed.
Example quick_14_raw_found :
  run_raw quick_benchmark_limits naturals_imply_n2 = RawFound 3 25 1 4.
Proof. Time vm_compute; reflexivity. Qed.

Definition expected_quick_summary := [
  ("01-odd-even.tst", RawFound 3 18 1 3);
  ("02-even-or-odd.tst", RawUnknown Search.IterationsExhausted);
  ("04-n-is-even-or-odd.tst", RawFound 3 15 1 2);
  ("05-p-and-q.tst", RawUnknown Search.IterationsExhausted);
  ("07-a-plus-zero.tst", RawFound 3 14 1 2);
  ("08-sum-is-nat.tst", RawUnknown Search.IterationsExhausted);
  ("09-a-plus-b-plus-one.tst", RawUnknown Search.IterationsExhausted);
  ("13-2-hydra.tst", RawUnknown Search.IterationsExhausted);
  ("14-two-n-is-n2.tst", RawFound 3 25 1 4)].
Example quick_suite_keeps_all_nine_outcomes :
  run_raw_suite quick_benchmark_limits = expected_quick_summary.
Proof.
  unfold run_raw_suite, expected_quick_summary.
  cbn [active_benchmarks benchmark_name benchmark_goal List.map].
  rewrite quick_01_raw_found, quick_02_raw_unknown, quick_04_raw_found,
    quick_05_raw_unknown, quick_07_raw_found, quick_08_raw_unknown,
    quick_09_raw_unknown, quick_13_raw_unknown, quick_14_raw_found.
  reflexivity.
Qed.

(** An actual Unknown result short-circuits prove BEFORE full checking. These
    are verified failures to find/package a proof under this budget, not
    counterexamples to semantic validity. *)
Lemma raw_unknown_has_no_packaged_proof limits j reason :
  run_raw limits j = RawUnknown reason -> Prover.prove limits j = None.
Proof.
  unfold run_raw, summarize_raw, Prover.prove.
  destruct (Prover.search_graph limits j) as [g depth|why];
    intro H; [discriminate|reflexivity].
Qed.
Lemma raw_suite_unknown_has_no_packaged_proof limits cases reason :
  map (fun b => (benchmark_name b, run_raw limits (benchmark_goal b))) cases =
  map (fun b => (benchmark_name b, RawUnknown reason)) cases ->
  forall b, In b cases -> Prover.prove limits (benchmark_goal b) = None.
Proof.
  induction cases as [|a cases IH]; cbn; [intros _ b H; contradiction|].
  intro H.
  assert (Ha : run_raw limits (benchmark_goal a) = RawUnknown reason).
  { exact (f_equal (fun xs => match xs with
      | [] => RawUnknown reason | (_,r) :: _ => r end) H). }
  assert (Htail :
    map (fun b => (benchmark_name b, run_raw limits (benchmark_goal b))) cases =
    map (fun b => (benchmark_name b, RawUnknown reason)) cases).
  { exact (f_equal (@List.tl (string * raw_run_summary)) H). }
  intros b [<-|Hb].
  - apply raw_unknown_has_no_packaged_proof with (reason := reason).
    exact Ha.
  - exact (IH Htail b Hb).
Qed.

(** This conditional theorem is the generic API contract. It is deliberately
    NOT an assertion that any timed-out full run returned a certificate. *)
Theorem full_benchmark_result_sound limits b p :
  Prover.prove limits (benchmark_goal b) = Some p -> valid Benchmarks.Env.defs (benchmark_goal b).
Proof. apply Prover.prove_sound. Qed.

(** External measurements from independent /tmp probes. A process timeout is
    NOT [RawUnknown], and no graph/node count is invented for an unfinished run.
    None wall_ms on 02 means its original timeout wrapper produced no timing. *)
Inductive observed_outcome := Returned (summary : raw_run_summary)
  | ProcessTimeout (nominal_deadline_seconds : nat).
Record timing_observation := {
  observation_name : string;
  observation_outcome : observed_outcome;
  observation_wall_ms : option nat
}.
Definition historical_eager_observations : list timing_observation := [
  {| observation_name := "01-odd-even.tst";
     observation_outcome := Returned (RawFound 3 18 1 3); observation_wall_ms := Some 17490 |};
  {| observation_name := "02-even-or-odd.tst";
     observation_outcome := ProcessTimeout 60; observation_wall_ms := None |};
  {| observation_name := "04-n-is-even-or-odd.tst";
     observation_outcome := Returned (RawFound 3 17 1 2); observation_wall_ms := Some 46520 |};
  {| observation_name := "05-p-and-q.tst";
     observation_outcome := ProcessTimeout 60; observation_wall_ms := Some 65900 |};
  {| observation_name := "07-a-plus-zero.tst";
     observation_outcome := Returned (RawFound 2 14 1 2); observation_wall_ms := Some 9680 |};
  {| observation_name := "08-sum-is-nat.tst";
     observation_outcome := ProcessTimeout 60; observation_wall_ms := Some 65900 |};
  {| observation_name := "09-a-plus-b-plus-one.tst";
     observation_outcome := ProcessTimeout 60; observation_wall_ms := Some 65820 |};
  {| observation_name := "13-2-hydra.tst";
     observation_outcome := ProcessTimeout 60; observation_wall_ms := Some 65820 |};
  {| observation_name := "14-two-n-is-n2.tst";
     observation_outcome := ProcessTimeout 60; observation_wall_ms := Some 65820 |}].
Definition historical_quick_wall_ms := [800; 2790; 3170; 6430; 810; 28000; 15470; 1750; 8710].
Example historical_report_keeps_all_nine_targets :
  map observation_name historical_eager_observations = benchmark_acceptance_targets.
Proof. reflexivity. Qed.
Example quick_timing_rows_cover_the_active_suite :
  List.length historical_quick_wall_ms = List.length active_benchmarks.
Proof. reflexivity. Qed.

Print Assumptions raw_unknown_has_no_packaged_proof.

(** Fuel-stability transport for the UNCHANGED frozen relational checker.
    A checked small closure is used only after checking that it stabilized.
    Structural induction then identifies it with every larger fuel, including
    the framework's default. This avoids converting enormous unary bounds in
    certificate proofs, without weakening or replacing C.raw_check. *)
Lemma path_closure_stable fuel ps :
  path_set_eqb ps (path_close_once ps) = true -> path_closure fuel ps = ps.
Proof. destruct fuel; simpl; intro H; [reflexivity|now rewrite H]. Qed.
Lemma path_closure_extend small large ps : small <= large ->
  path_set_eqb (path_closure small ps) (path_close_once (path_closure small ps)) = true ->
  path_closure large ps = path_closure small ps.
Proof.
  revert large ps; induction small as [|small IH]; intros large ps Hle Hstable.
  - now apply path_closure_stable.
  - destruct large as [|large]; [lia|].
    cbn [path_closure] in Hstable |- *.
    destruct (path_set_eqb ps (path_close_once ps)) eqn:E; [reflexivity|].
    apply IH; [lia|exact Hstable].
Qed.
Lemma relation_closure_stable fuel r :
  relation_eqb r (relation_close_once r) = true -> relation_closure fuel r = r.
Proof. destruct fuel; simpl; intro H; [reflexivity|now rewrite H]. Qed.
Lemma relation_closure_extend small large r : small <= large ->
  relation_eqb (relation_closure small r) (relation_close_once (relation_closure small r)) = true ->
  relation_closure large r = relation_closure small r.
Proof.
  revert large r; induction small as [|small IH]; intros large r Hle Hstable.
  - now apply relation_closure_stable.
  - destruct large as [|large]; [lia|].
    cbn [relation_closure] in Hstable |- *.
    destruct (relation_eqb r (relation_close_once r)) eqn:E; [reflexivity|].
    apply IH; [lia|exact Hstable].
Qed.
Lemma pow_three_positive n : 0 < Nat.pow 3 n.
Proof. induction n; cbn [Nat.pow]; lia. Qed.
Lemma pow_three_ge n : n <= Nat.pow 3 n.
Proof.
  induction n as [|n IH]; cbn [Nat.pow]; [lia|].
  pose proof (pow_three_positive n); lia.
Qed.
Lemma tag_fuel_lower g :
  S (List.length (Prover.C.all_graph_tags g)) <= Prover.C.relation_fuel g.
Proof.
  unfold Prover.C.relation_fuel; apply le_n_S.
  eapply Nat.le_trans; [|apply pow_three_ge].
  destruct (List.length (Prover.C.all_graph_tags g)); nia.
Qed.
Lemma path_fuel_lower g :
  S (List.length g.(Prover.C.graph_nodes) * List.length g.(Prover.C.graph_nodes)) <=
  Prover.C.graph_path_fuel g.
Proof.
  unfold Prover.C.graph_path_fuel; apply le_n_S.
  rewrite <- (Nat.mul_1_r (List.length g.(Prover.C.graph_nodes) * List.length g.(Prover.C.graph_nodes))) at 1.
  apply Nat.mul_le_mono_l; unfold Prover.C.relation_fuel; lia.
Qed.
Definition saturation_check steps g :=
  let paths := path_closure steps (Prover.C.base_relations_from 0 g.(Prover.C.graph_nodes)) in
  let small_tag := S (List.length (Prover.C.all_graph_tags g)) in
  path_set_eqb paths (path_close_once paths) &&
  forallb (fun p => if Nat.eqb p.(path_source) p.(path_target) then
    let closed := relation_closure small_tag p.(path_arcs) in
    relation_eqb closed (relation_close_once closed) && has_decreasing_diagonal closed
    else true) paths.
Lemma saturation_check_full steps g :
  steps <= S (List.length g.(Prover.C.graph_nodes) * List.length g.(Prover.C.graph_nodes)) ->
  saturation_check steps g = true -> Prover.C.relational_check g = true.
Proof.
  intros Hsteps Hcheck; unfold saturation_check in Hcheck.
  apply andb_true_iff in Hcheck; destruct Hcheck as [Hstable Hloops].
  unfold Prover.C.relational_check, relational_trace_check.
  rewrite (path_closure_extend steps (Prover.C.graph_path_fuel g) _
    (Nat.le_trans _ _ _ Hsteps (path_fuel_lower g)) Hstable).
  apply forallb_forall; intros p Hp.
  apply forallb_forall with (x:=p) in Hloops; [|exact Hp].
  unfold loop_relation_ok.
  destruct (Nat.eqb (path_source p) (path_target p)); [|reflexivity].
  apply andb_true_iff in Hloops; destruct Hloops as [Hstable_loop Hdiagonal].
  rewrite (relation_closure_extend _ _ _ (tag_fuel_lower g) Hstable_loop).
  exact Hdiagonal.
Qed.
Lemma raw_check_from_saturation steps g tw :
  steps <= S (List.length g.(Prover.C.graph_nodes) * List.length g.(Prover.C.graph_nodes)) ->
  saturation_check steps g = true -> Prover.C.structural_check g = true ->
  Prover.W.find_witness g = Some tw -> Prover.C.raw_check g tw = true.
Proof.
  intros Hbound Hsat Hstruct Hwit; unfold Prover.C.raw_check.
  rewrite Hstruct, (saturation_check_full steps g Hbound Hsat),
    (Prover.W.find_witness_sound g tw Hwit); reflexivity.
Qed.
Definition finish_succeeded j g := match Prover.finish_proof j g with
  | Some _ => true | None => false end.
Lemma finish_checked j g tw : Prover.C.graph_root g = j ->
  Prover.W.find_witness g = Some tw -> Prover.C.raw_check g tw = true ->
  finish_succeeded j g = true.
Proof.
  intros Hr Hw Hcheck; unfold finish_succeeded, Prover.finish_proof.
  destruct (Bool.bool_dec (sequent_eqb (Prover.C.graph_root g) j) true) as [H|H].
  - rewrite Hw; destruct (Bool.bool_dec (Prover.C.raw_check g tw) true); [reflexivity|contradiction].
  - exfalso; apply H, sequent_eqb_spec; exact Hr.
Qed.
Lemma staged_prove_exists limits j g depth :
  Prover.search_graph limits j = Search.Found g depth -> finish_succeeded j g = true ->
  exists p, Prover.prove limits j = Some p.
Proof.
  intros Hs Hf; unfold Prover.prove; rewrite Hs.
  unfold finish_succeeded in Hf; destruct (Prover.finish_proof j g) as [p|] eqn:E;
    [exists p; reflexivity|discriminate].
Qed.

Definition result_foundb (r : Search.search_result Prover.C.graph) :=
  match r with Search.Found _ _ => true | _ => false end.
Definition found_result r (H : result_foundb r = true) :
  {gd : Prover.C.graph * nat | r = Search.Found (fst gd) (snd gd)}.
Proof. destruct r as [g d|why]; [exists (g,d); reflexivity|discriminate]. Defined.

(** VM freezes an ACTUAL raw result. An explicit equation plus Found guard
    retains its provenance; there is no default graph/goal on Unknown. *)
Local Ltac record_found_search search :=
  let result := eval vm_compute in search in
  lazymatch result with
  | Search.Found ?g ?depth => exists (g,depth); vm_compute; reflexivity
  | Search.Unknown ?why => fail 1 "search returned Unknown" why end.
Definition transcript_01 : {gd : Prover.C.graph * nat |
  Prover.search_graph (focused_benchmark_limits 2000 3) odd_implies_natural =
  Search.Found (fst gd) (snd gd)}.
Proof. record_found_search
  (Prover.search_graph (focused_benchmark_limits 2000 3) odd_implies_natural). Defined.
Definition graph_01 := fst (proj1_sig transcript_01).

Definition transcript_04 : {gd : Prover.C.graph * nat |
  Prover.search_graph (focused_benchmark_limits 2000 3) natural_implies_odd_or_even =
  Search.Found (fst gd) (snd gd)}.
Proof. record_found_search
  (Prover.search_graph (focused_benchmark_limits 2000 3) natural_implies_odd_or_even). Defined.
Definition graph_04 := fst (proj1_sig transcript_04).

Definition transcript_07 : {gd : Prover.C.graph * nat |
  Prover.search_graph (focused_benchmark_limits 2000 3) addition_zero_right =
  Search.Found (fst gd) (snd gd)}.
Proof. record_found_search
  (Prover.search_graph (focused_benchmark_limits 2000 3) addition_zero_right). Defined.
Definition graph_07 := fst (proj1_sig transcript_07).

Local Ltac record_witness finder :=
  let result := eval vm_compute in finder in
  lazymatch result with Some ?tw => exact tw | None => fail 1 "no engine witness" end.
Definition witness_01 : Prover.C.trace_witness.
Proof. record_witness (Prover.W.find_witness graph_01). Defined.
Definition witness_04 : Prover.C.trace_witness.
Proof. record_witness (Prover.W.find_witness graph_04). Defined.
Definition witness_07 : Prover.C.trace_witness.
Proof. record_witness (Prover.W.find_witness graph_07). Defined.
Example witnessed_01 : Prover.W.find_witness graph_01 = Some witness_01.
Proof. vm_compute; reflexivity. Qed.
Example witnessed_04 : Prover.W.find_witness graph_04 = Some witness_04.
Proof. vm_compute; reflexivity. Qed.
Example witnessed_07 : Prover.W.find_witness graph_07 = Some witness_07.
Proof. vm_compute; reflexivity. Qed.
Example structural_01 : Prover.C.structural_check graph_01 = true.
Proof. vm_compute; reflexivity. Qed.
Example structural_04 : Prover.C.structural_check graph_04 = true.
Proof. vm_compute; reflexivity. Qed.
Example structural_07 : Prover.C.structural_check graph_07 = true.
Proof. vm_compute; reflexivity. Qed.
Example saturated_01 : saturation_check 12 graph_01 = true.
Proof. Time lazy; reflexivity. Qed.
Example saturated_04 : saturation_check 12 graph_04 = true.
Proof. Time lazy; reflexivity. Qed.
Example saturated_07 : saturation_check 12 graph_07 = true.
Proof. Time lazy; reflexivity. Qed.
Example full_checked_01 : Prover.C.raw_check graph_01 witness_01 = true.
Proof. apply raw_check_from_saturation with (steps:=12);
  [vm_compute; lia|exact saturated_01|exact structural_01|exact witnessed_01]. Qed.
Example full_checked_04 : Prover.C.raw_check graph_04 witness_04 = true.
Proof. apply raw_check_from_saturation with (steps:=12);
  [vm_compute; lia|exact saturated_04|exact structural_04|exact witnessed_04]. Qed.
Example full_checked_07 : Prover.C.raw_check graph_07 witness_07 = true.
Proof. apply raw_check_from_saturation with (steps:=12);
  [vm_compute; lia|exact saturated_07|exact structural_07|exact witnessed_07]. Qed.
Example root_01 : Prover.C.graph_root graph_01 = odd_implies_natural.
Proof. reflexivity. Qed.
Example root_04 : Prover.C.graph_root graph_04 = natural_implies_odd_or_even.
Proof. reflexivity. Qed.
Example root_07 : Prover.C.graph_root graph_07 = addition_zero_right.
Proof. reflexivity. Qed.
Definition certificate_01 : Prover.proved odd_implies_natural := {|
  Prover.proof_graph := graph_01; Prover.proof_witness := witness_01;
  Prover.proof_checks := full_checked_01; Prover.proof_root := root_01 |}.
Definition certificate_04 : Prover.proved natural_implies_odd_or_even := {|
  Prover.proof_graph := graph_04; Prover.proof_witness := witness_04;
  Prover.proof_checks := full_checked_04; Prover.proof_root := root_04 |}.
Definition certificate_07 : Prover.proved addition_zero_right := {|
  Prover.proof_graph := graph_07; Prover.proof_witness := witness_07;
  Prover.proof_checks := full_checked_07; Prover.proof_root := root_07 |}.
Theorem benchmark_01_valid : valid Benchmarks.Env.defs odd_implies_natural.
Proof. exact (Prover.proved_sound _ certificate_01). Qed.
Theorem benchmark_04_valid : valid Benchmarks.Env.defs natural_implies_odd_or_even.
Proof. exact (Prover.proved_sound _ certificate_04). Qed.
Theorem benchmark_07_valid : valid Benchmarks.Env.defs addition_zero_right.
Proof. exact (Prover.proved_sound _ certificate_07). Qed.
Theorem benchmark_01_prove_returns : exists p,
  Prover.prove (focused_benchmark_limits 2000 3) odd_implies_natural = Some p.
Proof.
  apply staged_prove_exists with (g:=graph_01) (depth:=snd (proj1_sig transcript_01)).
  - exact (proj2_sig transcript_01).
  - exact (finish_checked _ _ _ root_01 witnessed_01 full_checked_01).
Qed.
Theorem benchmark_04_prove_returns : exists p,
  Prover.prove (focused_benchmark_limits 2000 3) natural_implies_odd_or_even = Some p.
Proof.
  apply staged_prove_exists with (g:=graph_04) (depth:=snd (proj1_sig transcript_04)).
  - exact (proj2_sig transcript_04).
  - exact (finish_checked _ _ _ root_04 witnessed_04 full_checked_04).
Qed.
Theorem benchmark_07_prove_returns : exists p,
  Prover.prove (focused_benchmark_limits 2000 3) addition_zero_right = Some p.
Proof.
  apply staged_prove_exists with (g:=graph_07) (depth:=snd (proj1_sig transcript_07)).
  - exact (proj2_sig transcript_07).
  - exact (finish_checked _ _ _ root_07 witnessed_07 full_checked_07).
Qed.

(** Failed-target diagnostics use the SAME generic lazy transitions. The smaller
    diagnostic fuel is explicit; it is not a substitute acceptance profile. *)
Definition root_menu j := fast_source_menu initial_benchmark_limits.(generation_budget)
  Benchmarks.Env.defs 0 j [(0,j)].
Definition root_menu_statistics j :=
  let m := root_menu j in
  (List.length m.(menu_axioms),List.length m.(menu_simplifications),
   List.length m.(menu_choices),map (fun p => List.length (program_frontier p)) m.(menu_choices),
   List.length (compiled_backlink_plans initial_benchmark_limits.(generation_budget)
     Benchmarks.Env.defs 0 j [(0,j)])).
Example root_menu_05 : root_menu_statistics naturals_imply_q = (0,0,3,[1;2;2],0).
Proof. vm_compute; reflexivity. Qed.
Example root_menu_08 : root_menu_statistics addition_preserves_natural = (0,0,4,[1;2;2;1],0).
Proof. vm_compute; reflexivity. Qed.
Example root_menu_13 : root_menu_statistics naturals_imply_hydra = (0,0,2,[2;2],0).
Proof. vm_compute; reflexivity. Qed.
Definition diagnostic_trace j := LazySearch.lazy_bounded_dfs_traced
  (Prover.api initial_benchmark_limits.(generation_budget)) 40 64 3 (Prover.C.start_graph j) 0.
Definition diagnostic_trace_statistics j :=
  let '(r,attempts) := diagnostic_trace j in
  (summarize_raw r,List.length attempts,
   match List.rev attempts with a::_ => Some (program_input a.(LazySearch.attempt_program))
     | [] => None end).
Example trace_05 : diagnostic_trace_statistics naturals_imply_q =
  (RawUnknown Search.FuelExhausted,15,Some {|
    antecedent := [[Pred 1 "N" [Var (Free 2)];Pred 2 "N" [successor (Var (Free 2))];Pred 0 "N" [x]]];
    succedent := [[Pred 0 "Q" [x;Var (Free 2)]]] |}).
Proof. Time vm_compute; reflexivity. Qed.
Example trace_13 : diagnostic_trace_statistics naturals_imply_hydra =
  (RawUnknown Search.FuelExhausted,16,Some {|
    antecedent := [[Pred 1 "N" [Var (Free 2)];Pred 3 "N" [successor (Var (Free 2))];Pred 2 "N" [zero]]];
    succedent := [[Pred 2 "H" [successor (Var (Free 2));zero]]] |}).
Proof. Time vm_compute; reflexivity. Qed.
Example trace_08 : diagnostic_trace_statistics addition_preserves_natural =
  (RawUnknown Search.FuelExhausted,14,Some {|
    antecedent := [[
      Pred 2 "ADD" [Var (Free 8);y;Var (Free 12)];
      Pred 4 "ADD" [successor (Var (Free 8));y;successor (Var (Free 12))];
      Pred 3 "ADD" [successor (successor (Var (Free 8)));y;
                      successor (successor (Var (Free 12)))];
      Pred 0 "N" [successor (successor (Var (Free 8)))];Pred 1 "N" [y]]];
    succedent := [[Pred 0 "N" [successor (Var (Free 12))]]] |}).
Proof. Time vm_compute; reflexivity. Qed.

Print Assumptions saturation_check_full.
Print Assumptions benchmark_01_valid.
Print Assumptions benchmark_04_valid.
Print Assumptions benchmark_07_valid.
