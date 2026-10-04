From Stdlib Require Import List Bool Arith String Lia.
From CyclistRocq.FirstOrderNew Require Export FastGeneration SealedCompiler LazySearch Witness.
Import ListNotations.

Record search_limits := {
  generation_budget : generation_limits;
  search_fuel : nat;
  macro_fuel : nat;
  first_depth : nat;
  last_depth : nat
}.
Definition default_search_limits := {| generation_budget := default_generation_limits;
  search_fuel := 2000; macro_fuel := 64; first_depth := 1; last_depth := 11 |}.

Module Make (D : DEFINITION_ENV).
  Module W := Witness.Make D.
  Module Proof := W.Proof.
  Module FO := W.FO.
  Module C := W.C.

  Definition graph_label g i := option_map C.node_judgment (C.node_at g i).
  Definition graph_indices g := seq 0 (List.length (C.graph_nodes g)).
  Definition labels g := flat_map (fun i => match graph_label g i with
    | Some j => [(i,j)] | None => [] end) (graph_indices g).
  Definition apply_native j g i (ca : certified_application D.defs j) :=
    let r := certified_rule D.defs j ca in
    match C.graph_apply_rule g i (FO.rule r (certified_evidence D.defs j ca)) with
    | Some g' => Some (C.fresh_ids (List.length (C.graph_nodes g))
                        (List.length (premises r)),g')
    | None => None end.

  Definition exact_native j e (H : exact_backlink_edgeb j e = true) :
    certified_application D.defs j.
  Proof.
    refine {| certified_rule := {| application_name := "exact_backlink"%string;
      conclusion := j; premises := [{| premise_label := j; premise_trace := e |}] |};
      certified_conclusion := eq_refl |}.
    constructor; intros w Hbad; exists 0; eexists; exists w;
      split; [reflexivity|]; split; [exact Hbad|].
    unfold exact_backlink_edgeb in H; apply andb_true_iff in H;
      destruct H as [Hp Hv]. apply Nat.eqb_eq in Hp.
    split.
    - intros a b Hab. apply forallb_forall with (x:=(a,b)) in Hv; [|exact Hab].
      apply andb_true_iff in Hv; destruct Hv as [Heq _]; cbn in Heq.
      apply Nat.eqb_eq in Heq; subst b; apply Nat.le_refl.
    - destruct (progressing e) eqn:Ep; cbn in Hp; [|discriminate].
      intros a b Hab; cbn in Hab; rewrite Ep in Hab; contradiction.
  Defined.
  Definition close_native g i target e : option C.graph :=
    match graph_label g target with
    | None => None
    | Some j => match Bool.bool_dec (exact_backlink_edgeb j e) true with
      | left H => let ca := exact_native j e H in
        C.graph_add_backlink g i target
          (FO.rule (certified_rule D.defs j ca) (certified_evidence D.defs j ca))
      | right _ => None end end.

  (** The search loop uses the cheap proof-producing routing criterion. The
      frozen relational checker is additionally checked when packaging success;
      lazy evaluation avoids eagerly materializing its exponential fuel. *)
  Definition routing_accept g := C.structural_check g && W.partial_check g.
  Definition api limits : search_api D.defs C.graph := {|
    node_label := graph_label; node_indices := graph_indices;
    generate_rules := fun g i j => fast_source_menu limits D.defs i j (labels g);
    compile_descriptor := sealed_compile_rule_descriptor D.defs;
    apply_application := apply_native;
    close_exact := close_native;
    partial_trace_check := W.partial_check;
    final_accept := routing_accept |}.

  Definition search_graph limits j : search_result C.graph :=
    if definitions_wfb D.defs && sequent_wfb D.defs j then
      lazy_iddfs (api limits.(generation_budget)) limits.(search_fuel) limits.(macro_fuel)
        limits.(first_depth) limits.(last_depth) (C.start_graph j) 0
    else Unknown NoCandidate.

  Record proved (j : sequent) := {
    proof_graph : C.graph;
    proof_witness : C.trace_witness;
    proof_checks : C.raw_check proof_graph proof_witness = true;
    proof_root : C.graph_root proof_graph = j
  }.
  Definition finish_proof j (g : C.graph) : option (proved j).
  Proof.
    destruct (Bool.bool_dec (sequent_eqb (C.graph_root g) j) true) as [Hroot|]; [|exact None].
    destruct (W.find_witness g) as [tw|] eqn:Htw; [|exact None].
    destruct (Bool.bool_dec (C.raw_check g tw) true) as [Hchecks|]; [|exact None].
    refine (Some {| proof_graph := g; proof_witness := tw; proof_checks := Hchecks;
      proof_root := proj1 (sequent_eqb_spec _ _) Hroot |}).
  Defined.
  Definition prove limits j := match search_graph limits j with
    | Found g _ => finish_proof j g | Unknown _ => None end.
  Theorem proved_sound j (p : proved j) : valid D.defs j.
  Proof.
    rewrite <- (proof_root j p).
    exact (Proof.checked_graph_sound (proof_graph j p) (proof_witness j p) (proof_checks j p)).
  Qed.
  Theorem prove_sound limits j p : prove limits j = Some p -> valid D.defs j.
  Proof. intros _; apply (proved_sound j p). Qed.
  Definition solvedb limits j := match prove limits j with Some _ => true | None => false end.
End Make.
