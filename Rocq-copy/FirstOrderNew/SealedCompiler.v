From Stdlib Require Import List Bool Arith.
From CyclistRocq.FirstOrderNew Require Export Compiler.
Import ListNotations.

(** Keep only executable application data after running the original checked
    compiler. No certificate or semantic evidence is an argument of the opaque
    theorem below: wrapping an already-built evidence value would still expose
    that value to VM normalization. *)
Definition compiled_application_data d j rd : option application :=
  option_map (certified_rule d j) (compile_rule_descriptor d j rd).

Lemma compiled_data_evidence d j rd a :
  compiled_application_data d j rd = Some a -> local_evidence d a.
Proof.
  unfold compiled_application_data.
  destruct (compile_rule_descriptor d j rd) as [c|] eqn:E; cbn; [|discriminate].
  intro H; inversion H; subst a; exact (certified_evidence d j c).
Qed.

Lemma compiled_data_conclusion d j rd a :
  compiled_application_data d j rd = Some a -> conclusion a = j.
Proof.
  unfold compiled_application_data.
  destruct (compile_rule_descriptor d j rd) as [c|] eqn:E; cbn; [|discriminate].
  intro H; inversion H; subst a; exact (certified_conclusion d j c).
Qed.

(** The dependent match captures only a data equality. Exact conclusion
    comparison is still executed independently before constructing a result. *)
Definition sealed_application_from_data d j rd (data : option application)
  (Hr : compiled_application_data d j rd = data) : option (certified_application d j) :=
  match data as result return compiled_application_data d j rd = result ->
    option (certified_application d j) with
  | Some a => fun Hdata => match sequent_eq_dec (conclusion a) j with
    | left Hconclusion => Some {| certified_rule := a;
        certified_conclusion := Hconclusion;
        certified_evidence := compiled_data_evidence d j rd a Hdata |}
    | right _ => None end
  | None => fun _ => None end Hr.

Definition sealed_compile_rule_descriptor d j rd : option (certified_application d j) :=
  sealed_application_from_data d j rd (compiled_application_data d j rd) eq_refl.

Lemma sealed_application_from_data_projection d j rd data Hr :
  option_map (certified_rule d j) (sealed_application_from_data d j rd data Hr) = data.
Proof.
  destruct data as [a|]; cbn [sealed_application_from_data]; [|reflexivity].
  destruct (sequent_eq_dec (conclusion a) j) as [Hconclusion|Hbad]; [reflexivity|].
  exfalso; apply Hbad; exact (compiled_data_conclusion d j rd a Hr).
Qed.

Theorem sealed_compile_application_data d j rd :
  option_map (certified_rule d j) (sealed_compile_rule_descriptor d j rd) =
  compiled_application_data d j rd.
Proof. apply sealed_application_from_data_projection. Qed.

Theorem sealed_compile_agrees d j rd :
  option_map (certified_rule d j) (sealed_compile_rule_descriptor d j rd) =
  option_map (certified_rule d j) (compile_rule_descriptor d j rd).
Proof. apply sealed_compile_application_data. Qed.

Theorem sealed_compile_rejects d j rd :
  sealed_compile_rule_descriptor d j rd = None <-> compile_rule_descriptor d j rd = None.
Proof.
  pose proof (sealed_compile_agrees d j rd) as E.
  destruct (sealed_compile_rule_descriptor d j rd), (compile_rule_descriptor d j rd);
    cbn in E; split; intro H; try discriminate; reflexivity.
Qed.

Theorem sealed_compile_success d j rd original :
  compile_rule_descriptor d j rd = Some original ->
  exists sealed, sealed_compile_rule_descriptor d j rd = Some sealed /\
    certified_rule d j sealed = certified_rule d j original.
Proof.
  intro H; pose proof (sealed_compile_agrees d j rd) as E; rewrite H in E.
  destruct (sealed_compile_rule_descriptor d j rd) as [c|] eqn:Hc;
    cbn in E; [exists c; split; [reflexivity|now inversion E]|discriminate].
Qed.

Theorem sealed_compile_fields d j rd sealed :
  sealed_compile_rule_descriptor d j rd = Some sealed ->
  exists original, compile_rule_descriptor d j rd = Some original /\
    certified_rule d j sealed = certified_rule d j original.
Proof.
  intro H; pose proof (sealed_compile_agrees d j rd) as E; rewrite H in E.
  destruct (compile_rule_descriptor d j rd) as [c|] eqn:Hc;
    cbn in E; [exists c; split; [reflexivity|now inversion E]|discriminate].
Qed.

(** Equality of whole applications includes names, exact conclusions, ordered
    premise labels, and all native continuation/progress annotations. *)
Theorem compiled_fields_sound d j rd a : compiled_application_data d j rd = Some a ->
  conclusion a = j /\
  ((forall p, In p (premises a) -> valid d (premise_label p)) -> valid d j).
Proof.
  intro H; split; [exact (compiled_data_conclusion d j rd a H)|].
  intro Hpremises; rewrite <- (compiled_data_conclusion d j rd a H).
  apply local_sound; [exact (compiled_data_evidence d j rd a H)|exact Hpremises].
Qed.

Theorem sealed_compiled_proposal_local_sound d p c :
  sealed_compile_rule_descriptor d (proposal_conclusion p) (proposal_descriptor p) = Some c ->
  application_matches p (certified_rule d (proposal_conclusion p) c) = true ->
  (forall k, In k (proposal_premises p) -> valid d k) -> valid d (proposal_conclusion p).
Proof.
  intros Hcompile Hmatch Hvalid.
  destruct (sealed_compile_fields d _ _ c Hcompile) as [original [Horiginal E]].
  eapply compiled_proposal_local_sound; [exact Horiginal|now rewrite <- E|exact Hvalid].
Qed.
