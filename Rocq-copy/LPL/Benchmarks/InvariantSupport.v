(** * Compositional safety for finite traces

    These generic list lemmas support CounterLoop.v and NestedProgram.v.
    They reproduce the semantic overlap/power shapes without depending on a
    particular signature or kernel, so the lemmas apply to both model
    instances by definitional conversion. They prove every visited state
    safe, rather than only the final state or first observation. *)
From Stdlib Require Import List Arith.
Import ListNotations.

(** Generic finite-trace invariant lemmas, independent of the LPL signature. *)
Definition trace_join {A} (a b c : list A) :=
  exists prefix s tail, a = prefix ++ [s] /\ b = s :: tail /\ c = prefix ++ s :: tail.
Definition trace_compose {A} (R T : list A -> Prop) tr :=
  exists a b, R a /\ T b /\ trace_join a b tr.
Section Powers.
Context {A : Type}.
Fixpoint trace_power (R : list A -> Prop) n tr :=
  match n with 0 => exists s, tr = [s;s]
  | S n => trace_compose R (trace_power R n) tr end.
End Powers.
(** Safety assumes the invariant at the initial state and guarantees it on
    the entire execution list, including stuttering and intermediate states. *)
Definition trace_safe {A} (Inv : A -> Prop) (R : list A -> Prop) :=
  forall s tail, R (s :: tail) -> Inv s -> Forall Inv (s :: tail).

Lemma join_head {A} (a b c : list A) : trace_join a b c ->
  exists s tail tail', a = s :: tail /\ c = s :: tail'.
Proof. intros [[|x prefix] [s [tail [-> [-> ->]]]]]; cbn; eauto. Qed.
Lemma join_Forall {A} (Inv : A -> Prop) a b c : trace_join a b c ->
  Forall Inv a -> Forall Inv b -> Forall Inv c.
Proof.
  intros [prefix [s [tail [-> [-> ->]]]]] Ha Hb.
  rewrite Forall_app in Ha |- *; tauto.
Qed.
(** First use safety of [R]; its final shared state supplies the initial
    invariant needed by [T]. [join_Forall] then combines both all-state facts
    on the overlapped result. This is why endpoint overlap matters. *)
Lemma compose_safe {A} (Inv : A -> Prop) R T : trace_safe Inv R -> trace_safe Inv T ->
  trace_safe Inv (trace_compose R T).
Proof.
  intros HR HT s tail [a [b [Ha [Hb Ho]]]] Hs.
  destruct (join_head a b (s::tail) Ho) as [head [arest [crest [Hfirst Heq]]]].
  injection Heq as Hhead Htail; subst head. subst a.
  pose proof (HR s arest Ha Hs) as HsafeA.
  destruct Ho as [prefix [middle [btail [Haend [Hbstart Hresult]]]]].
  assert (Inv middle) as Hmiddle.
  { rewrite Forall_forall in HsafeA; apply HsafeA; rewrite Haend; apply in_app_iff; cbn; auto. }
  rewrite Hbstart in Hb. pose proof (HT middle btail Hb Hmiddle) as HsafeB.
  eapply join_Forall; [exists prefix,middle,btail; eauto|exact HsafeA|].
  now rewrite Hbstart.
Qed.
Lemma choice_safe {A} (Inv : A -> Prop) R T : trace_safe Inv R -> trace_safe Inv T ->
  trace_safe Inv (fun tr => R tr \/ T tr).
Proof. intros HR HT s tail [H|H] Hs; [eapply HR|eapply HT]; eauto. Qed.
(** Induct on an arbitrary finite iteration count. Zero repeats the initial
    state twice; the successor case is just compositional safety. No claim
    about reaching an exit condition or about infinite executions is needed. *)
Lemma power_safe {A} (Inv : A -> Prop) R : trace_safe Inv R -> forall n, trace_safe Inv (trace_power R n).
Proof.
  intros HR n; induction n.
  - intros s tail [start Heq] Hs; injection Heq as Hstart Htail; subst; repeat constructor; exact Hs.
  - apply compose_safe; assumption.
Qed.
