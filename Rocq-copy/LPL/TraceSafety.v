(** * Compositional safety for finite traces

    These generic list lemmas support CounterLoop.v and NestedProgram.v.
    They reproduce the semantic overlap/power shapes without depending on a
    particular signature or kernel, so the lemmas apply to both model
    instances by definitional conversion. They prove every visited state
    safe, rather than only the final state or first observation. *)
From Stdlib Require Import List Arith.
From CyclistRocq.LPL Require Import Signature Syntax Semantics.
Import ListNotations.

(** Generic finite-trace invariant lemmas, independent of the LPL signature. *)
(** Compatibility names are thin aliases of the production trace algebra. *)
Definition trace_join {A} (a b c : list A) := TraceAlgebra.overlap_list a b c.
Definition trace_compose {A} (R T : list A -> Prop) tr := TraceAlgebra.trace_compose R T tr.
Definition trace_power {A} (R : list A -> Prop) n tr := TraceAlgebra.trace_power R n tr.
(** Safety assumes the invariant at the initial state and guarantees it on
    the entire execution list, including stuttering and intermediate states. *)
Definition trace_safe {A} (Inv : A -> Prop) (R : list A -> Prop) :=
  forall s tail, R (s :: tail) -> Inv s -> Forall Inv (s :: tail).

Lemma join_head {A} (a b c : list A) : trace_join a b c ->
  exists s tail tail', a = s :: tail /\ c = s :: tail'.
Proof. apply TraceAlgebra.overlap_list_head. Qed.
(** Combining two all-state invariants is valid even though their shared
    endpoint occurs only once in the overlapped result. No new state is
    introduced by joining the lists. *)
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

Module MakeSafety (L : LANGUAGE) (Syn : SYNTAX L) (Sem : SEMANTICS L Syn).
Export Syn Sem.
Section Model.
Context (M : Sem.model).
Variable Inv : state M -> Prop.
Hypothesis action_preserves : forall action s t,
  interpret_action M action s t -> Inv s -> Inv t.
(** Structural induction lifts one hypothesis about every atomic action to
    every program. Tests merely repeat a state, sequence and choice use the
    generic closure lemmas, and star uses induction on its finite count.
    The theorem is conditional on [action_preserves] for this chosen [Inv]. *)
Theorem program_safe p : trace_safe Inv (program_holds M p).
Proof.
  induction p.
  - intros s tail Hrun Hs; cbn [program_holds] in Hrun; apply atomic_trace_law in Hrun.
    destruct Hrun as [start [next [Heq Hstep]]]; injection Heq as Hstart Htail; subst.
    constructor; [exact Hs|]. constructor; [eapply action_preserves; eauto|constructor].
  - intros s tail [start [Heq _]] Hs; injection Heq as Hstart Htail; subst; repeat constructor; exact Hs.
  - apply compose_safe; assumption.
  - apply choice_safe; assumption.
  - intros s tail [n Hrun] Hs; apply (power_safe Inv (program_holds M p) IHp n s tail Hrun Hs).
Qed.
End Model.

(** The bridge needs a proved first-state property; arbitrary extensions are
    not assumed to have it. FOPL pure bodies and PPL atoms can supply it.
    Under this hypothesis, checking [a] on the current trace and every proper
    suffix is equivalent to checking [a] on each visited state's singleton.
    This theorem interprets [Always]; [program_safe] above establishes the
    separate invariant-preservation fact for executions. *)
Theorem always_head_forall M a :
  (forall s tail, formula_holds M a (s::tail) <-> formula_holds M a [s]) ->
  forall tr, tr<>[] ->
  (formula_holds M (Always a) tr <-> Forall (fun s => formula_holds M a [s]) tr).
Proof.
  intros Hhead tr; induction tr as [|s tail IH]; intro Hne; [contradiction|].
  (* A singleton has no proper suffix. With a nonempty tail, [suffix_step]
     separates the current head observation from the remaining suffix
     obligation, allowing the induction hypothesis to establish [Forall]. *)
  destruct tail as [|t tail].
  - unfold Always, Eventually; rewrite !nonempty_neg, nonempty_disj by discriminate.
    change (~ (~ formula_holds M a [s] \/ formula_holds M (Suffix Truth (Neg a)) [s]) <-> Forall (fun s => formula_holds M a [s]) [s]).
    rewrite Forall_cons_iff; pose proof (suffix_singleton M Truth (Neg a) s) as Hsuffix.
    split; [intro H; split; [tauto|constructor]|intros [H _]; tauto].
  - specialize (IH ltac:(discriminate)).
    unfold Always, Eventually in *; rewrite nonempty_neg in * by discriminate.
    rewrite nonempty_disj in * by discriminate.
    change (~ (formula_holds M (Neg a) (s::t::tail) \/ formula_holds M (Suffix Truth (Neg a)) (s::t::tail)) <->
      Forall (fun s => formula_holds M a [s]) (s::t::tail)).
    rewrite nonempty_neg, suffix_step by discriminate; rewrite nonempty_neg by discriminate.
    change (formula_holds M Truth (t::tail)) with True.
    rewrite (Hhead s (t::tail)).
    change (~ (formula_holds M (Neg a) (t::tail) \/ formula_holds M (Suffix Truth (Neg a)) (t::tail)) <->
      Forall (fun s => formula_holds M a [s]) (t::tail)) in IH.
    rewrite nonempty_neg in IH by discriminate; rewrite (Hhead t tail) in *.
    rewrite Forall_cons_iff; tauto.
Qed.
End MakeSafety.
