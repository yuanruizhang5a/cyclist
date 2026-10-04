From Stdlib Require Import List Arith Bool Lia.
From Stdlib Require Import Logic.ClassicalDescription Logic.ConstructiveEpsilon.
From CyclistRocq.FirstOrderNew Require Export Semantics.
Import ListNotations.

Definition predicate_rank d m p args :=
  match excluded_middle_informative (inductive_relation d m p args) with
  | left H => proj1_sig (epsilon_smallest (fun n => stage d m n p args)
      (fun n => excluded_middle_informative (stage d m n p args)) H)
  | right _ => 0 end.
Lemma predicate_rank_spec d m p args : inductive_relation d m p args ->
  stage d m (predicate_rank d m p args) p args.
Proof.
  intro H; unfold predicate_rank.
  destruct (excluded_middle_informative _) as [Hyes|Hno]; [|contradiction].
  destruct (epsilon_smallest _ _ Hyes) as [n [Hn Hmin]]; exact Hn.
Qed.
Lemma predicate_rank_min d m p args n : stage d m n p args ->
  predicate_rank d m p args <= n.
Proof.
  intro H; unfold predicate_rank.
  destruct (excluded_middle_informative _) as [Hyes|Hno].
  - destruct (epsilon_smallest _ _ Hyes) as [k [Hk Hmin]]; apply Hmin; exact H.
  - exfalso; apply Hno; exists n; exact H.
Qed.
Lemma predicate_rank_positive d m p args : inductive_relation d m p args ->
  0 < predicate_rank d m p args.
Proof.
  intro H; pose proof (predicate_rank_spec d m p args H).
  destruct (predicate_rank d m p args); [contradiction|lia].
Qed.
Definition atom_rank d m rho a := match a with
  | Pred _ p ts => predicate_rank d m p (map (eval_term m rho) ts)
  | _ => 0 end.
Definition rank (_ : definitions) (_ : sequent) (w : world) (t : nat) :=
  w.(world_bounds) t.

(** Each child of a minimum-height derivation has a strictly smaller rank.
    Occurrence identifiers avoid an invalid maximum/sum argument for grouped
    source tags, and remain valid when substitution collapses logical atoms. *)
Theorem minimum_unfold_decreases d m p args : inductive_relation d m p args ->
  exists c rho,
    In c d /\ clause_name c = p /\
    map (eval_term m rho) (head c) = args /\
    eval_product d m rho (body c) /\
    forall a, In a (body c) -> match a with
      | Pred _ _ _ => atom_rank d m rho a < predicate_rank d m p args
      | _ => True end.
Proof.
  intro H; pose proof (predicate_rank_spec d m p args H) as Hstage.
  destruct (predicate_rank d m p args) as [|n] eqn:E; [contradiction|].
  destruct Hstage as [c [Hc [Hname [rho [Hhead Hbody]]]]].
  exists c,rho; repeat split; try assumption.
  - eapply product_monotone; [|exact Hbody]. intros name xs Hx; exists n; exact Hx.
  - intros a Ha; destruct a; try exact I; cbn.
    apply Forall_forall with (x:=Pred tag symbol arguments) in Hbody; [|exact Ha].
    cbn in Hbody. pose proof (predicate_rank_min d m symbol
      (map (eval_term m rho) arguments) n Hbody); lia.
Qed.
Lemma atom_rank_substitution d m s rho a :
  atom_rank d m rho (subst_atom s a) = atom_rank d m (subst_valuation m s rho) a.
Proof.
  destruct a; cbn; try reflexivity. f_equal. rewrite map_map.
  apply map_ext; apply eval_subst_term.
Qed.
