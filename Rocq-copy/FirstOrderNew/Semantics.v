From Stdlib Require Import List Bool Arith ZArith String Lia Classical_Prop.
From CyclistRocq.FirstOrderNew Require Export Definitions.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** No freeness of arbitrary constructors or distinctness of integer constants
    is assumed. These are exactly the constructor properties used by FO rules. *)
Record model := {
  carrier : Type;
  constant_value : Z -> carrier;
  function_value : string -> list carrier -> carrier;
  successor_injective : forall x y,
    function_value "s" [x] = function_value "s" [y] -> x = y;
  cons_injective : forall x y u v,
    function_value "cons" [x;y] = function_value "cons" [u;v] -> x = u /\ y = v;
  zero_not_successor : forall x, constant_value 0%Z <> function_value "s" [x];
  zero_not_cons : forall x y, constant_value 0%Z <> function_value "cons" [x;y]
}.
Definition valuation (m : model) := variable -> carrier m.
Fixpoint eval_term m (rho : valuation m) t : carrier m := match t with
  | Const z => constant_value m z | Var x => rho x
  | Fun f ts => function_value m f (map (eval_term m rho) ts) end.
Definition relation m := string -> list (carrier m) -> Prop.
Definition eval_atom_with m (r : relation m) rho a := match a with
  | Eq t u => eval_term m rho t = eval_term m rho u
  | Deq t u => eval_term m rho t <> eval_term m rho u
  | Pred _ p ts => r p (map (eval_term m rho) ts) end.
Definition eval_product_with m r rho p := Forall (eval_atom_with m r rho) p.

Fixpoint stage d m (n : nat) : relation m := match n with
  | 0 => fun _ _ => False
  | S k => fun p args => exists c, In c d /\ clause_name c = p /\
      exists rho : valuation m,
        map (eval_term m rho) (head c) = args /\
        eval_product_with m (stage d m k) rho (body c)
  end.
Definition inductive_relation d m : relation m :=
  fun p args => exists n, stage d m n p args.
Definition eval_atom d m := eval_atom_with m (inductive_relation d m).
Definition eval_product d m := eval_product_with m (inductive_relation d m).
Definition eval_formula d m rho f := exists p, In p f /\ eval_product d m rho p.
Definition agrees_free m (rho sigma : valuation m) := forall n, sigma (Free n) = rho (Free n).
Definition eval_right d m rho f := exists p, In p f /\
  exists sigma : valuation m, agrees_free m rho sigma /\ eval_product d m sigma p.
Definition valid d j := forall m (rho : valuation m),
  eval_formula d m rho j.(antecedent) -> eval_right d m rho j.(succedent).

Lemma product_monotone m r s rho p :
  (forall name args, r name args -> s name args) ->
  eval_product_with m r rho p -> eval_product_with m s rho p.
Proof.
  intros Hrs Hp. eapply Forall_impl; [|exact Hp]. intros a Ha.
  destruct a; cbn in *; auto.
Qed.
Lemma stage_step d m n : forall p args,
  stage d m n p args -> stage d m (S n) p args.
Proof.
  induction n as [|n IH]; cbn; [contradiction|].
  intros p args [c [Hc [Hname [rho [Hhead Hbody]]]]].
  exists c; repeat split; try assumption. exists rho; split; [exact Hhead|].
  eapply product_monotone; [exact IH|exact Hbody].
Qed.
Lemma stage_le d m n k : n <= k -> forall p args,
  stage d m n p args -> stage d m k p args.
Proof.
  intro H; induction H; intros p args Hp; [exact Hp|].
  apply stage_step; auto.
Qed.
Lemma atom_stage_bound d m rho a : eval_atom d m rho a ->
  exists n, eval_atom_with m (stage d m n) rho a.
Proof. destruct a; cbn; intro H; try (exists 0; exact H); exact H. Qed.
Lemma product_stage_bound d m rho p : eval_product d m rho p ->
  exists n, eval_product_with m (stage d m n) rho p.
Proof.
  intro H; induction H as [|a p Ha Hp [k Hk]].
  - exists 0; constructor.
  - destruct (atom_stage_bound d m rho a Ha) as [n Hn].
    exists (Nat.max n k); constructor.
    + destruct a; cbn in *; try exact Hn.
      eapply stage_le; [apply Nat.le_max_l|exact Hn].
    + eapply product_monotone; [|exact Hk].
      intros name args Hargs; eapply stage_le; [apply Nat.le_max_r|exact Hargs].
Qed.

(** Worlds record finite derivation bounds for individual antecedent
    occurrences. Quantifying over these bounds is equivalent to ordinary
    least-fixed-point validity, as proved below. Logical tags may be shared. *)
Fixpoint bounded_product d m rho (bounds : nat -> nat) start p : Prop :=
  match p with [] => True | a::p' =>
    eval_atom_with m (stage d m (bounds start)) rho a /\
    bounded_product d m rho bounds (S start) p' end.
Lemma bounded_product_forget d m rho bounds start p :
  bounded_product d m rho bounds start p -> eval_product d m rho p.
Proof.
  revert start; induction p as [|a p IH]; intros start H; constructor.
  - destruct H as [Ha Hp]; destruct a; cbn in *; try exact Ha.
    exists (bounds start); exact Ha.
  - apply (IH (S start)); exact (proj2 H).
Qed.
Lemma bounded_product_uniform d m rho n start p :
  eval_product_with m (stage d m n) rho p ->
  bounded_product d m rho (fun _ => n) start p.
Proof. intro H; revert start; induction H; cbn; auto. Qed.
Record world := { world_model : model;
  world_valuation : valuation world_model; active_product : nat;
  world_bounds : nat -> nat }.
Definition active_offset j w := List.length
  (List.concat (firstn w.(active_product) j.(antecedent))).
Definition active_holds d j w := exists p,
  nth_error j.(antecedent) w.(active_product) = Some p /\
  bounded_product d w.(world_model) w.(world_valuation) w.(world_bounds)
    (active_offset j w) p.
Definition denote d j w := active_holds d j w ->
  eval_right d w.(world_model) w.(world_valuation) j.(succedent).
Lemma valid_iff_worlds d j : valid d j <-> forall w, denote d j w.
Proof.
  split.
  - intros H [m rho i bounds] [p [Hi Hp]]. apply H. exists p; split.
    + eapply nth_error_In; exact Hi.
    + eapply bounded_product_forget; exact Hp.
  - intros H m rho [p [Hp Htruth]]. apply In_nth_error in Hp.
    destruct Hp as [i Hi]. destruct (product_stage_bound d m rho p Htruth) as [n Hn].
    apply (H {| world_model := m; world_valuation := rho; active_product := i;
      world_bounds := fun _ => n |}). exists p; split; [exact Hi|].
    cbn [world_model world_valuation world_bounds].
    apply bounded_product_uniform; exact Hn.
Qed.
Theorem inductive_unfold d m p args : inductive_relation d m p args <->
  exists c, In c d /\ clause_name c = p /\ exists rho : valuation m,
    map (eval_term m rho) (head c) = args /\ eval_product d m rho (body c).
Proof.
  split.
  - intros [[|n] H]; [contradiction|].
    destruct H as [c [Hc [Hname [rho [Hhead Hbody]]]]].
    exists c; repeat split; try assumption. exists rho; split; [exact Hhead|].
    eapply product_monotone; [|exact Hbody]. intros name xs Hx; exists n; exact Hx.
  - intros [c [Hc [Hname [rho [Hhead Hbody]]]]].
    destruct (product_stage_bound d m rho (body c) Hbody) as [n Hn].
    exists (S n), c; repeat split; try assumption. exists rho; auto.
Qed.
Theorem inductive_least d m (r : relation m)
  (Hclosed : forall c rho, In c d -> eval_product_with m r rho (body c) ->
    r (clause_name c) (map (eval_term m rho) (head c))) :
  forall p args, inductive_relation d m p args -> r p args.
Proof.
  intros p args [n Hn]; revert p args Hn.
  induction n as [|n IH]; [cbn; contradiction|].
  intros p args [c [Hc [<- [rho [<- Hbody]]]]]. apply Hclosed; [exact Hc|].
  eapply product_monotone; [exact IH|exact Hbody].
Qed.

Lemma eval_atom_erase d m rho a : eval_atom d m rho (erase_tag a) <-> eval_atom d m rho a.
Proof. destruct a; reflexivity. Qed.
Lemma eval_atom_logical_eq d m rho a b : atom_logical_eqb a b = true ->
  (eval_atom d m rho a <-> eval_atom d m rho b).
Proof.
  unfold atom_logical_eqb; intro H; apply eqb_of_dec_spec in H.
  rewrite <- eval_atom_erase, <- (eval_atom_erase d m rho b), H; reflexivity.
Qed.
Lemma product_subset_sound d m rho p q : product_subset p q = true ->
  eval_product d m rho q -> eval_product d m rho p.
Proof.
  intros Hsub Hq. apply Forall_forall; intros a Ha.
  apply forallb_forall with (x:=a) in Hsub; [|exact Ha].
  apply existsb_exists in Hsub; destruct Hsub as [b [Hb Heq]].
  apply (proj2 (eval_atom_logical_eq d m rho a b Heq)).
  apply Forall_forall with (x:=b) in Hq; auto.
Qed.
Theorem identity_sound d j : identityb j = true -> valid d j.
Proof.
  intros H m rho [p [Hp Htruth]].
  apply forallb_forall with (x:=p) in H; [|exact Hp].
  apply existsb_exists in H; destruct H as [q [Hq Hsub]].
  exists q; split; [exact Hq|]. exists rho; split; [intro n; reflexivity|].
  eapply product_subset_sound; eauto.
Qed.

(** Strong induction for the nested-list term syntax. *)
Lemma term_induction (P : term -> Prop)
  (HC : forall z, P (Const z)) (HV : forall x, P (Var x))
  (HF : forall f ts, Forall P ts -> P (Fun f ts)) : forall t, P t.
Proof.
  fix IH 1; intro t; destruct t.
  - apply HC.
  - apply HV.
  - apply HF. induction arguments; constructor; auto.
Qed.
Definition subst_valuation m s (rho : valuation m) : valuation m :=
  fun x => eval_term m rho (lookup s x).
Lemma eval_subst_term m s rho t : eval_term m rho (subst_term s t) =
  eval_term m (subst_valuation m s rho) t.
Proof.
  induction t using term_induction; cbn; try reflexivity.
  f_equal. rewrite map_map. apply map_ext_in; intros t Ht.
  apply Forall_forall with (x:=t) in H; auto.
Qed.
Lemma eval_subst_atom d m s rho a :
  eval_atom d m rho (subst_atom s a) <-> eval_atom d m (subst_valuation m s rho) a.
Proof.
  destruct a; cbn; try (rewrite !eval_subst_term; reflexivity).
  rewrite map_map. assert (map (fun t => eval_term m rho (subst_term s t)) arguments =
    map (eval_term m (subst_valuation m s rho)) arguments).
  { apply map_ext; apply eval_subst_term. } rewrite H; reflexivity.
Qed.
Lemma eval_subst_product d m s rho p :
  eval_product d m rho (subst_product s p) <->
  eval_product d m (subst_valuation m s rho) p.
Proof.
  unfold eval_product, eval_product_with, subst_product. rewrite Forall_map.
  split; intro H.
  - eapply Forall_impl; [|exact H]; intros a Ha.
    apply (proj1 (eval_subst_atom d m s rho a)); exact Ha.
  - eapply Forall_impl; [|exact H]; intros a Ha.
    apply (proj2 (eval_subst_atom d m s rho a)); exact Ha.
Qed.
