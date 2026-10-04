From Stdlib Require Import List Bool Arith ZArith String Lia Classical_Prop.
From CyclistRocq.FirstOrderNew Require Export Rank Matching.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Record trace_edge := { continuations : list (nat * nat); progressing : list (nat * nat) }.
Definition empty_edge := {| continuations := []; progressing := [] |}.
Record native_premise := { premise_label : sequent; premise_trace : trace_edge }.
Record application := { application_name : string;
  conclusion : sequent; premises : list native_premise }.
Definition respects d source target w w' e :=
  (forall a b, In (a,b) e.(continuations) -> rank d target w' b <= rank d source w a) /\
  (forall a b, In (a,b) e.(progressing) -> rank d target w' b < rank d source w a).
Record local_evidence d (r : application) := {
  local_counter_step : forall w, ~ denote d r.(conclusion) w ->
    { k : nat & { p : native_premise & { w' : world |
      nth_error r.(premises) k = Some p /\ ~ denote d p.(premise_label) w' /\
      respects d r.(conclusion) p.(premise_label) w w' p.(premise_trace) } } }
}.
Record certified_application d (j : sequent) := {
  certified_rule : application;
  certified_conclusion : certified_rule.(conclusion) = j;
  certified_evidence : local_evidence d certified_rule
}.
Theorem local_sound d r : local_evidence d r ->
  (forall p, In p r.(premises) -> valid d p.(premise_label)) -> valid d r.(conclusion).
Proof.
  intros E Hps. apply valid_iff_worlds; intros w.
  apply NNPP; intro Hfalse.
  destruct (local_counter_step d r E w Hfalse) as [k [p [w' [Hk [Hbad Hrank]]]]].
  apply Hbad. apply valid_iff_worlds. apply Hps. eapply nth_error_In; exact Hk.
Qed.

Definition constructorb t := match t with
  | Fun f ts => (String.eqb f "s" && Nat.eqb (List.length ts) 1) ||
                (String.eqb f "cons" && Nat.eqb (List.length ts) 2)
  | _ => false end.
Definition contradictory_atom a := match a with
  | Deq t u => term_eqb t u
  | Eq t u =>
    let zero_constructor x y := term_eqb x zero && constructorb y in
    zero_constructor t u || zero_constructor u t
  | _ => false end.
Definition contradictionb j := forallb (existsb contradictory_atom) j.(antecedent).
Lemma constructor_not_zero m rho t : constructorb t = true ->
  constant_value m 0%Z <> eval_term m rho t.
Proof.
  destruct t as [z|x|f ts]; cbn; try discriminate.
  rewrite orb_true_iff; intros [H|H]; apply andb_true_iff in H;
    destruct H as [Hf Hlen]; apply String.eqb_eq in Hf;
    apply Nat.eqb_eq in Hlen; subst f.
  - destruct ts as [|a [|b ts]]; cbn in Hlen; try discriminate.
    cbn; apply zero_not_successor.
  - destruct ts as [|a [|b [|c ts]]]; cbn in Hlen; try discriminate.
    cbn; apply zero_not_cons.
Qed.
Lemma contradictory_atom_sound d m rho a : contradictory_atom a = true ->
  ~ eval_atom d m rho a.
Proof.
  destruct a; cbn; try discriminate.
  - rewrite orb_true_iff; intros [H|H]; apply andb_true_iff in H;
      destruct H as [Hz Hc]; apply eqb_of_dec_spec in Hz; subst; cbn.
    + apply constructor_not_zero; exact Hc.
    + intro H; apply (constructor_not_zero m rho left Hc); symmetry; exact H.
  - intro H; apply eqb_of_dec_spec in H; subst; cbn; intuition.
Qed.
Theorem contradiction_sound d j : contradictionb j = true -> valid d j.
Proof.
  intros H m rho [p [Hp Htruth]].
  apply forallb_forall with (x:=p) in H; [|exact Hp].
  apply existsb_exists in H; destruct H as [a [Ha Hbad]].
  exfalso; apply (contradictory_atom_sound d m rho a Hbad).
  apply Forall_forall with (x:=a) in Htruth; auto.
Qed.
Definition axiom_check j := contradictionb j || identityb j.
Theorem axiom_check_sound d j : axiom_check j = true -> valid d j.
Proof. unfold axiom_check; rewrite orb_true_iff; intros [H|H];
  [apply contradiction_sound|apply identity_sound]; assumption. Qed.

Definition lhs_split j := map
  (fun p => {| antecedent := [p]; succedent := j.(succedent) |}) j.(antecedent).
Theorem lhs_split_sound d j : (forall k, In k (lhs_split j) -> valid d k) -> valid d j.
Proof.
  intros H m rho [p [Hp Htruth]]. apply (H {| antecedent := [p];
    succedent := succedent j |});
    [unfold lhs_split; apply in_map_iff; exists p; auto|].
  exists p; split; [now left|exact Htruth].
Qed.
Theorem weakening_sound d j k :
  (forall m rho, eval_formula d m rho j.(antecedent) ->
                eval_formula d m rho k.(antecedent)) ->
  (forall m rho, eval_right d m rho k.(succedent) -> eval_right d m rho j.(succedent)) ->
  valid d k -> valid d j.
Proof. unfold valid; intros Hl Hr H m rho Hp; apply Hr, H, Hl, Hp. Qed.

(** Folding a clause instance is sound without freshness: the substitution
    valuation provides its clause witnesses. *)
Theorem fold_instance d m rho c s : In c d ->
  eval_product d m rho (subst_product s (body c)) ->
  inductive_relation d m (clause_name c)
    (map (eval_term m rho) (map (subst_term s) (head c))).
Proof.
  intros Hc Hbody. apply inductive_unfold.
  exists c; split; [exact Hc|]. split; [reflexivity|].
  exists (subst_valuation m s rho); split.
  - rewrite map_map; symmetry; apply map_ext; apply eval_subst_term.
  - apply eval_subst_product in Hbody; exact Hbody.
Qed.
