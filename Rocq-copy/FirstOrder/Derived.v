From Stdlib Require Import List Arith Lia String Wf_nat.

From CyclistRocq.FirstOrder Require Import
  Syntax Semantics Definitions.

Import ListNotations.
Open Scope string_scope.

Definition vzero : value := VConst 0.
Definition vsucc (x : value) : value := VFun "s" [x].

Definition value_env (xs : list value) : valuation :=
  fun x => nth x.(variable_id) xs vzero.

Definition ranked (i : interpretation) (name : string)
    (args : list value) (height : nat) : Prop :=
  i.(predicate_rank) name args = Some height.

Definition holds (i : interpretation) (name : string)
    (args : list value) : Prop := predicate_holds i name args.

Lemma ranked_holds i name args height :
  ranked i name args height -> holds i name args.
Proof. intro H. exists height. exact H. Qed.

Lemma model_intro ds i name c rho :
  models ds i ->
  In c (lookup_definition name ds) ->
  product_holds i rho c.(clause_body) ->
  holds i name (eval_terms rho c.(clause_head)).
Proof. intros [Hintro _]. now apply Hintro. Qed.

Lemma model_elim ds i name args height :
  models ds i ->
  ranked i name args height ->
  exists c rho,
    In c (lookup_definition name ds) /\
    eval_terms rho c.(clause_head) = args /\
    product_holds i rho c.(clause_body) /\
    body_decreases i rho c.(clause_body) height.
Proof. intros [_ Helim]. now apply Helim. Qed.

Lemma n_zero i : models fo_definitions i -> holds i "N" [vzero].
Proof.
  intro Hmodel. eapply model_intro with
    (c := clause_of [] [zero]) (rho := value_env []); try exact Hmodel;
    cbn; auto.
Qed.

Lemma n_succ i x :
  models fo_definitions i -> holds i "N" [x] -> holds i "N" [vsucc x].
Proof.
  intros Hmodel Hx. eapply model_intro with
    (c := clause_of [pred "N" [fv 0]] [succ (fv 0)])
    (rho := value_env [x]); try exact Hmodel; cbn; auto.
Qed.

Lemma e_zero i : models fo_definitions i -> holds i "E" [vzero].
Proof.
  intro Hmodel. eapply model_intro with
    (c := clause_of [] [zero]) (rho := value_env []); try exact Hmodel;
    cbn; auto.
Qed.

Lemma e_succ i x :
  models fo_definitions i -> holds i "O" [x] -> holds i "E" [vsucc x].
Proof.
  intros Hmodel Hx. eapply model_intro with
    (c := clause_of [pred "O" [fv 0]] [succ (fv 0)])
    (rho := value_env [x]); try exact Hmodel; cbn; auto.
Qed.

Lemma o_succ i x :
  models fo_definitions i -> holds i "E" [x] -> holds i "O" [vsucc x].
Proof.
  intros Hmodel Hx. eapply model_intro with
    (c := clause_of [pred "E" [fv 0]] [succ (fv 0)])
    (rho := value_env [x]); try exact Hmodel; cbn; auto.
Qed.

Lemma p_zero i : models fo_definitions i -> holds i "P" [vzero].
Proof.
  intro Hmodel. eapply model_intro with
    (c := clause_of [] [zero]) (rho := value_env []); try exact Hmodel;
    cbn; auto.
Qed.

Lemma p_succ i x :
  models fo_definitions i ->
  holds i "P" [x] -> holds i "Q" [x; vsucc x] ->
  holds i "P" [vsucc x].
Proof.
  intros Hmodel Hp Hq. eapply model_intro with
    (c := clause_of [pred "P" [fv 0]; pred "Q" [fv 0; succ (fv 0)]]
      [succ (fv 0)]) (rho := value_env [x]); try exact Hmodel;
    cbn; auto.
Qed.

Lemma q_zero i x : models fo_definitions i -> holds i "Q" [x; vzero].
Proof.
  intro Hmodel. eapply model_intro with
    (c := clause_of [] [fv 0; zero]) (rho := value_env [x]);
    try exact Hmodel; cbn; auto.
Qed.

Lemma q_succ i x y :
  models fo_definitions i ->
  holds i "Q" [x; y] -> holds i "P" [x] ->
  holds i "Q" [x; vsucc y].
Proof.
  intros Hmodel Hq Hp. eapply model_intro with
    (c := clause_of [pred "Q" [fv 0; fv 1]; pred "P" [fv 0]]
      [fv 0; succ (fv 1)]) (rho := value_env [x; y]);
    try exact Hmodel; cbn; auto.
Qed.

Lemma add_zero i y :
  models fo_definitions i -> holds i "N" [y] -> holds i "ADD" [vzero; y; y].
Proof.
  intros Hmodel Hy. eapply model_intro with
    (c := clause_of [pred "N" [fv 0]] [zero; fv 0; fv 0])
    (rho := value_env [y]); try exact Hmodel; cbn; auto.
Qed.

Lemma add_succ i x y z :
  models fo_definitions i -> holds i "ADD" [x; y; z] ->
  holds i "ADD" [vsucc x; y; vsucc z].
Proof.
  intros Hmodel Hadd. eapply model_intro with
    (c := clause_of [pred "ADD" [fv 0; fv 1; fv 2]]
      [succ (fv 0); fv 1; succ (fv 2)])
    (rho := value_env [x; y; z]); try exact Hmodel; cbn; auto.
Qed.

Lemma n2_zero i y :
  models fo_definitions i -> holds i "N" [y] -> holds i "N2" [vzero; y].
Proof.
  intros Hmodel Hy. eapply model_intro with
    (c := clause_of [pred "N" [fv 0]] [zero; fv 0])
    (rho := value_env [y]); try exact Hmodel; cbn; auto.
Qed.

Lemma n2_succ i x y :
  models fo_definitions i -> holds i "N2" [y; x] ->
  holds i "N2" [vsucc x; y].
Proof.
  intros Hmodel Hn2. eapply model_intro with
    (c := clause_of [pred "N2" [fv 0; fv 1]] [succ (fv 1); fv 0])
    (rho := value_env [y; x]); try exact Hmodel; cbn; auto.
Qed.

Lemma h_00 i : models fo_definitions i -> holds i "H" [vzero; vzero].
Proof.
  intro Hmodel. eapply model_intro with
    (c := clause_of [] [zero; zero]) (rho := value_env []);
    try exact Hmodel; cbn; auto.
Qed.

Lemma h_10 i : models fo_definitions i -> holds i "H" [vsucc vzero; vzero].
Proof.
  intro Hmodel. eapply model_intro with
    (c := clause_of [] [succ zero; zero]) (rho := value_env []);
    try exact Hmodel; cbn; auto.
Qed.

Lemma h_x1 i x : models fo_definitions i -> holds i "H" [x; vsucc vzero].
Proof.
  intro Hmodel. eapply model_intro with
    (c := clause_of [] [fv 0; succ zero]) (rho := value_env [x]);
    try exact Hmodel; cbn; auto.
Qed.

Lemma h_step i x y :
  models fo_definitions i -> holds i "H" [x; y] ->
  holds i "H" [vsucc x; vsucc (vsucc y)].
Proof.
  intros Hmodel Hh. eapply model_intro with
    (c := clause_of [pred "H" [fv 0; fv 1]]
      [succ (fv 0); succ (succ (fv 1))])
    (rho := value_env [x; y]); try exact Hmodel; cbn; auto.
Qed.

Lemma h_zero_step i y :
  models fo_definitions i -> holds i "H" [vsucc y; y] ->
  holds i "H" [vzero; vsucc (vsucc y)].
Proof.
  intros Hmodel Hh. eapply model_intro with
    (c := clause_of [pred "H" [succ (fv 1); fv 1]]
      [zero; succ (succ (fv 1))])
    (rho := value_env [vzero; y]).
  - exact Hmodel.
  - cbn. tauto.
  - cbn. tauto.
Qed.

Lemma h_end_step i x :
  models fo_definitions i -> holds i "H" [vsucc x; x] ->
  holds i "H" [vsucc (vsucc x); vzero].
Proof.
  intros Hmodel Hh. eapply model_intro with
    (c := clause_of [pred "H" [succ (fv 0); fv 0]]
      [succ (succ (fv 0)); zero])
    (rho := value_env [x]).
  - exact Hmodel.
  - cbn. tauto.
  - cbn. tauto.
Qed.

(** Inversion exposes both constructor shape and the strictly smaller rank
    that drives proof search on inductive antecedents. *)
Lemma n_rank_inversion i x height :
  models fo_definitions i -> ranked i "N" [x] height ->
  x = vzero \/
  exists y child,
    x = vsucc y /\ ranked i "N" [y] child /\ child < height.
Proof.
  intros Hmodel Hrank.
  destruct (model_elim fo_definitions i "N" [x] height Hmodel Hrank)
    as [c [rho [Hin [Hhead [Hbody Hdec]]]]].
  cbn in Hin. destruct Hin as [<- | [<- | []]].
  - left. cbn in Hhead. now inversion Hhead.
  - right. cbn in Hhead. inversion Hhead; subst x.
    destruct (Hdec None "N" [fv 0] ltac:(now left))
      as [child [Hchild Hlt]].
    exists (rho (free_var 0)), child. cbn in Hchild. auto.
Qed.

Lemma e_rank_inversion i x height :
  models fo_definitions i -> ranked i "E" [x] height ->
  x = vzero \/
  exists y child,
    x = vsucc y /\ ranked i "O" [y] child /\ child < height.
Proof.
  intros Hmodel Hrank.
  destruct (model_elim fo_definitions i "E" [x] height Hmodel Hrank)
    as [c [rho [Hin [Hhead [Hbody Hdec]]]]].
  cbn in Hin. destruct Hin as [<- | [<- | []]].
  - left. cbn in Hhead. now inversion Hhead.
  - right. cbn in Hhead. inversion Hhead; subst x.
    destruct (Hdec None "O" [fv 0] ltac:(now left))
      as [child [Hchild Hlt]].
    exists (rho (free_var 0)), child. cbn in Hchild. auto.
Qed.

Lemma o_rank_inversion i x height :
  models fo_definitions i -> ranked i "O" [x] height ->
  exists y child,
    x = vsucc y /\ ranked i "E" [y] child /\ child < height.
Proof.
  intros Hmodel Hrank.
  destruct (model_elim fo_definitions i "O" [x] height Hmodel Hrank)
    as [c [rho [Hin [Hhead [Hbody Hdec]]]]].
  cbn in Hin. destruct Hin as [<- | []].
  cbn in Hhead. inversion Hhead; subst x.
  destruct (Hdec None "E" [fv 0] ltac:(now left))
    as [child [Hchild Hlt]].
  exists (rho (free_var 0)), child. cbn in Hchild. auto.
Qed.

Lemma add_rank_inversion i x y z height :
  models fo_definitions i -> ranked i "ADD" [x; y; z] height ->
  (x = vzero /\ z = y /\ holds i "N" [y]) \/
  exists x' z' child,
    x = vsucc x' /\ z = vsucc z' /\
    ranked i "ADD" [x'; y; z'] child /\ child < height.
Proof.
  intros Hmodel Hrank.
  destruct (model_elim fo_definitions i "ADD" [x; y; z] height Hmodel Hrank)
    as [c [rho [Hin [Hhead [Hbody Hdec]]]]].
  cbn in Hin. destruct Hin as [<- | [<- | []]].
  - left. cbn in Hhead, Hbody. inversion Hhead; subst x z.
    tauto.
  - right. cbn in Hhead. inversion Hhead; subst x y z.
    destruct (Hdec None "ADD" [fv 0; fv 1; fv 2] ltac:(now left))
      as [child [Hchild Hlt]].
    exists (rho (free_var 0)), (rho (free_var 2)), child.
    cbn in Hchild. auto.
Qed.

Fixpoint value_depth (x : value) : nat :=
  match x with
  | VConst _ => 0
  | VFun _ xs => S (fold_right Nat.max 0 (map value_depth xs))
  end.

Lemma value_depth_succ x : value_depth (vsucc x) = S (value_depth x).
Proof. cbn. now rewrite Nat.max_0_r. Qed.

Lemma even_odd_natural_by_rank i :
  models fo_definitions i ->
  forall height,
    (forall x, ranked i "E" [x] height -> holds i "N" [x]) /\
    (forall x, ranked i "O" [x] height -> holds i "N" [x]).
Proof.
  intros Hmodel height. induction height using lt_wf_ind.
  split.
  - intros x Hrank. destruct (e_rank_inversion i x height Hmodel Hrank)
      as [-> | [y [child [-> [Hchild Hlt]]]]].
    + apply n_zero. exact Hmodel.
    + apply n_succ; [exact Hmodel|].
      exact (proj2 (H child Hlt) y Hchild).
  - intros x Hrank. destruct (o_rank_inversion i x height Hmodel Hrank)
      as [y [child [-> [Hchild Hlt]]]].
    apply n_succ; [exact Hmodel|].
    exact (proj1 (H child Hlt) y Hchild).
Qed.

Lemma even_natural i x :
  models fo_definitions i -> holds i "E" [x] -> holds i "N" [x].
Proof.
  intros Hmodel [height Hrank].
  exact (proj1 (even_odd_natural_by_rank i Hmodel height) x Hrank).
Qed.

Lemma odd_natural i x :
  models fo_definitions i -> holds i "O" [x] -> holds i "N" [x].
Proof.
  intros Hmodel [height Hrank].
  exact (proj2 (even_odd_natural_by_rank i Hmodel height) x Hrank).
Qed.

Lemma natural_parity_by_rank i :
  models fo_definitions i ->
  forall height x, ranked i "N" [x] height ->
    holds i "O" [x] \/ holds i "E" [x].
Proof.
  intros Hmodel height. induction height using lt_wf_ind.
  intros x Hrank. destruct (n_rank_inversion i x height Hmodel Hrank)
    as [-> | [y [child [-> [Hchild Hlt]]]]].
  - right. apply e_zero. exact Hmodel.
  - destruct (H child Hlt y Hchild) as [Ho | He].
    + right. now apply e_succ.
    + left. now apply o_succ.
Qed.

Lemma natural_parity i x :
  models fo_definitions i -> holds i "N" [x] ->
  holds i "O" [x] \/ holds i "E" [x].
Proof.
  intros Hmodel [height Hrank].
  now apply (natural_parity_by_rank i Hmodel height x).
Qed.

Lemma q_for_p_by_n_rank i x :
  models fo_definitions i -> holds i "P" [x] ->
  forall height y, ranked i "N" [y] height -> holds i "Q" [x; y].
Proof.
  intros Hmodel Hp height. induction height using lt_wf_ind.
  intros y Hrank. destruct (n_rank_inversion i y height Hmodel Hrank)
    as [-> | [z [child [-> [Hchild Hlt]]]]].
  - now apply q_zero.
  - apply q_succ; [exact Hmodel| |exact Hp].
    exact (H child Hlt z Hchild).
Qed.

Lemma q_for_p i x y :
  models fo_definitions i -> holds i "P" [x] -> holds i "N" [y] ->
  holds i "Q" [x; y].
Proof.
  intros Hmodel Hp [height Hrank].
  exact (q_for_p_by_n_rank i x Hmodel Hp height y Hrank).
Qed.

Lemma p_for_n_by_rank i :
  models fo_definitions i ->
  forall height x, ranked i "N" [x] height -> holds i "P" [x].
Proof.
  intros Hmodel height. induction height using lt_wf_ind.
  intros x Hrank. destruct (n_rank_inversion i x height Hmodel Hrank)
    as [-> | [y [child [-> [Hchild Hlt]]]]].
  - apply p_zero. exact Hmodel.
  - pose proof (H child Hlt y Hchild) as Hp.
    apply p_succ; [exact Hmodel|exact Hp|].
    eapply q_for_p; [exact Hmodel|exact Hp|].
    apply ranked_holds with (height := height). exact Hrank.
Qed.

Lemma p_for_n i x :
  models fo_definitions i -> holds i "N" [x] -> holds i "P" [x].
Proof.
  intros Hmodel [height Hrank].
  exact (p_for_n_by_rank i Hmodel height x Hrank).
Qed.

Lemma q_for_naturals i x y :
  models fo_definitions i -> holds i "N" [x] -> holds i "N" [y] ->
  holds i "Q" [x; y].
Proof.
  intros Hmodel Hx Hy. eapply q_for_p; eauto using p_for_n.
Qed.

Lemma add_zero_right_by_n_rank i :
  models fo_definitions i ->
  forall height x, ranked i "N" [x] height -> holds i "ADD" [x; vzero; x].
Proof.
  intros Hmodel height. induction height using lt_wf_ind.
  intros x Hrank. destruct (n_rank_inversion i x height Hmodel Hrank)
    as [-> | [y [child [-> [Hchild Hlt]]]]].
  - apply add_zero; [exact Hmodel|]. apply n_zero. exact Hmodel.
  - apply add_succ; [exact Hmodel|]. exact (H child Hlt y Hchild).
Qed.

Lemma add_zero_right i x :
  models fo_definitions i -> holds i "N" [x] -> holds i "ADD" [x; vzero; x].
Proof.
  intros Hmodel [height Hrank].
  exact (add_zero_right_by_n_rank i Hmodel height x Hrank).
Qed.

Lemma add_result_natural_by_rank i :
  models fo_definitions i ->
  forall height x y z, ranked i "ADD" [x; y; z] height -> holds i "N" [z].
Proof.
  intros Hmodel height. induction height using lt_wf_ind.
  intros x y z Hrank.
  destruct (add_rank_inversion i x y z height Hmodel Hrank)
    as [[-> [-> Hy]] | [x' [z' [child [-> [-> [Hchild Hlt]]]]]]].
  - exact Hy.
  - apply n_succ; [exact Hmodel|]. exact (H child Hlt x' y z' Hchild).
Qed.

Lemma add_result_natural i x y z :
  models fo_definitions i -> holds i "ADD" [x; y; z] -> holds i "N" [z].
Proof.
  intros Hmodel [height Hrank].
  exact (add_result_natural_by_rank i Hmodel height x y z Hrank).
Qed.

Lemma add_shift_right_by_rank i :
  models fo_definitions i ->
  forall height x y z, ranked i "ADD" [x; y; z] height ->
    holds i "ADD" [x; vsucc y; vsucc z].
Proof.
  intros Hmodel height. induction height using lt_wf_ind.
  intros x y z Hrank.
  destruct (add_rank_inversion i x y z height Hmodel Hrank)
    as [[-> [-> Hy]] | [x' [z' [child [-> [-> [Hchild Hlt]]]]]]].
  - apply add_zero; [exact Hmodel|]. now apply n_succ.
  - apply add_succ; [exact Hmodel|]. exact (H child Hlt x' y z' Hchild).
Qed.

Lemma add_shift_right i x y z :
  models fo_definitions i -> holds i "ADD" [x; y; z] ->
  holds i "ADD" [x; vsucc y; vsucc z].
Proof.
  intros Hmodel [height Hrank].
  exact (add_shift_right_by_rank i Hmodel height x y z Hrank).
Qed.

Lemma n2_for_n_rank_sum i :
  models fo_definitions i ->
  forall total hx hy x y,
    hx + hy = total ->
    ranked i "N" [x] hx -> ranked i "N" [y] hy ->
    holds i "N2" [x; y].
Proof.
  intros Hmodel total. induction total using lt_wf_ind.
  intros hx hy x y Hsum Hx Hy.
  destruct (n_rank_inversion i x hx Hmodel Hx)
    as [-> | [x' [child [-> [Hx' Hlt]]]]].
  - apply n2_zero; [exact Hmodel|]. now apply ranked_holds with (height := hy).
  - apply n2_succ; [exact Hmodel|].
    eapply H with (m := hy + child) (hx := hy) (hy := child);
      try reflexivity; try exact Hy; try exact Hx'.
    lia.
Qed.

Lemma n2_for_naturals i x y :
  models fo_definitions i -> holds i "N" [x] -> holds i "N" [y] ->
  holds i "N2" [x; y].
Proof.
  intros Hmodel [hx Hx] [hy Hy].
  eapply n2_for_n_rank_sum with (total := hx + hy) (hx := hx) (hy := hy);
    eauto.
Qed.

Lemma max_step_decreases a b :
  Nat.max a b < Nat.max (S a) (S (S b)).
Proof.
  pose proof (Nat.le_max_l a b). pose proof (Nat.le_max_r a b).
  pose proof (Nat.le_max_l (S a) (S (S b))).
  pose proof (Nat.le_max_r (S a) (S (S b))). lia.
Qed.

Lemma max_left_hydra_decreases a :
  Nat.max (S a) a < Nat.max (S (S a)) 0.
Proof. rewrite Nat.max_0_r. apply Nat.max_lub_lt_iff. lia. Qed.

Lemma max_right_hydra_decreases a :
  Nat.max (S a) a < Nat.max 0 (S (S a)).
Proof. rewrite Nat.max_0_l. apply Nat.max_lub_lt_iff. lia. Qed.

Lemma h_for_natural_depth i :
  models fo_definitions i ->
  forall depth x y,
    Nat.max (value_depth x) (value_depth y) = depth ->
    holds i "N" [x] -> holds i "N" [y] -> holds i "H" [x; y].
Proof.
  intros Hmodel depth. induction depth using lt_wf_ind.
  intros x y Hdepth [hx Hx] [hy Hy].
  destruct (n_rank_inversion i y hy Hmodel Hy)
    as [-> | [y' [hy' [-> [Hy' Hylt]]]]].
  - destruct (n_rank_inversion i x hx Hmodel Hx)
      as [-> | [x' [hx' [-> [Hx' Hxlt]]]]].
    + apply h_00. exact Hmodel.
    + destruct (n_rank_inversion i x' hx' Hmodel Hx')
        as [-> | [x'' [hx'' [-> [Hx'' Hxlt']]]]].
      * apply h_10. exact Hmodel.
      * apply h_end_step; [exact Hmodel|].
        eapply H with
          (m := Nat.max (value_depth (vsucc x'')) (value_depth x''));
          try reflexivity.
        -- cbn [vzero] in Hdepth.
           repeat rewrite value_depth_succ in Hdepth.
           rewrite Nat.max_0_r in Hdepth. subst depth.
           repeat rewrite value_depth_succ.
           apply Nat.max_lub_lt_iff. lia.
        -- apply ranked_holds with (height := hx'). exact Hx'.
        -- apply ranked_holds with (height := hx''). exact Hx''.
  - destruct (n_rank_inversion i y' hy' Hmodel Hy')
      as [-> | [y'' [hy'' [-> [Hy'' Hylt']]]]].
    + apply h_x1. exact Hmodel.
    + destruct (n_rank_inversion i x hx Hmodel Hx)
        as [-> | [x' [hx' [-> [Hx' Hxlt]]]]].
      * apply h_zero_step; [exact Hmodel|].
        eapply H with
          (m := Nat.max (value_depth (vsucc y'')) (value_depth y''));
          try reflexivity.
        -- cbn [vzero] in Hdepth.
           repeat rewrite value_depth_succ in Hdepth.
           rewrite Nat.max_0_l in Hdepth. subst depth.
           repeat rewrite value_depth_succ.
           apply Nat.max_lub_lt_iff. lia.
        -- apply ranked_holds with (height := hy'). exact Hy'.
        -- apply ranked_holds with (height := hy''). exact Hy''.
      * apply h_step; [exact Hmodel|].
        eapply H with
          (m := Nat.max (value_depth x') (value_depth y''));
          try reflexivity.
        -- repeat rewrite value_depth_succ in Hdepth. subst depth.
           repeat rewrite value_depth_succ.
           apply max_step_decreases.
        -- apply ranked_holds with (height := hx'). exact Hx'.
        -- apply ranked_holds with (height := hy''). exact Hy''.
Qed.

Lemma h_for_naturals i x y :
  models fo_definitions i -> holds i "N" [x] -> holds i "N" [y] ->
  holds i "H" [x; y].
Proof.
  intros Hmodel Hx Hy.
  eapply h_for_natural_depth with
    (depth := Nat.max (value_depth x) (value_depth y)); eauto.
Qed.
