From Stdlib Require Import List Bool Arith Lia String.

From CyclistRocq.LTL Require Import Syntax.

Import ListNotations.
Open Scope string_scope.

Definition occ (tag : option nat) (f : formula) : occurrence :=
  {| occurrence_tag := tag; occurrence_formula := f |}.

Lemma denote_cons_inv o gamma w :
  denote (o :: gamma) w ->
  eval o.(occurrence_formula) (fst w) (snd w) \/ denote gamma w.
Proof.
  intros [x [[Hx | Hx] Heval]].
  - left. subst x. exact Heval.
  - right. exists x. auto.
Qed.

Lemma denote_cons_intro_left o gamma w :
  eval o.(occurrence_formula) (fst w) (snd w) -> denote (o :: gamma) w.
Proof. intro H. exists o. split; [left; reflexivity|exact H]. Qed.

Lemma denote_cons_intro_right o gamma w :
  denote gamma w -> denote (o :: gamma) w.
Proof.
  intros [x [Hin Heval]]. exists x. split; [right; exact Hin|exact Heval].
Qed.

Theorem axiom_rule (gamma : judgment) (p : string) :
  Cyclic.Valid (untagged (Atom p) :: untagged (NegAtom p) :: gamma).
Proof.
  intros [tr now].
  destruct (tr now p) eqn:Hp.
  - exists (untagged (Atom p)). split; [now left|exact Hp].
  - exists (untagged (NegAtom p)). split; [right; now left|exact Hp].
Qed.

Theorem disjunction_rule
    (gamma : judgment) (ta tb : option nat) (a b : formula) :
  Cyclic.Valid (occ ta a :: occ tb b :: gamma) ->
  Cyclic.Valid (untagged (Disj a b) :: gamma).
Proof.
  intros Hvalid w.
  specialize (Hvalid w).
  apply denote_cons_inv in Hvalid as [Ha | Hrest].
  - apply denote_cons_intro_left. now left.
  - apply denote_cons_inv in Hrest as [Hb | Hgamma].
    + apply denote_cons_intro_left. now right.
    + apply denote_cons_intro_right. exact Hgamma.
Qed.

Theorem conjunction_rule
    (gamma : judgment) (ta tb : option nat) (a b : formula) :
  Cyclic.Valid (occ ta a :: gamma) ->
  Cyclic.Valid (occ tb b :: gamma) ->
  Cyclic.Valid (untagged (Conj a b) :: gamma).
Proof.
  intros Hleft Hright w.
  specialize (Hleft w). specialize (Hright w).
  apply denote_cons_inv in Hleft as [Ha | Hgamma].
  - apply denote_cons_inv in Hright as [Hb | Hgamma].
    + apply denote_cons_intro_left. now split.
    + apply denote_cons_intro_right. exact Hgamma.
  - apply denote_cons_intro_right. exact Hgamma.
Qed.

Theorem eventually_rule
    (gamma : judgment) (ta : option nat) (a : formula) :
  Cyclic.Valid
    (occ ta a :: untagged (Next (Eventually a)) :: gamma) ->
  Cyclic.Valid (untagged (Eventually a) :: gamma).
Proof.
  intros Hvalid [tr now].
  specialize (Hvalid (tr, now)).
  apply denote_cons_inv in Hvalid as [Ha | Hrest].
  - apply denote_cons_intro_left. exists 0. now rewrite Nat.add_0_r.
  - apply denote_cons_inv in Hrest as [Hnext | Hgamma].
    + apply denote_cons_intro_left.
      cbn in Hnext |- *. destruct Hnext as [k Hk]. exists (S k).
      replace (now + S k) with (S now + k) by lia. exact Hk.
    + apply denote_cons_intro_right. exact Hgamma.
Qed.

Theorem always_rule
    (gamma : judgment) (ta : option nat) (t t' : nat) (a : formula) :
  Cyclic.Valid (occ ta a :: gamma) ->
  Cyclic.Valid (tagged t' (Next (Always a)) :: gamma) ->
  Cyclic.Valid (tagged t (Always a) :: gamma).
Proof.
  intros Hleft Hright [tr now].
  specialize (Hleft (tr, now)). specialize (Hright (tr, now)).
  apply denote_cons_inv in Hleft as [Ha | Hgamma].
  - apply denote_cons_inv in Hright as [Hnext | Hgamma].
    + apply denote_cons_intro_left. cbn in Ha, Hnext |- *.
      intro k. destruct k as [|k].
      * now rewrite Nat.add_0_r.
      * replace (now + S k) with (S now + k) by lia. apply Hnext.
    + apply denote_cons_intro_right. exact Hgamma.
  - apply denote_cons_intro_right. exact Hgamma.
Qed.

Definition wrap_next (o : occurrence) : occurrence :=
  {| occurrence_tag := o.(occurrence_tag);
     occurrence_formula := Next o.(occurrence_formula) |}.

Theorem next_rule (inner discarded : judgment) :
  Cyclic.Valid inner ->
  Cyclic.Valid (map wrap_next inner ++ discarded)%list.
Proof.
  intros Hvalid [tr now].
  specialize (Hvalid (tr, S now)).
  destruct Hvalid as [o [Hin Heval]].
  exists (wrap_next o). split.
  - apply in_or_app. left. apply in_map. exact Hin.
  - exact Heval.
Qed.

Theorem weakening_rule (small extra : judgment) :
  Cyclic.Valid small -> Cyclic.Valid (small ++ extra)%list.
Proof.
  intros Hvalid w. destruct (Hvalid w) as [o [Hin Heval]].
  exists o. split; [apply in_or_app; now left|exact Heval].
Qed.

Theorem exact_backlink_rule (j : judgment) :
  Cyclic.Valid j -> Cyclic.Valid j.
Proof. auto. Qed.

Definition atom_axiom_instance (gamma : judgment) (p : string)
  : Cyclic.axiom_instance :=
  {| Cyclic.axiom_name := "Axiom";
     Cyclic.axiom_conclusion :=
       untagged (Atom p) :: untagged (NegAtom p) :: gamma;
     Cyclic.axiom_theorem := axiom_rule gamma p |}.

Lemma in_identity_pairs_eq a b ts :
  In (a, b) (Cyclic.identity_pairs ts) -> a = b.
Proof.
  unfold Cyclic.identity_pairs.
  intro H. apply in_map_iff in H.
  destruct H as [t [Heq _]]. inversion Heq. reflexivity.
Qed.

Definition exact_backlink_premise (j : judgment) : Cyclic.premise :=
  {| Cyclic.premise_judgment := j;
     Cyclic.premise_edge :=
       {| Cyclic.edge_valid := Cyclic.identity_pairs (judgment_tags j);
          Cyclic.edge_progress := [] |} |}.

Definition exact_backlink_instance (j : judgment) : Cyclic.rule_instance.
Proof.
  refine
    {| Cyclic.rule_name := "Backlink";
       Cyclic.rule_conclusion := j;
       Cyclic.rule_premises := [exact_backlink_premise j] |}.
  - intros Hprem. apply Hprem with (p := exact_backlink_premise j).
    now left.
  - intros w Hfalse.
    exists 0. exists (exact_backlink_premise j). exists w.
    split; [reflexivity|]. split; [exact Hfalse|].
    split.
    + intros a b Hin.
      apply in_identity_pairs_eq in Hin. subst b. apply Nat.le_refl.
    + intros a b Hin. inversion Hin.
Defined.
