From Stdlib Require Import List Bool Arith Lia String.

From CyclistRocq.LTL Require Import Syntax.

Import ListNotations.
Open Scope string_scope.

(* Shorthand constructor for an [occurrence] with an arbitrary optional tag.
   [occ (Some 3) f] is formula [f] tagged 3; [occ None f] is untagged.
   Unlike [tagged]/[untagged] in Syntax.v, the tag is a parameter, so the
   rules below can be stated for "any tag" generically. *)
Definition occ (tag : option nat) (f : formula) : occurrence :=
  {| occurrence_tag := tag; occurrence_formula := f |}.

(* Inversion for [denote] on a cons: a judgment [o :: gamma] holds at [w]
   iff the head formula holds, or the rest of the judgment holds.
   (Disjunctive semantics.)  Used to peel off the head in every rule proof. *)
Lemma denote_cons_inv o gamma w :
  denote (o :: gamma) w ->
  eval o.(occurrence_formula) (fst w) (snd w) \/ denote gamma w.
Proof.
  intros [x [[Hx | Hx] Heval]].
  - left. subst x. exact Heval.
  - right. exists x. auto.
Qed.

(* Introduction (head): if the head formula holds at [w], so does the
   whole judgment.  Converse direction of [denote_cons_inv], left case. *)
Lemma denote_cons_intro_left o gamma w :
  eval o.(occurrence_formula) (fst w) (snd w) -> denote (o :: gamma) w.
Proof. intro H. exists o. split; [left; reflexivity|exact H]. Qed.

(* Introduction (tail): if the tail [gamma] holds at [w], then so does
   [o :: gamma] -- adding a disjunct never falsifies a disjunction. *)
Lemma denote_cons_intro_right o gamma w :
  denote gamma w -> denote (o :: gamma) w.
Proof.
  intros [x [Hin Heval]]. exists x. split; [right; exact Hin|exact Heval].
Qed.

(* Axiom rule (identity):   ------------------  Id
                            p, ¬p, Γ
   For any atom [p] the sequent [p, ¬p, Γ] is valid: at any time, the
   trace either makes [p] true (first disjunct) or false (second).
   It has no premises, so it closes a branch of a proof. *)
Theorem axiom_rule (gamma : judgment) (p : string) :
  Cyclic.Valid (untagged (Atom p) :: untagged (NegAtom p) :: gamma).
Proof.
  intros [tr now].
  destruct (tr now p) eqn:Hp.
  - exists (untagged (Atom p)). split; [now left|exact Hp].
  - exists (untagged (NegAtom p)). split; [right; now left|exact Hp].
Qed.

(* Disjunction rule:    a, b, Γ
                       ---------- Disj
                        a ∨ b, Γ
   Soundness of the invertible ∨ rule: if the sequent with both disjuncts
   split out is valid, then the sequent with [a ∨ b] is valid.
   [ta] and [tb] are the tags carried over to the premise formulae. *)
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

(* Conjunction rule:  a, Γ     b, Γ
                     --------------- Conj
                          a ∧ b, Γ
   Two premises, one per conjunct; the context Γ is shared.  If both
   premises are valid then at every world either Γ holds or both a and b
   hold, hence a ∧ b holds. *)
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

(* Eventually rule (unfolding ◇):   a, ◯◇a, Γ
                                  ------------- Eventually
                                     ◇a, Γ
   Uses the fixpoint law  ◇a ≡ a ∨ ◯◇a : either [a] holds now (k = 0),
   or [◇a] holds from the next step (witness k+1).  The premise contains
   [◯◇a], which is where a cyclic proof can later backlink. *)
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

(* Always rule (unfolding □):   a, Γ      ◯□a, Γ
                              ------------------- Always
                                    □a, Γ
   Uses the fixpoint law  □a ≡ a ∧ ◯□a.  The conclusion's [□a] carries
   tag [t] and the premise's [◯□a] carries tag [t'], so that progress of
   this formula can be followed along a path (see [occurrence_rank]). *)
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

(* Put a [Next] around an occurrence's formula, keeping its tag.
   Mapped over a whole judgment by [next_rule]. *)
Definition wrap_next (o : occurrence) : occurrence :=
  {| occurrence_tag := o.(occurrence_tag);
     occurrence_formula := Next o.(occurrence_formula) |}.

(* Next rule:        Γ
                 ------------ Next     (all of Γ's formulae are under ◯,
                  ◯Γ, Δ                 Δ is discarded/weakened away)
   If [inner] is valid at every world, it is valid at the shifted world
   (tr, now+1); therefore [◯inner] is valid at (tr, now).  [discarded]
   lets the rule also absorb extra formulae (a built-in weakening). *)
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

(* Weakening: if [small] is valid, then adding any extra disjuncts
   [extra] keeps it valid.  Sound because judgments are disjunctions. *)
Theorem weakening_rule (small extra : judgment) :
  Cyclic.Valid small -> Cyclic.Valid (small ++ extra)%list.
Proof.
  intros Hvalid w. destruct (Hvalid w) as [o [Hin Heval]].
  exists o. split; [apply in_or_app; now left|exact Heval].
Qed.

(* Exact backlink: a judgment can be justified by an identical,
   already-seen ancestor judgment.  Semantically trivial (A -> A); the real
   content (that the cycle makes progress) is checked by the framework
   via the edge data in [exact_backlink_instance]. *)
Theorem exact_backlink_rule (j : judgment) :
  Cyclic.Valid j -> Cyclic.Valid j.
Proof. auto. Qed.

(* Packages [axiom_rule] as a [Cyclic.axiom_instance]: the named record
   (name, conclusion, soundness proof) the generic framework consumes
   when a proof-tree leaf is an axiom. *)
Definition atom_axiom_instance (gamma : judgment) (p : string)
  : Cyclic.axiom_instance :=
  {| Cyclic.axiom_name := "Axiom";
     Cyclic.axiom_conclusion :=
       untagged (Atom p) :: untagged (NegAtom p) :: gamma;
     Cyclic.axiom_theorem := axiom_rule gamma p |}.

(* Every pair in [identity_pairs ts] (the list [(t,t)] for each tag t)
   has equal components.  Helper for the backlink soundness proof. *)
Lemma in_identity_pairs_eq a b ts :
  In (a, b) (Cyclic.identity_pairs ts) -> a = b.
Proof.
  unfold Cyclic.identity_pairs.
  intro H. apply in_map_iff in H.
  destruct H as [t [Heq _]]. inversion Heq. reflexivity.
Qed.

(* The single premise of a backlink: the same judgment [j] again, with a
   trace edge mapping every tag of [j] to itself ([identity_pairs]) and
   an empty progress list (no tag is claimed to strictly decrease). *)
Definition exact_backlink_premise (j : judgment) : Cyclic.premise :=
  {| Cyclic.premise_judgment := j;
     Cyclic.premise_edge :=
       {| Cyclic.edge_valid := Cyclic.identity_pairs (judgment_tags j);
          Cyclic.edge_progress := [] |} |}.

(* Packages a backlink as a [Cyclic.rule_instance] with premise
   [j] itself.  The two proof obligations (built in tactic mode) show:
   (1) validity of the premise gives validity of the conclusion, and
   (2) any countermodel to the conclusion is a countermodel to the premise,
       with ranks related by the identity edge (so the framework's
       infinite-descent argument is respected). *)
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
