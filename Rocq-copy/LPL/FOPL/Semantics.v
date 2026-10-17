(** * Meaning of first-order labelled process logic

    Suggested reading order: the generic overlap relation; models, states and
    labels; the mutual formula/program interpretation; FOL substitution and
    sequent denotation; semantic rule equations; finally state-switch
    freshness. Progress.v builds ranks on top of these definitions.

    Two operations must stay distinct throughout: labels concatenate by list
    append, while executable program traces overlap a shared endpoint. All
    formulas are false on an empty trace; assertion admissibility makes the
    intended logical laws available on the nonempty traces used by rules. *)
From Stdlib Require Import List Bool Arith Lia Classical_Prop Classical_Pred_Type.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ClassicalDescription.
From CyclistRocq.LPL.FOPL Require Import Signature Syntax.
From CyclistRocq.LPL Require Import Semantics.
Import ListNotations.

Module MakeSemantics (S : SIGNATURE).
Module Export Syn := MakeSyntax S.
Module Shared := CyclistRocq.LPL.Semantics.MakeSemantics Syn.Language Syn.Shared.
Definition overlap_list := @Shared.overlap_list.
Definition overlap_list_append := @Shared.overlap_list_append.
Definition last_append_nonempty := @Shared.last_append_nonempty.
Definition overlap_list_last := @Shared.overlap_list_last.
Definition map_involutive := @Shared.map_involutive.
Definition overlap_list_map := @Shared.overlap_list_map.
Definition overlap_list_head := @Shared.overlap_list_head.
Definition overlap_list_singleton := @Shared.overlap_list_singleton.
Definition overlap_list_snoc := @Shared.overlap_list_snoc.
Definition overlap_list_cons := @Shared.overlap_list_cons.
Definition overlap_list_assoc := @Shared.overlap_list_assoc.
Arguments overlap_list {A}.
Arguments overlap_list_append {A}.
Arguments last_append_nonempty {A}.
Arguments overlap_list_last {A}.
Arguments map_involutive {A}.
Arguments overlap_list_head {A}.
Arguments overlap_list_singleton {A}.
Arguments overlap_list_snoc {A}.
Arguments overlap_list_cons {A}.
Arguments overlap_list_assoc {A}.
Arguments overlap_list_map {A B}.
Record model : Type := Model {
  domain : Type;
  domain_inhabitant : domain;
  interpret_function : S.function_symbol -> list domain -> domain;
  interpret_predicate : S.predicate_symbol -> list domain -> Prop
}.

Section Interpretation.
Context (M : model).
(** A state assigns a model value to each program variable. The surrounding
    section generalizes the definitions and proofs over [M]; integer-specific
    reasoning only appears in the benchmarks. *)
Definition state := nat -> domain M.
Definition trace := list state.

Definition write (s : state) (x : nat) (value : domain M) : state :=
  fun y => if Nat.eqb x y then value else s y.

Lemma write_same s x v : write s x v x = v.
Proof. unfold write; now rewrite Nat.eqb_refl. Qed.
Lemma write_other s x y v : x <> y -> write s x v y = s y.
Proof. intro H; unfold write; apply Nat.eqb_neq in H; now rewrite H. Qed.

Fixpoint eval_term (s : state) (t : term) : domain M :=
  match t with
  | Var x => s x
  | Fun f ts => interpret_function M f (map (eval_term s) ts)
  end.

(** States are functions, so equalities between whole updated states use
    functional extensionality. These update laws also handle the shadowing
    and commuting writes encountered under named quantifiers. *)
Lemma write_shadow s x a b : write (write s x a) x b = write s x b.
Proof. apply functional_extensionality; intro y; unfold write; destruct (Nat.eqb x y); reflexivity. Qed.
Lemma write_commute s x y a b : x <> y ->
  write (write s x a) y b = write (write s y b) x a.
Proof.
  intro Hne; apply functional_extensionality; intro z; unfold write.
  destruct (Nat.eqb x z) eqn:Hx, (Nat.eqb y z) eqn:Hy; try reflexivity.
  apply Nat.eqb_eq in Hx, Hy; congruence.
Qed.
Lemma write_current s x : write s x (s x) = s.
Proof.
  apply functional_extensionality; intro y; unfold write.
  destruct (Nat.eqb x y) eqn:H; [apply Nat.eqb_eq in H; subst|]; reflexivity.
Qed.

(** The basic substitution equation: replacing a variable syntactically is
    equivalent to first evaluating its replacement in the original state,
    then changing that variable's semantic value. *)
Lemma eval_term_subst t : forall s x replacement,
  eval_term s (subst_term x replacement t) =
  eval_term (write s x (eval_term s replacement)) t.
Proof.
  revert t; fix IH 1; intro t; destruct t as [y|f ts]; intros s x replacement; cbn [subst_term eval_term].
  - unfold write; destruct (Nat.eqb x y); reflexivity.
  - f_equal. rewrite map_map. induction ts as [|a ts IHts]; cbn; [reflexivity|].
    rewrite (IH a s x replacement), IHts; reflexivity.
Qed.

(** Coincidence only needs agreement on variables actually used by a term.
    The nested induction on argument lists supplies the recursive hypotheses
    that ordinary induction on the nested [term] datatype does not provide. *)
Lemma eval_term_coincidence t : forall s s',
  (forall x, In x (term_vars t) -> s x = s' x) -> eval_term s t = eval_term s' t.
Proof.
  revert t; fix IH 1; intro t; destruct t as [y|f ts]; intros s s' H; cbn [eval_term].
  - apply H; cbn; auto.
  - f_equal. cbn [term_vars] in H. revert H.
    induction ts as [|a ts IHts]; intro H; cbn; [reflexivity|].
    f_equal.
    + apply (IH a s s'). intros x Hx; apply H; apply in_app_iff; auto.
    + apply IHts. intros x Hx; apply H; apply in_app_iff; auto.
Qed.

Lemma eval_term_fresh t s x value : ~ In x (term_vars t) ->
  eval_term (write s x value) t = eval_term s t.
Proof.
  intro Hfresh; apply eval_term_coincidence. intros y Hy; apply write_other; congruence.
Qed.

(** The first-order model is interpreted once into the common frame.
    These are concrete proofs of the abstract frame laws, not new axioms. *)
Fixpoint eval_world_term (rho : nat -> state) (u : update) : state :=
  match u with
  | Base x => rho x
  | AssignUpdate x t previous =>
      let s := eval_world_term rho previous in write s x (eval_term s t)
  end.
Definition general_model : Shared.model.
Proof.
  refine {| Shared.carrier := state;
    Shared.carrier_inhabitant := fun _ => domain_inhabitant M;
    Shared.interpret_atom := fun a s => match a with
      | Predicate p ts => interpret_predicate M p (map (eval_term s) ts)
      | Equality a b => eval_term s a = eval_term s b end;
    Shared.interpret_extension := fun x child tr => forall value, child (map (fun s => write s x value) tr);
    Shared.interpret_action := fun a s next => match a with Assignment x t => next = write s x (eval_term s t) end;
    Shared.interpret_atomic_trace := fun a tr => match a with Assignment x t => exists s, tr = [s;write s x (eval_term s t)] end;
    Shared.interpret_world_term := eval_world_term;
    Shared.interpret_relation := fun symbol _ => match symbol with end |}.
  - intros [x t] tr; split.
    + intros [s ->]; exists s, (write s x (eval_term s t)); auto.
    + intros [s [next [-> ->]]]; exists s; reflexivity.
  - intros rho x; reflexivity.
  - intros rho rho' u; induction u; intro H; cbn [eval_world_term].
    + apply H; now left.
    + rewrite IHu; [reflexivity|exact H].
  - intros rho x replacement u; unfold Language.subst_world; induction u; cbn [eval_world_term subst_world_update].
    + destruct (Nat.eqb x world_variable); reflexivity.
    + now rewrite IHu.
Defined.
Definition world := @Shared.world general_model.
Definition World := @Shared.World general_model.
Definition world_mapping := @Shared.world_mapping general_model.
Definition trace_mapping := @Shared.trace_mapping general_model.
Definition trace_mapping_nonempty := @Shared.trace_mapping_nonempty general_model.
Definition eval_update := @Shared.eval_update general_model.
Definition eval_label := @Shared.eval_label general_model.
Definition label_eval := @Shared.label_eval general_model.
Definition label_admissible := @Shared.label_admissible general_model.
Definition label_eval_total := @Shared.label_eval_total general_model.
Definition label_eval_unique := @Shared.label_eval_unique general_model.
Definition label_left_unit := @Shared.label_left_unit general_model.
Definition label_right_unit := @Shared.label_right_unit general_model.
Definition label_join_length := @Shared.label_join_length general_model.
Definition label_prefix_length := @Shared.label_prefix_length general_model.
Definition label_nonemptyb_spec := @Shared.label_nonemptyb_spec general_model.
Definition replace_world := @Shared.replace_world general_model.
Definition replace_trace := @Shared.replace_trace general_model.
Definition eval_world_substitution := @Shared.eval_world_substitution general_model.
Definition eval_world_label_substitution := @Shared.eval_world_label_substitution general_model.
Definition eval_trace_label_substitution := @Shared.eval_trace_label_substitution general_model.
Definition eval_rotate_label := @Shared.eval_rotate_label general_model.
Definition eval_unit_label := @Shared.eval_unit_label general_model.
Definition overlap := @Shared.overlap general_model.
Definition compose := @Shared.compose general_model.
Definition finite_power := @Shared.finite_power general_model.
Definition proper_suffix := @Shared.proper_suffix general_model.
Definition formula_holds := @Shared.formula_holds general_model.
Definition program_holds := @Shared.program_holds general_model.
Definition labelled_holds := @Shared.labelled_holds general_model.
Definition relation_admissible := @Shared.relation_admissible general_model.
Definition relation_holds := @Shared.relation_holds general_model.
Definition relations_hold := @Shared.relations_hold general_model.
Definition admissible := @Shared.admissible general_model.
Definition left_holds := @Shared.left_holds general_model.
Definition right_holds := @Shared.right_holds general_model.
Definition denote := @Shared.denote general_model.
Definition Valid := @Shared.Valid general_model.
Definition relation_mapping := @Shared.relation_mapping general_model.
Definition relation_admissible_mapping := @Shared.relation_admissible_mapping general_model.
Definition labelled_mapping := @Shared.labelled_mapping general_model.
Definition denote_mapping := @Shared.denote_mapping general_model.
Definition denote_tag_renaming := @Shared.denote_tag_renaming general_model.
Definition denote_erase_tags := @Shared.denote_erase_tags general_model.
Definition backlink_eqb_denote := @Shared.backlink_eqb_denote general_model.
Definition valid_admissible := @Shared.valid_admissible general_model.
Definition false_relations := @Shared.false_relations general_model.
Definition false_sequent := @Shared.false_sequent general_model.
Definition judgment_wfb_admissible := @Shared.judgment_wfb_admissible general_model.
Definition overlap_nonempty := @Shared.overlap_nonempty general_model.
Definition overlap_length := @Shared.overlap_length general_model.
Definition finite_power_length := @Shared.finite_power_length general_model.
Definition program_length := @Shared.program_length general_model.
Definition overlap_snoc := @Shared.overlap_snoc general_model.
Definition box_test := @Shared.box_test general_model.
Definition diamond_test := @Shared.diamond_test general_model.
Definition box_sequence := @Shared.box_sequence general_model.
Definition box_choice := @Shared.box_choice general_model.
Definition box_star := @Shared.box_star general_model.
Definition diamond_sequence := @Shared.diamond_sequence general_model.
Definition diamond_choice := @Shared.diamond_choice general_model.
Definition diamond_star := @Shared.diamond_star general_model.
Definition diamond_clause := @Shared.diamond_clause general_model.
Definition nonempty_disj := @Shared.nonempty_disj general_model.
Definition nonempty_impl := @Shared.nonempty_impl general_model.
Definition diamond_dual := @Shared.diamond_dual general_model.
Definition box_test_label := @Shared.box_test_label general_model.
Definition diamond_test_label := @Shared.diamond_test_label general_model.
Definition first_label := @Shared.first_label general_model.
Definition atom_head_label := @Shared.atom_head_label general_model.
Definition proper_suffix_length := @Shared.proper_suffix_length general_model.
Definition proper_suffix_step := @Shared.proper_suffix_step general_model.
Definition proper_suffix_trans := @Shared.proper_suffix_trans general_model.
Definition suffix_clause := @Shared.suffix_clause general_model.
Definition suffix_step := @Shared.suffix_step general_model.
Definition nonempty_neg := @Shared.nonempty_neg general_model.
Definition dual_suffix_dual := @Shared.dual_suffix_dual general_model.
Definition dual_suffix_step := @Shared.dual_suffix_step general_model.
Definition suffix_label := @Shared.suffix_label general_model.
Definition dual_suffix_label := @Shared.dual_suffix_label general_model.
Definition no_singleton_suffix := @Shared.no_singleton_suffix general_model.
Definition suffix_singleton := @Shared.suffix_singleton general_model.
Definition next_singleton := @Shared.next_singleton general_model.
Definition dual_suffix_singleton := @Shared.dual_suffix_singleton general_model.
Fixpoint fol_holds (a : formula) (s : state) : Prop :=
  match a with
  | Truth => True
  | Atom (Predicate p ts) => interpret_predicate M p (map (eval_term s) ts)
  | Atom (Equality a b) => eval_term s a = eval_term s b
  | Neg a => ~ fol_holds a s
  | Conj a b => fol_holds a s /\ fol_holds b s
  | All x a => forall value, fol_holds a (write s x value)
  | _ => False
  end.

Lemma ex_clause x a tr : tr <> [] ->
  (formula_holds (Ex x a) tr <-> exists value,
    formula_holds a (map (fun s => write s x value) tr)).
Proof.
  intro Hne; destruct tr as [|s tail]; [contradiction|].
  change (~ (forall value, formula_holds (Neg a) (map (fun s => write s x value) (s::tail))) <->
    exists value, formula_holds a (map (fun s => write s x value) (s::tail))).
  assert (forall value, formula_holds (Neg a) (map (fun s => write s x value) (s::tail)) <->
    ~ formula_holds a (map (fun s => write s x value) (s::tail))) as Hneg.
  { intro value; apply nonempty_neg; discriminate. }
  setoid_rewrite Hneg; split.
  - intro H; apply not_all_ex_not in H as [value H]; exists value; tauto.
  - intros [value H] Hall; exact (Hall value H).
Qed.

Lemma fol_ex x a s : fol_holds (Ex x a) s <-> exists value, fol_holds a (write s x value).
Proof. cbn [Ex Coextension fol_holds]; split.
  - intro H; apply not_all_ex_not in H as [v H]; exists v; tauto.
  - intros [v H] Hall; exact (Hall v H). Qed.

Lemma fol_fresh a : pureb a = true -> forall s x value,
  ~ In x (formula_vars a) -> (fol_holds a (write s x value) <-> fol_holds a s).
Proof.
  induction a as [|[p args|a b]|a IHa|a1 IHa1 a2 IHa2|x a IHa|a IHa|a1 IHa1 a2 IHa2|p a IHa]; cbn [pureb]; intro Hp; try discriminate;
    intros s u value Hfresh; cbn [fol_holds formula_vars] in *; try tauto.
  - assert (map (eval_term (write s u value)) args = map (eval_term s) args) as Heq.
    { apply map_ext_in; intros t Hin; apply eval_term_fresh.
      intro H; apply Hfresh; apply in_flat_map; exists t; auto. }
    now rewrite Heq.
  - rewrite !eval_term_fresh; try tauto; intros H; apply Hfresh; apply in_app_iff; auto.
  - now rewrite IHa by assumption.
  - apply andb_true_iff in Hp as [Ha Hb].
    rewrite IHa1, IHa2; try assumption; try (intro H; apply Hfresh; apply in_app_iff; auto); tauto.
  - assert (u <> x) as Hux by (intro Heq; subst u; apply Hfresh; now left).
    assert (~ In u (formula_vars a)) as Hbody by (intro Hin; apply Hfresh; now right).
    split; intros H v; specialize (H v).
    + rewrite write_commute in H by exact Hux. apply (proj1 (IHa Hp (write s x v) u value Hbody)); exact H.
    + rewrite write_commute by exact Hux. apply (proj2 (IHa Hp (write s x v) u value Hbody)); exact H.
Qed.

(** Raw substitution is sound under [free_forb]. In the quantifier cases,
    freshness of the binder in [t] keeps the replacement's evaluated value
    fixed while writes are commuted. The public theorem below removes this
    side condition by renaming conflicting binders first. *)
Lemma raw_subst_correct a : pureb a = true -> forall s u t,
  free_forb u t a = true ->
  (fol_holds (raw_subst_fo u t a) s <-> fol_holds a (write s u (eval_term s t))).
Proof.
  induction a as [|[p args|a b]|a IHa|a1 IHa1 a2 IHa2|x a IHa|a IHa|a1 IHa1 a2 IHa2|p a IHa]; cbn [pureb]; intro Hp; try discriminate;
    intros s u t Hfree; cbn [Pred Equal raw_subst_fo free_forb fol_holds] in *; try tauto.
  - rewrite map_map. assert (map (fun a => eval_term s (subst_term u t a)) args =
      map (eval_term (write s u (eval_term s t))) args) as Heq.
    { apply map_ext; intro a; apply eval_term_subst. }
    now rewrite Heq.
  - now rewrite !eval_term_subst.
  - now rewrite IHa by assumption.
  - apply andb_true_iff in Hp as [Ha Hb]; apply andb_true_iff in Hfree as [Hfa Hfb].
    rewrite IHa1, IHa2 by assumption; tauto.
  - destruct (Nat.eqb u x) eqn:Hux.
    + apply Nat.eqb_eq in Hux; subst u. cbn [fol_holds]. setoid_rewrite write_shadow; reflexivity.
    + apply Nat.eqb_neq in Hux; apply andb_true_iff in Hfree as [Hfresh Hfree].
      apply negb_true_iff, occursb_false in Hfresh. cbn [fol_holds].
      split; intros H v; specialize (H v).
      * apply (proj1 (IHa Hp (write s x v) u t Hfree)) in H.
        rewrite eval_term_fresh in H by exact Hfresh.
        rewrite write_commute in H by congruence. exact H.
      * apply (proj2 (IHa Hp (write s x v) u t Hfree)).
        rewrite eval_term_fresh by exact Hfresh. rewrite write_commute by congruence. exact H.
Qed.

(** Alpha-conversion is a semantic theorem about the raw renaming helper.
    Freshness includes nested bound names, so the chosen new binder cannot
    collide with a binder deeper in the body. [alpha_ex] is the existential
    counterpart used by the same substitution algorithm. *)
Lemma alpha_all body y z s : pureb body = true -> ~ In z (formula_vars body) -> z <> y ->
  (fol_holds (All z (raw_subst_fo y (Var z) body)) s <-> fol_holds (All y body) s).
Proof.
  intros Hp Hfresh Hzy; cbn [fol_holds].
  split; intros H v; specialize (H v).
  - apply (proj1 (raw_subst_correct body Hp (write s z v) y (Var z)
      (rename_free_for body y z Hp Hfresh))) in H.
    cbn [eval_term] in H; rewrite write_same, write_commute in H by exact Hzy.
    apply (proj1 (fol_fresh body Hp (write s y v) z v Hfresh)); exact H.
  - apply (proj2 (raw_subst_correct body Hp (write s z v) y (Var z)
      (rename_free_for body y z Hp Hfresh))).
    cbn [eval_term]; rewrite write_same, write_commute by exact Hzy.
    apply (proj2 (fol_fresh body Hp (write s y v) z v Hfresh)); exact H.
Qed.

Lemma alpha_ex body y z s : pureb body = true -> ~ In z (formula_vars body) -> z <> y ->
  (fol_holds (Ex z (raw_subst_fo y (Var z) body)) s <-> fol_holds (Ex y body) s).
Proof.
  setoid_rewrite fol_ex.
  intros Hp Hfresh Hzy; cbn [fol_holds].
  split; intros [v H]; exists v.
  - apply (proj1 (raw_subst_correct body Hp (write s z v) y (Var z)
      (rename_free_for body y z Hp Hfresh))) in H.
    cbn [eval_term] in H; rewrite write_same, write_commute in H by exact Hzy.
    apply (proj1 (fol_fresh body Hp (write s y v) z v Hfresh)); exact H.
  - apply (proj2 (raw_subst_correct body Hp (write s z v) y (Var z)
      (rename_free_for body y z Hp Hfresh))).
    cbn [eval_term]; rewrite write_same, write_commute by exact Hzy.
    apply (proj2 (fol_fresh body Hp (write s y v) z v Hfresh)); exact H.
Qed.

(** Lift a body substitution equation through a nonconflicting binder.
    Factoring out this write-commutation argument keeps the fuel proof's
    capture and no-capture branches focused on their different bodies. *)
Lemma all_subst_congruence body result y u t : y <> u -> ~ In y (term_vars t) ->
  (forall s, fol_holds result s <-> fol_holds body (write s u (eval_term s t))) -> forall s,
  (fol_holds (All y result) s <-> fol_holds (All y body) (write s u (eval_term s t))).
Proof.
  intros Hy Hfresh IH s; cbn [fol_holds].
  split; intros H v; specialize (H v).
  - apply (proj1 (IH _)) in H. rewrite eval_term_fresh in H by exact Hfresh.
    rewrite write_commute in H by exact Hy; exact H.
  - apply (proj2 (IH _)); rewrite eval_term_fresh by exact Hfresh.
    rewrite write_commute by exact Hy; exact H.
Qed.

Lemma ex_subst_congruence body result y u t : y <> u -> ~ In y (term_vars t) ->
  (forall s, fol_holds result s <-> fol_holds body (write s u (eval_term s t))) -> forall s,
  (fol_holds (Ex y result) s <-> fol_holds (Ex y body) (write s u (eval_term s t))).
Proof.
  setoid_rewrite fol_ex.
  intros Hy Hfresh IH s; cbn [fol_holds].
  split; intros [v H]; exists v.
  - apply (proj1 (IH _)) in H. rewrite eval_term_fresh in H by exact Hfresh.
    rewrite write_commute in H by exact Hy; exact H.
  - apply (proj2 (IH _)); rewrite eval_term_fresh by exact Hfresh.
    rewrite write_commute by exact Hy; exact H.
Qed.

(** Induct on fuel rather than the original body: after alpha-renaming, the
    recursive argument is newly constructed syntax. [raw_subst_size] proves
    that it still fits the smaller fuel bound. At each binder, first handle
    shadowing, then separate capture from direct descent. *)
Lemma subst_fo_fuel_correct fuel : forall a, pureb a = true -> fol_size a <= fuel -> forall s u t,
  (fol_holds (subst_fo_fuel fuel u t a) s <-> fol_holds a (write s u (eval_term s t))).
Proof.
  induction fuel as [|fuel IH]; intros a Hp Hsize s u t.
  - destruct a as [|[p args|a b]|a|a1 a2|x a|a|a1 a2|p a]; cbn [fol_size] in Hsize; lia.
  - destruct a as [|[p args|a b]|a|a1 a2|x a|a|a1 a2|p a]; cbn [pureb fol_size] in Hp, Hsize; try discriminate;
      cbn [Pred Equal subst_fo_fuel fol_holds]; try tauto.
    + rewrite map_map. assert (map (fun a => eval_term s (subst_term u t a)) args =
        map (eval_term (write s u (eval_term s t))) args) as Heq.
      { apply map_ext; intro a; apply eval_term_subst. } now rewrite Heq.
    + now rewrite !eval_term_subst.
    + rewrite IH by (assumption || lia); tauto.
    + apply andb_true_iff in Hp as [Ha Hb]; rewrite !IH by (assumption || lia); tauto.
    + destruct (Nat.eqb u x) eqn:Hux.
      * apply Nat.eqb_eq in Hux; subst u; cbn [fol_holds]; setoid_rewrite write_shadow; reflexivity.
      * apply Nat.eqb_neq in Hux; destruct (existsb (Nat.eqb x) (term_vars t)) eqn:Hcapture.
        -- set (z := fresh_name (u :: x :: (formula_vars a ++ term_vars t))).
           assert (~ In z (u :: x :: (formula_vars a ++ term_vars t))) as Hz by apply fresh_name_not_in.
           assert (z <> u /\ z <> x /\ ~ In z (formula_vars a) /\ ~ In z (term_vars t)) as [Hzu [Hzx [Hzbody Hzt]]].
           { repeat split; intro H; apply Hz; cbn; try (left; congruence);
             try (right; left; congruence); right; right; apply in_app_iff; auto. }
           change (fol_holds (All z (subst_fo_fuel fuel u t (raw_subst_fo x (Var z) a))) s <-> fol_holds (All x a) (write s u (eval_term s t))).
           transitivity (fol_holds (All z (raw_subst_fo x (Var z) a)) (write s u (eval_term s t))).
           ++ apply all_subst_congruence; try assumption.
              intro state'; apply IH; [apply raw_subst_pure; exact Hp|rewrite raw_subst_size; lia].
           ++ apply alpha_all; assumption.
        -- apply all_subst_congruence; [congruence|now apply occursb_false|].
           intro state'; apply IH; [exact Hp|lia].
Qed.

Lemma subst_fo_correct a s u t : pureb a = true ->
  (fol_holds (subst_fo u t a) s <-> fol_holds a (write s u (eval_term s t))).
Proof. intro Hp; apply subst_fo_fuel_correct; [exact Hp|lia]. Qed.

(** This is the bridge from uniform-value trace quantification to ordinary
    FOL. Pure bodies cannot observe the tail, so writing one value to every
    state has precisely the usual first-state FOL meaning. This restriction
    is essential for the quantifier instantiation rules. *)
Lemma pure_head a : pureb a = true -> forall s tail,
  formula_holds a (s :: tail) <-> fol_holds a s.
Proof.
  induction a as [|[p args|a b]|a IHa|a1 IHa1 a2 IHa2|x a IHa|a IHa|a1 IHa1 a2 IHa2|p a IHa]; cbn [pureb]; intro Hp; try discriminate;
    intros s tail; cbn [formula_holds fol_holds Shared.formula_holds Shared.program_holds general_model general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term]; try tauto.
  - rewrite IHa by exact Hp. tauto.
  - apply andb_true_iff in Hp as [Ha Hb].
    rewrite IHa1 by exact Ha. rewrite IHa2 by exact Hb. tauto.
  - split; intros H v; specialize (IHa Hp (write s x v) (map (fun s => write s x v) tail));
      [apply IHa; apply H | apply IHa; apply H].
Qed.

Lemma pure_singleton a s tail : pureb a = true ->
  (formula_holds a (s :: tail) <-> formula_holds a [s]).
Proof. intro H; rewrite !pure_head by exact H; reflexivity. Qed.

Lemma box_assignment prefix s x t a :
  formula_holds (Box (Assign x t) a) (prefix ++ [s]) <->
  formula_holds a ((prefix ++ [s]) ++ [write s x (eval_term s t)]).
Proof.
  rewrite (Shared.box_atomic general_model prefix s (Assignment x t) a).
  change ((forall next, next = write s x (eval_term s t) -> formula_holds a ((prefix ++ [s]) ++ [next])) <->
    formula_holds a ((prefix ++ [s]) ++ [write s x (eval_term s t)])).
  split; [intro H; apply H; reflexivity|intros H next ->; exact H].
Qed.

Lemma diamond_assignment prefix s x t a :
  formula_holds (Diamond (Assign x t) a) (prefix ++ [s]) <->
  formula_holds a ((prefix ++ [s]) ++ [write s x (eval_term s t)]).
Proof.
  rewrite (Shared.diamond_atomic general_model prefix s (Assignment x t) a).
  change ((exists next, next = write s x (eval_term s t) /\ formula_holds a ((prefix ++ [s]) ++ [next])) <->
    formula_holds a ((prefix ++ [s]) ++ [write s x (eval_term s t)])).
  split; [intros [next [-> H]]; exact H|intro H; eexists; split; [reflexivity|exact H]].
Qed.

Lemma assignment_label w sigma u x t body tag tag' :
  (labelled_holds w (Occ (Join sigma (StateLabel u)) (Box (Assign x t) body) tag) <->
   labelled_holds w (Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tag')).
Proof.
  unfold labelled_holds, Shared.labelled_holds, Shared.labelled_holds, label_admissible, Shared.label_admissible; cbn [occurrence_label occurrence_formula eval_label Shared.eval_label general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term].
  rewrite box_assignment.
  assert (eval_label w sigma ++ [eval_update w u] <> []) by
    (intro H; apply app_eq_nil in H; destruct H; discriminate).
  assert ((eval_label w sigma ++ [eval_update w u]) ++
    [write (eval_update w u) x (eval_term (eval_update w u) t)] <> []) by
    (intro H'; apply app_eq_nil in H'; destruct H'; discriminate).
  tauto.
Qed.

Lemma diamond_assignment_label w sigma u x t body tag tag' :
  (labelled_holds w (Occ (Join sigma (StateLabel u)) (Diamond (Assign x t) body) tag) <->
   labelled_holds w (Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tag')).
Proof.
  unfold labelled_holds, Shared.labelled_holds, Shared.labelled_holds, label_admissible, Shared.label_admissible; cbn [occurrence_label occurrence_formula eval_label Shared.eval_label general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term].
  rewrite diamond_assignment.
  assert (eval_label w sigma ++ [eval_update w u] <> []) by
    (intro H; apply app_eq_nil in H; destruct H; discriminate).
  assert ((eval_label w sigma ++ [eval_update w u]) ++
    [write (eval_update w u) x (eval_term (eval_update w u) t)] <> []) by
    (intro H'; apply app_eq_nil in H'; destruct H'; discriminate).
  tauto.
Qed.

Lemma pure_head_label w u sigma body tag tag' : pureb body = true ->
  (labelled_holds w (Occ (Join (StateLabel u) sigma) body tag) <->
   labelled_holds w (Occ (StateLabel u) body tag')).
Proof.
  intro Hp; unfold labelled_holds, Shared.labelled_holds, Shared.labelled_holds, label_admissible, Shared.label_admissible; cbn [occurrence_label occurrence_formula eval_label Shared.eval_label general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term].
  rewrite (pure_singleton body (eval_update w u) (eval_label w sigma) Hp).
  split; intros [_ H]; split; try discriminate; exact H.
Qed.

Section StateSwitch.
Context (v : nat) (f : domain M -> domain M) (Hf : forall d, f (f d) = d).
Definition switch s := write s v (f (s v)).

Lemma switch_involutive s : switch (switch s) = s.
Proof. unfold switch; rewrite write_same, write_shadow, Hf; apply write_current. Qed.
Lemma switch_write s x d : x <> v -> switch (write s x d) = write (switch s) x d.
Proof.
  intro Hx; unfold switch; rewrite write_other by exact Hx.
  apply write_commute; exact Hx.
Qed.
Lemma switch_term t s : ~ In v (term_vars t) -> eval_term (switch s) t = eval_term s t.
Proof. apply eval_term_fresh. Qed.
Lemma switch_map_involutive tr : map switch (map switch tr) = tr.
Proof. apply map_involutive, switch_involutive. Qed.

(** For an involution, a forward preservation theorem already gives an
    equivalence: apply preservation twice and cancel the two switches. *)
Lemma switch_predicate_iff (Q : trace -> Prop) :
  (forall tr, Q tr -> Q (map switch tr)) -> forall tr, Q (map switch tr) <-> Q tr.
Proof.
  intros H tr; split; [intro HQ; specialize (H _ HQ); now rewrite switch_map_involutive in H|apply H].
Qed.

Lemma switch_compose R T :
  (forall tr, R (map switch tr) <-> R tr) ->
  (forall tr, T (map switch tr) <-> T tr) -> forall tr,
  compose R T (map switch tr) <-> compose R T tr.
Proof.
  intros HR HT; apply switch_predicate_iff; intros tr [a [b [Ha [Hb Ho]]]].
  exists (map switch a), (map switch b); split; [apply HR; exact Ha|].
  split; [apply HT; exact Hb|]. now apply overlap_list_map.
Qed.

Lemma switch_power R : (forall tr, R (map switch tr) <-> R tr) -> forall n tr,
  finite_power R n (map switch tr) <-> finite_power R n tr.
Proof.
  intros HR n; induction n as [|n IH].
  - apply switch_predicate_iff; intros tr [s ->]; exists (switch s); reflexivity.
  - cbn [finite_power Shared.finite_power]; apply switch_compose; assumption.
Qed.

Lemma switch_box p a :
  (forall tr, program_holds p (map switch tr) <-> program_holds p tr) ->
  (forall tr, formula_holds a (map switch tr) <-> formula_holds a tr) -> forall tr,
  formula_holds (Box p a) (map switch tr) <-> formula_holds (Box p a) tr.
Proof.
  intros Hp Ha; apply switch_predicate_iff; intros tr Hbox.
  destruct tr as [|s tail]; [contradiction|]; cbn [map formula_holds Shared.formula_holds Shared.program_holds general_model general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term] in *.
  intros execution result Hprogram Hover.
  pose proof (overlap_list_map switch _ _ _ Hover) as Ho.
  change (overlap_list (map switch (map switch (s :: tail)))
    (map switch execution) (map switch result)) in Ho.
  rewrite switch_map_involutive in Ho.
  apply (proj1 (Ha result)). eapply Hbox; [apply Hp; exact Hprogram|exact Ho].
Qed.

Lemma switch_diamond p a :
  (forall tr, program_holds p (map switch tr) <-> program_holds p tr) ->
  (forall tr, formula_holds a (map switch tr) <-> formula_holds a tr) -> forall tr,
  formula_holds (Diamond p a) (map switch tr) <-> formula_holds (Diamond p a) tr.
Proof.
  intros Hp Ha; apply switch_predicate_iff; intros tr Hdiamond.
  destruct tr as [|s tail]; [contradiction|].
  rewrite diamond_clause in Hdiamond by discriminate.
  rewrite diamond_clause by discriminate.

  destruct Hdiamond as [execution [result [Hprogram [Hover Hbody]]]].
  exists (map switch execution), (map switch result); split; [apply Hp; exact Hprogram|].
  split; [exact (overlap_list_map switch (s :: tail) execution result Hover)|apply Ha; exact Hbody].
Qed.

(** The mutual induction follows every formula and program constructor.
    Freshness excludes assignment targets as well as read variables, so
    writes commute with the switch. Quantifiers likewise have different
    binders. The modal cases use reversible execution transport; suffix
    cases use their one-step equations and induction on finite traces. *)
Lemma switch_semantics :
  (forall a, ~ In v (formula_vars a) -> forall tr,
    formula_holds a (map switch tr) <-> formula_holds a tr) /\
  (forall p, ~ In v (program_vars p) -> forall tr,
    program_holds p (map switch tr) <-> program_holds p tr).
Proof.
  apply formula_program_mutind.
  - intros Hfresh [|s tail]; reflexivity.
  - intros [p args|a b].
    + intros Hfresh [|s tail]; [reflexivity|]. cbn [map formula_holds Shared.formula_holds Shared.program_holds general_model general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term].
      assert (map (eval_term (switch s)) args = map (eval_term s) args) as Heq.
      { apply map_ext_in; intros t Hin; apply switch_term.
        intro H; apply Hfresh; apply in_flat_map; exists t; auto. }
      now rewrite Heq.
    + intros Hfresh [|s tail]; [reflexivity|]. cbn [map formula_holds Shared.formula_holds Shared.program_holds general_model general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term].
      rewrite !switch_term; try (intro H; apply Hfresh; apply in_app_iff; auto); reflexivity.
  - intros a IH Hfresh [|s tail]; [reflexivity|].
    change (~ formula_holds a (map switch (s :: tail)) <-> ~ formula_holds a (s :: tail)).
    now rewrite IH by exact Hfresh.
  - intros a Ha b Hb Hfresh [|s tail]; [reflexivity|].
    change ((formula_holds a (map switch (s :: tail)) /\ formula_holds b (map switch (s :: tail))) <->
      (formula_holds a (s :: tail) /\ formula_holds b (s :: tail))).
    rewrite Ha, Hb; try (intro H; apply Hfresh; apply in_app_iff; auto); tauto.
  - intros x a IH Hfresh tr.
    assert (x <> v) as Hx by (intro H; subst; apply Hfresh; now left).
    assert (~ In v (formula_vars a)) as Ha by (intro H; apply Hfresh; now right).
    destruct tr as [|s tail]; [reflexivity|]. cbn [formula_holds map Shared.formula_holds Shared.program_holds general_model general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term].
    assert (forall d, map (fun s => write s x d) (map switch (s :: tail)) =
      map switch (map (fun s => write s x d) (s :: tail))) as Hmaps.
    { intro d; rewrite !map_map; apply map_ext; intro state'; symmetry; apply switch_write; exact Hx. }
    change ((forall d, formula_holds a (map (fun s => write s x d) (map switch (s :: tail)))) <->
      (forall d, formula_holds a (map (fun s => write s x d) (s :: tail)))).
    split; intros H d; specialize (H d).
    + rewrite Hmaps in H; apply (proj1 (IH Ha _)); exact H.
    + rewrite Hmaps; apply (proj2 (IH Ha _)); exact H.
  - intros a IH Hfresh [|s tail]; [reflexivity|]; change (formula_holds a (map switch [s]) <-> formula_holds a [s]); apply IH; exact Hfresh.
  - intros a Ha b Hb Hfresh tr.
    assert (~ In v (formula_vars a) /\ ~ In v (formula_vars b)) as [Hfa Hfb]
      by (split; intro H; apply Hfresh; apply in_app_iff; auto).
    induction tr as [|s tail IH]; [reflexivity|]. destruct tail as [|t tail].
    + cbn [map]; split; intro H; exfalso; eapply suffix_singleton; exact H.
    + change (formula_holds (Suffix a b) (switch s :: map switch (t :: tail)) <-> formula_holds (Suffix a b) (s :: t :: tail)).
      rewrite !suffix_step by discriminate. rewrite Ha, Hb, IH by assumption; reflexivity.
  - intros p Hp a Ha Hfresh; apply switch_box;
      [apply Hp|apply Ha]; intro H; apply Hfresh; apply in_app_iff; auto.
  - intros [x t] Hfresh. apply switch_predicate_iff; intros tr [s ->].
    assert (x <> v) as Hx by (intro H; subst; apply Hfresh; now left).
    assert (~ In v (term_vars t)) as Ht by (intro H; apply Hfresh; now right).
    cbn [map]. exists (switch s). rewrite switch_write by exact Hx.
    rewrite switch_term by exact Ht; reflexivity.
  - intros a Ha Hfresh; apply switch_predicate_iff; intros tr [s [-> Hguard]].
    exists (switch s); split; [reflexivity|]. apply (proj2 (Ha Hfresh [s;s])); exact Hguard.
  - intros a Ha b Hb Hfresh; apply switch_compose;
      [apply Ha|apply Hb]; intro H; apply Hfresh; apply in_app_iff; auto.
  - intros a Ha b Hb Hfresh tr; cbn [program_holds Shared.formula_holds Shared.program_holds general_model general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term].
    rewrite Ha, Hb; try (intro H; apply Hfresh; apply in_app_iff; auto); reflexivity.
  - intros a Ha Hfresh tr; cbn [program_holds Shared.formula_holds Shared.program_holds general_model general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term].
    setoid_rewrite (switch_power (program_holds a) (Ha Hfresh)); reflexivity.
Qed.

(** Switch every state in both label environments. Mapping a nonempty trace
    preserves nonemptiness, so the environment remains a valid [world]. The
    following lemmas lift the semantic switch through updates, labels and
    whole contexts under the same syntactic freshness condition. *)
Definition switch_world (w : world) : world.
Proof.
  refine (World (fun x => switch (world_mapping w x))
    (fun x => map switch (trace_mapping w x)) _).
  intros x Heq; apply map_eq_nil in Heq; apply (trace_mapping_nonempty w x); exact Heq.
Defined.

Lemma switch_update w u : ~ In v (update_vars u) ->
  eval_update (switch_world w) u = switch (eval_update w u).
Proof.
  induction u; intro Hfresh; cbn [eval_update Shared.eval_update general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term]; [reflexivity|].
  assert (x <> v) as Hx by (intro H; subst; apply Hfresh; now left).
  assert (~ In v (term_vars value)) as Ht by
    (intro H; apply Hfresh; right; apply in_app_iff; auto).
  assert (~ In v (update_vars u)) as Hu by
    (intro H; apply Hfresh; right; apply in_app_iff; auto).
  specialize (IHu Hu).
  change (eval_world_term (world_mapping (switch_world w)) u = switch (eval_world_term (world_mapping w) u)) in IHu.
  unfold world_mapping in IHu.
  rewrite IHu; rewrite switch_term by exact Ht.
  symmetry; apply switch_write; exact Hx.
Qed.

Lemma switch_label w l : ~ In v (label_vars l) ->
  eval_label (switch_world w) l = map switch (eval_label w l).
Proof.
  induction l; intro Hfresh; cbn [eval_label Shared.eval_label general_model eval_world_term Shared.interpret_atom Shared.interpret_extension Shared.interpret_atomic_trace Shared.interpret_world_term]; try reflexivity.
  - now rewrite switch_update by exact Hfresh.
  - rewrite IHl1, IHl2, map_app; try reflexivity;
      intro H; apply Hfresh; apply in_app_iff; auto.
Qed.

Lemma switch_labelled w o : ~ In v (occurrence_vars o) ->
  (labelled_holds (switch_world w) o <-> labelled_holds w o).
Proof.
  intro Hfresh.
  assert (~ In v (label_vars o.(occurrence_label))) as Hl by
    (intro H; apply Hfresh; apply in_app_iff; auto).
  assert (~ In v (formula_vars o.(occurrence_formula))) as Ha by
    (intro H; apply Hfresh; apply in_app_iff; auto).
  unfold labelled_holds, Shared.labelled_holds, Shared.labelled_holds, label_admissible, Shared.label_admissible; rewrite switch_label by exact Hl.
  rewrite (proj1 switch_semantics _ Ha).
  assert (map switch (eval_label w o.(occurrence_label)) <> [] <-> eval_label w o.(occurrence_label) <> []) as Hne.
  { split; intros H Heq; [apply H; now rewrite Heq|apply map_eq_nil in Heq; contradiction]. }
  tauto.
Qed.

Lemma switch_left_context w context :
  (forall o, In o context -> ~ In v (occurrence_vars o)) ->
  (left_holds (switch_world w) context <-> left_holds w context).
Proof.
  intro Hfresh; unfold left_holds, Shared.left_holds; rewrite !Forall_forall.
  split; intros H o Hin.
  - apply (proj1 (switch_labelled w o (Hfresh o Hin))); apply H; exact Hin.
  - apply (proj2 (switch_labelled w o (Hfresh o Hin))); apply H; exact Hin.
Qed.

Lemma switch_right_context w context :
  (forall o, In o context -> ~ In v (occurrence_vars o)) ->
  (right_holds (switch_world w) context <-> right_holds w context).
Proof.
  intro Hfresh; unfold right_holds, Shared.right_holds; split; intros [o [Hin Ho]]; exists o; split; try exact Hin.
  - apply (proj1 (switch_labelled w o (Hfresh o Hin))); exact Ho.
  - apply (proj2 (switch_labelled w o (Hfresh o Hin))); exact Ho.
Qed.

(** The legacy first-order fragment has an empty relational context. *)
Lemma switch_denote w j : relations j = [] -> ~ In v (judgment_vars j) ->
  (denote j (switch_world w) <-> denote j w).
Proof.
  intros Hrel Hfresh.
  assert (forall o, In o (j.(antecedent) ++ j.(succedent)) -> ~ In v (occurrence_vars o)) as Hocc.
  { intros o Hin Hvar; apply Hfresh; apply in_flat_map; exists o; auto. }
  assert (admissible j (switch_world w) <-> admissible j w) as Hadm.
  { unfold admissible, Shared.admissible; rewrite Hrel.
    split; intros [H _]; split; try constructor;
      rewrite Forall_forall in *; intros o Hin;
      specialize (H o Hin); unfold Shared.label_admissible in *;
      rewrite switch_label in * by (intro Hv; apply (Hocc o Hin); apply in_app_iff; auto);
      unfold eval_label in *.
    - intro Heq; apply H; now rewrite Heq.
    - intro Heq; apply map_eq_nil in Heq; contradiction. }
  assert (left_holds (switch_world w) j.(antecedent) <-> left_holds w j.(antecedent)) as Hl.
  { apply switch_left_context; intros o Hin; apply Hocc; apply in_app_iff; auto. }
  assert (right_holds (switch_world w) j.(succedent) <-> right_holds w j.(succedent)) as Hr.
  { apply switch_right_context; intros o Hin; apply Hocc; apply in_app_iff; auto. }
  assert (Shared.relations_hold general_model (switch_world w) []) as R1 by constructor.
  assert (Shared.relations_hold general_model w []) as R2 by constructor.
  unfold denote, Shared.denote; rewrite Hadm, Hl, Hr, Hrel; tauto.
Qed.

End StateSwitch.

(** Exchange two arbitrary model values and fix all other values. Classical
    equality is used internally; the model interface still requires no
    executable equality decision. Swapping also works when the values agree. *)
Definition swap_values (a b d : domain M) : domain M :=
  if excluded_middle_informative (d = a) then b
  else if excluded_middle_informative (d = b) then a else d.

Lemma swap_values_left a b : swap_values a b a = b.
Proof. unfold swap_values; destruct (excluded_middle_informative (a = a)); congruence. Qed.
Lemma swap_values_right a b : swap_values a b b = a.
Proof.
  unfold swap_values; destruct (excluded_middle_informative (b = a)); [congruence|].
  destruct (excluded_middle_informative (b = b)); congruence.
Qed.
Lemma swap_values_involutive a b d : swap_values a b (swap_values a b d) = d.
Proof.
  destruct (excluded_middle_informative (d = a)) as [->|Hda]; [now rewrite swap_values_left, swap_values_right|].
  destruct (excluded_middle_informative (d = b)) as [->|Hdb]; [now rewrite swap_values_right, swap_values_left|].
  assert (swap_values a b d = d) as Hd.
  { unfold swap_values; destruct (excluded_middle_informative (d = a)); [contradiction|].
    destruct (excluded_middle_informative (d = b)); [contradiction|reflexivity]. }
  now rewrite Hd.
Qed.

Lemma fol_write_fresh body s u v value other : pureb body = true -> ~ In v (formula_vars body) ->
  (fol_holds body (write (write s v other) u value) <-> fol_holds body (write s u value)).
Proof.
  intros Hp Hv; destruct (Nat.eq_dec u v) as [->|Huv].
  - now rewrite write_shadow.
  - rewrite write_commute by congruence; apply fol_fresh; assumption.
Qed.

(** If the head's current [v] value is exchanged with [d], evaluating the
    fresh-variable instance in the switched world means evaluating the
    quantified body with [u := d] in the original head state. Label freshness
    is essential: an update mentioning [v] could otherwise overwrite it. *)
Lemma eigen_instance w l u v body d s tail :
  eval_label w l = s :: tail -> ~ In v (label_vars l) ->
  pureb body = true -> ~ In v (formula_vars body) ->
  (formula_holds (subst_fo u (Var v) body)
    (eval_label (switch_world v (swap_values (s v) d) w) l) <->
   fol_holds body (write s u d)).
Proof.
  intros Hlabel Hl Hp Hv.
  rewrite switch_label by exact Hl; rewrite Hlabel.
  change (formula_holds (subst_fo u (Var v) body)
    (switch v (swap_values (s v) d) s :: map (switch v (swap_values (s v) d)) tail) <-> fol_holds body (write s u d)).
  rewrite (pure_head (subst_fo u (Var v) body)) by (apply subst_fo_fuel_pure; exact Hp).
  rewrite subst_fo_correct by exact Hp.
  cbn [eval_term]; unfold switch; rewrite write_same, swap_values_left.
  apply fol_write_fresh; assumption.
Qed.

(** Arbitrary-term instantiation reduces via [pure_head] to the proved FOL
    substitution theorem. It does not assert a substitution law for a modal
    quantifier body or freeze a term's value across a changing program run. *)
Lemma all_instantiation body u t tr : pureb body = true -> tr <> [] ->
  formula_holds (All u body) tr -> formula_holds (subst_fo u t body) tr.
Proof.
  intros Hp Hne; destruct tr as [|s tail]; [contradiction|].
  rewrite (pure_head (All u body)) by exact Hp.
  rewrite (pure_head (subst_fo u t body)) by (apply subst_fo_fuel_pure; exact Hp).
  rewrite subst_fo_correct by exact Hp. cbn [fol_holds]; auto.
Qed.

Lemma ex_instantiation body u t tr : pureb body = true -> tr <> [] ->
  formula_holds (subst_fo u t body) tr -> formula_holds (Ex u body) tr.
Proof.
  intros Hp Hne; destruct tr as [|s tail]; [contradiction|].
  rewrite (pure_head (Ex u body)) by exact Hp.
  rewrite (pure_head (subst_fo u t body)) by (apply subst_fo_fuel_pure; exact Hp).
  rewrite subst_fo_correct by exact Hp. rewrite fol_ex; eauto.
Qed.

(** For a pure observation, [Always] is exactly the observation at every
    visited state. The complex benchmarks use this to turn finite-trace
    safety induction into an object-language temporal validity theorem. *)
Lemma always_pure_forall a tr : pureb a = true -> tr <> [] ->
  (formula_holds (Always a) tr <-> Forall (fun s => formula_holds a [s]) tr).
Proof.
  intros Hp; induction tr as [|s tail IH]; intro Hne; [contradiction|].
  destruct tail as [|t tail].
  - unfold Always, Eventually; rewrite !nonempty_neg, nonempty_disj by discriminate.
    change (~ (~ formula_holds a [s] \/ formula_holds (Suffix Truth (Neg a)) [s]) <-> Forall (fun s => formula_holds a [s]) [s]).
    rewrite Forall_cons_iff. pose proof (suffix_singleton Truth (Neg a) s) as Hsuffix.
    split; [intro H; split; [tauto|constructor]|intros [H _]; tauto].
  - specialize (IH ltac:(discriminate)).
    unfold Always, Eventually in *.
    rewrite nonempty_neg in * by discriminate.
    rewrite nonempty_disj in * by discriminate.
    change (~ (formula_holds (Neg a) (s :: t :: tail) \/
      formula_holds (Suffix Truth (Neg a)) (s :: t :: tail)) <-> Forall (fun s => formula_holds a [s]) (s :: t :: tail)).
    rewrite nonempty_neg, suffix_step by discriminate.
    rewrite nonempty_neg by discriminate.
    change (formula_holds Truth (t :: tail)) with True.
    rewrite (pure_singleton a s (t :: tail) Hp).
    change (~ (formula_holds (Neg a) (t :: tail) \/ formula_holds (Suffix Truth (Neg a)) (t :: tail)) <-> Forall (fun s => formula_holds a [s]) (t :: tail)) in IH.
    rewrite nonempty_neg in IH by discriminate.
    fold formula_holds in *.
    rewrite (pure_singleton a t tail Hp) in *.
    change (formula_holds Truth (t :: tail)) with True.
    rewrite Forall_cons_iff. tauto.
Qed.

End Interpretation.

(** Package a chosen model for the later [ForModel] functors. This module
    type belongs to this particular syntax/semantics functor instance. *)
Module Type INTERPRETATION.
  Parameter interpretation : model.
End INTERPRETATION.
End MakeSemantics.
