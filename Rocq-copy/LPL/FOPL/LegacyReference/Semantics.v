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
From CyclistRocq.LPL.FOPL Require Import Signature.
From CyclistRocq.LPL.FOPL.LegacyReference Require Import Syntax.
Import ListNotations.

Module MakeSemantics (S : SIGNATURE).
Module Export Syn := MakeSyntax S.

(** The same overlapping operation applies to traces and to sequences of
    traces, as in Section 2 and Definition 5.3 of the manuscript. *)
Definition overlap_list {A : Type} (a b c : list A) : Prop :=
  exists prefix s tail, a = prefix ++ [s] /\ b = s :: tail /\ c = prefix ++ s :: tail.

Lemma overlap_list_append {A} (a b c : list A) : overlap_list a b c -> c = a ++ tl b.
Proof.
  intros [prefix [s [tail [-> [-> ->]]]]]. cbn; now rewrite <- app_assoc.
Qed.

Lemma last_append_nonempty {A} (prefix : list A) x tail default :
  last (prefix ++ x :: tail) default = last (x :: tail) default.
Proof.
  induction prefix as [|s prefix IH]; [reflexivity|].
  change (last (s :: (prefix ++ x :: tail)) default = last (x :: tail) default).
  destruct prefix; cbn in *; assumption.
Qed.

Lemma overlap_list_last {A} (a b c : list A) default :
  overlap_list a b c -> last c default = last b default.
Proof.
  intros [prefix [s [tail [_ [-> ->]]]]]. apply last_append_nonempty.
Qed.

Lemma map_involutive {A} (f : A -> A) (Hf : forall x, f (f x) = x) xs : map f (map f xs) = xs.
Proof. induction xs; cbn; [reflexivity|now rewrite Hf, IHxs]. Qed.

Lemma overlap_list_map {A B} (f : A -> B) a b c : overlap_list a b c ->
  overlap_list (map f a) (map f b) (map f c).
Proof.
  intros [prefix [s [tail [-> [-> ->]]]]]. rewrite !map_app; cbn.
  exists (map f prefix), (f s), (map f tail); auto.
Qed.

Lemma overlap_list_head {A} (a b c : list A) : overlap_list a b c ->
  exists s tail tail', a = s :: tail /\ c = s :: tail'.
Proof.
  intros [[|x prefix] [s [tail [-> [-> ->]]]]]; cbn; eauto.
Qed.

Lemma overlap_list_singleton {A} (s : A) b c :
  overlap_list [s] b c <-> exists tail, b = s :: tail /\ c = b.
Proof.
  split.
  - intros [prefix [s' [tail [Heq [-> ->]]]]].
    assert (prefix = []) as ->.
    { apply (f_equal (@length A)) in Heq. rewrite length_app in Heq.
      destruct prefix; [reflexivity|cbn in Heq; lia]. }
    cbn in Heq. inversion Heq; subst; exists tail; auto.
  - intros [tail [-> ->]]. exists [], s, tail; auto.
Qed.

Lemma overlap_list_snoc {A} (prefix : list A) s start rest result :
  overlap_list (prefix ++ [s]) (start :: rest) result <->
  start = s /\ result = (prefix ++ [s]) ++ rest.
Proof.
  split.
  - intros [prefix' [middle [tail [Heq [Hstart ->]]]]].
    inversion Hstart; subst.
    apply app_inj_tail in Heq as [-> ->]. split; [reflexivity|].
    now rewrite <- app_assoc.
  - intros [-> ->]. exists prefix, s, rest. repeat split; auto.
    now rewrite <- app_assoc.
Qed.

Lemma overlap_list_cons {A} (s : A) a b c : a <> [] ->
  (overlap_list (s :: a) b c <-> exists tail, c = s :: tail /\ overlap_list a b tail).
Proof.
  intro Hne; split.
  - intros [[|x prefix] [middle [tail [Heq [Hb Hc]]]]].
    + cbn in Heq; inversion Heq; contradiction.
    + cbn in Heq, Hc. inversion Heq; subst.
      exists (prefix ++ middle :: tail); split; [reflexivity|].
      exists prefix, middle, tail; auto.
  - intros [tail [-> [prefix [middle [rest [-> [-> ->]]]]]]].
    exists (s :: prefix), middle, rest; auto.
Qed.

Lemma overlap_list_assoc {A} (a b c out : list A) :
  (exists ab, overlap_list a b ab /\ overlap_list ab c out) <->
  (exists bc, overlap_list b c bc /\ overlap_list a bc out).
Proof.
  (* Reassociate by peeling the first trace. The singleton case is the
     boundary where overlap contributes no additional prefix state. This
     list lemma later reassociates both program runs and counterexamples. *)
  revert b c out; induction a as [|s a IH]; intros b c out.
  - split; intros [middle [H1 H2]];
      [destruct H1 as [prefix [x [tail [Heq _]]]] |
       destruct H2 as [prefix [x [tail [Heq _]]]]];
      symmetry in Heq; apply app_eq_nil in Heq; destruct Heq; discriminate.
  - destruct a as [|t a].
    + split.
      * intros [ab [Hab Hout]]. apply overlap_list_singleton in Hab as [tail [-> ->]].
        exists out; split; [exact Hout|].
        destruct (overlap_list_head _ _ _ Hout) as [x [r [r' [Heq Hout_eq]]]].
        inversion Heq; subst. apply overlap_list_singleton; eauto.
      * intros [bc [Hbc Hout]]. apply overlap_list_singleton in Hout as [tail [Heq ->]].
        destruct (overlap_list_head _ _ _ Hbc) as [x [r [r' [Hb Hbc_eq]]]].
        rewrite Hbc_eq in Heq; inversion Heq; subst.
        exists (s :: r); split; [apply overlap_list_singleton; eauto|exact Hbc].
    + split.
      * intros [ab [Hab Hout]].
        apply overlap_list_cons in Hab as [abtail [-> Hab]]; [|discriminate].
        destruct (overlap_list_head _ _ _ Hab) as [x [r [r' [_ Habtail]]]].
        assert (abtail <> []) as Hne by (rewrite Habtail; discriminate).
        apply overlap_list_cons in Hout as [outtail [-> Hout]]; [|exact Hne].
        assert (exists bc, overlap_list b c bc /\ overlap_list (t :: a) bc outtail) as H.
        { apply IH. exists abtail; auto. }
        destruct H as [bc [Hbc Ha]]. exists bc; split; [exact Hbc|].
        apply overlap_list_cons; [discriminate|]. eauto.
      * intros [bc [Hbc Ha]].
        apply overlap_list_cons in Ha as [outtail [-> Ha]]; [|discriminate].
        assert (exists ab, overlap_list (t :: a) b ab /\ overlap_list ab c outtail) as H.
        { apply IH. exists bc; auto. }
        destruct H as [ab [Hab Hout]]. exists (s :: ab); split;
          apply overlap_list_cons; try (eexists; split; [reflexivity|eassumption]); try discriminate.
        destruct (overlap_list_head _ _ _ Hab) as [x [r [r' [_ ->]]]]; discriminate.
Qed.

(** Interpretations are total on argument lists; syntax checks enforce arity
    for actual object-language uses. No injectivity, disjoint constructors,
    decision procedure for truth, or arithmetic structure is assumed.
    [domain_inhabitant] witnesses nonemptiness and supports classical choice. *)
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

(** A framework world contains two label environments, rather than just one
    program state. World names denote states; trace names denote nonempty
    finite traces. The proof field is why a trace variable passes the purely
    structural nonemptiness check in Syntax.v. *)
Record world : Type := World {
  world_mapping : nat -> state;
  trace_mapping : nat -> trace;
  trace_mapping_nonempty : forall x, trace_mapping x <> []
}.

(** Evaluate inside out. In a nested assignment, both the old state and the
    right-hand term come from the already evaluated previous update. *)
Fixpoint eval_update (w : world) (u : update) : state :=
  match u with
  | Base x => world_mapping w x
  | AssignUpdate x t u =>
      let s := eval_update w u in write s x (eval_term s t)
  end.

(** D1: label juxtaposition is ordinary append, with no endpoint condition. *)
Fixpoint eval_label (w : world) (l : label) : trace :=
  match l with
  | Empty => []
  | StateLabel u => [eval_update w u]
  | TraceLabel x => trace_mapping w x
  | Join a b => eval_label w a ++ eval_label w b
  end.

Definition label_eval w l tr := eval_label w l = tr.
Definition label_admissible w l := eval_label w l <> [].

Lemma label_eval_total w l : exists tr, label_eval w l tr.
Proof. exists (eval_label w l); reflexivity. Qed.
Lemma label_eval_unique w l tr tr' : label_eval w l tr -> label_eval w l tr' -> tr = tr'.
Proof. unfold label_eval; congruence. Qed.
Lemma label_left_unit w l : eval_label w (Join Empty l) = eval_label w l.
Proof. reflexivity. Qed.
Lemma label_right_unit w l : eval_label w (Join l Empty) = eval_label w l.
Proof. cbn; apply app_nil_r. Qed.
Lemma label_join_length w a b :
  length (eval_label w (Join a b)) = length (eval_label w a) + length (eval_label w b).
Proof. cbn; apply length_app. Qed.
Lemma label_prefix_length w u l :
  length (eval_label w (Join (StateLabel u) l)) = S (length (eval_label w l)).
Proof. reflexivity. Qed.

(** Reflection is independent of endpoint values: append is empty exactly
    when both lists are empty. Consequently syntactic nonemptiness works
    uniformly for every world, including joins of different endpoint states. *)
Lemma label_nonemptyb_spec w l : label_nonemptyb l = true <-> label_admissible w l.
Proof.
  unfold label_admissible. induction l as [|u|x|a IHa b IHb]; cbn.
  - split; [discriminate | intro H; contradiction H; reflexivity].
  - split; [intros _; discriminate | auto].
  - split; [intros _; apply trace_mapping_nonempty | auto].
  - rewrite orb_true_iff, IHa, IHb. split.
    + intros [Ha | Hb] Heq; apply app_eq_nil in Heq; tauto.
    + destruct (eval_label w a), (eval_label w b); cbn; intuition discriminate.
Qed.

(** Sorted environment updates are the semantic counterparts of label
    substitution. A trace replacement must supply nonemptiness evidence so
    that the new environment still inhabits [world]. *)
Definition replace_world (w : world) (x : nat) (value : state) : world :=
  World (fun y => if Nat.eqb x y then value else world_mapping w y)
    (trace_mapping w) (trace_mapping_nonempty w).

Definition replace_trace (w : world) (x : nat) (value : trace) (Hne : value <> []) : world.
Proof.
  refine (World (world_mapping w) (fun y => if Nat.eqb x y then value else trace_mapping w y) _).
  intro y; destruct (Nat.eqb x y); [exact Hne|apply trace_mapping_nonempty].
Defined.

(** Substitution changes syntax on the left and the label environment on the
    right. Formula syntax is untouched. Rules.v will transport both sequent
    truth and ranks along exactly these environment changes. *)
Lemma eval_world_substitution w x replacement u :
  eval_update w (subst_world_update x replacement u) =
  eval_update (replace_world w x (eval_update w replacement)) u.
Proof.
  induction u; cbn [subst_world_update eval_update replace_world world_mapping].
  - destruct (Nat.eqb x world_variable); reflexivity.
  - now rewrite IHu.
Qed.

Lemma eval_world_label_substitution w x replacement l :
  eval_label w (subst_world_label x replacement l) =
  eval_label (replace_world w x (eval_update w replacement)) l.
Proof.
  induction l; cbn [subst_world_label eval_label]; try reflexivity.
  - now rewrite eval_world_substitution.
  - now rewrite IHl1, IHl2.
Qed.

Lemma eval_trace_label_substitution w x replacement Hne l :
  eval_label w (subst_trace_label x replacement l) =
  eval_label (replace_trace w x (eval_label w replacement) Hne) l.
Proof.
  induction l; cbn [subst_trace_label eval_label]; try reflexivity.
  - assert (forall u, eval_update w u = eval_update (replace_trace w x (eval_label w replacement) Hne) u) as Hu.
    { intro v; induction v; cbn [eval_update replace_trace world_mapping]; [reflexivity|now rewrite IHv]. }
    now rewrite Hu.
  - cbn [replace_trace trace_mapping]. destruct (Nat.eqb x trace_variable); reflexivity.
  - now rewrite IHl1, IHl2.
Qed.

(** These equations justify explicit parenthesis/unit rules while keeping
    graph equality syntactic. They do not choose a normal form for a label. *)
Lemma eval_rotate_label w path left l : eval_label w (rotate_label path left l) = eval_label w l.
Proof.
  revert l; induction path as [|direction path IH]; intro l.
  - destruct left; destruct l; cbn [rotate_label]; try reflexivity.
    + destruct l2; cbn [eval_label]; try reflexivity; symmetry; apply app_assoc.
    + destruct l1; cbn [eval_label]; try reflexivity; apply app_assoc.
  - destruct l; cbn [rotate_label]; try reflexivity.
    destruct direction; cbn [eval_label]; now rewrite IH.
Qed.

Lemma eval_unit_label w path on_left insert l : eval_label w (unit_label path on_left insert l) = eval_label w l.
Proof.
  revert l; induction path as [|direction path IH]; intro l.
  - destruct insert, on_left; cbn [unit_label eval_label]; try reflexivity; try apply app_nil_r.
    + destruct l; try reflexivity; destruct l1; cbn [eval_label]; reflexivity.
    + destruct l; try reflexivity; destruct l2; cbn [eval_label]; try reflexivity; symmetry; apply app_nil_r.
  - destruct l; cbn [unit_label]; try reflexivity.
    destruct direction; cbn [eval_label]; now rewrite IH.
Qed.

(** Program composition overlaps exactly one shared endpoint. Unlike label
    evaluation it can fail, and it never deletes a stuttering transition. *)
Definition overlap : trace -> trace -> trace -> Prop := @overlap_list state.

Definition compose (R T : trace -> Prop) (tr : trace) : Prop :=
  exists a b, R a /\ T b /\ overlap a b tr.

(** The base case is the successful true test, not a singleton identity
    trace. Thus even zero iterations record [s;s], and a positive finite
    unfolding ends in the final stutter supplied by its zero-power tail. *)
Fixpoint finite_power (R : trace -> Prop) (n : nat) (tr : trace) : Prop :=
  match n with
  | 0 => exists s, tr = [s; s]
  | S n => compose R (finite_power R n) tr
  end.

(** Both the suffix and the removed prefix are nonempty. Suffix modalities
    therefore move strictly forward, and cannot succeed on a singleton. *)
Definition proper_suffix (small big : trace) : Prop :=
  small <> [] /\ exists prefix, prefix <> [] /\ big = prefix ++ small.

(** The guard of a test is evaluated on the two-state stutter [s;s]. The zero
    iteration case is the successful true test, also [s;s]. Quantification
    writes one uniform value to every state; D2 is checked in Syntax.v. *)
(** Atoms inspect the first state. [First] restricts its entire body to that
    singleton. [Suffix a b] chooses a later suffix satisfying [b], requiring
    [a] at each strictly intermediate suffix, but not at the current trace.
    Its dual is expressed by negating the corresponding failure condition.
    Boxes/diamonds extend the current trace by whole program executions;
    they test their body on the accumulated trace, not only its final state. *)
Fixpoint formula_holds (a : formula) (tr : trace) : Prop :=
  match tr with
  | [] => False
  | s :: tail =>
    match a with
    | Truth => True
    | Falsity => False
    | Pred p ts => interpret_predicate M p (map (eval_term s) ts)
    | Equal a b => eval_term s a = eval_term s b
    | Neg a => ~ formula_holds a tr
    | Conj a b => formula_holds a tr /\ formula_holds b tr
    | Disj a b => formula_holds a tr \/ formula_holds b tr
    | Impl a b => formula_holds a tr -> formula_holds b tr
    | All x a => forall value, formula_holds a (map (fun s => write s x value) tr)
    | Ex x a => exists value, formula_holds a (map (fun s => write s x value) tr)
    | First a => formula_holds a [s]
    | Suffix a b =>
        exists suffix, proper_suffix suffix tr /\ formula_holds b suffix /\
          forall middle, proper_suffix suffix middle -> proper_suffix middle tr -> formula_holds a middle
    | DualSuffix a b =>
        ~ (exists suffix, proper_suffix suffix tr /\ ~ formula_holds b suffix /\
          forall middle, proper_suffix suffix middle -> proper_suffix middle tr -> ~ formula_holds a middle)
    | Box p a => forall execution result,
        program_holds p execution -> overlap tr execution result -> formula_holds a result
    | Diamond p a => exists execution result,
        program_holds p execution /\ overlap tr execution result /\ formula_holds a result
    end
  end
with program_holds (p : program) (tr : trace) : Prop :=
  match p with
  | Assign x t => exists s, tr = [s; write s x (eval_term s t)]
  | Test a => exists s, tr = [s; s] /\ formula_holds a [s; s]
  | Seq a b => compose (program_holds a) (program_holds b) tr
  | Choice a b => program_holds a tr \/ program_holds b tr
  | Star a => exists n, finite_power (program_holds a) n tr
  end.

(** Independent shallow FOL evaluation. Nonpure cases have no FOL meaning. *)
Fixpoint fol_holds (a : formula) (s : state) : Prop :=
  match a with
  | Truth => True
  | Falsity => False
  | Pred p ts => interpret_predicate M p (map (eval_term s) ts)
  | Equal a b => eval_term s a = eval_term s b
  | Neg a => ~ fol_holds a s
  | Conj a b => fol_holds a s /\ fol_holds b s
  | Disj a b => fol_holds a s \/ fol_holds b s
  | Impl a b => fol_holds a s -> fol_holds b s
  | All x a => forall value, fol_holds a (write s x value)
  | Ex x a => exists value, fol_holds a (write s x value)
  | _ => False
  end.

Lemma fol_fresh a : pureb a = true -> forall s x value,
  ~ In x (formula_vars a) -> (fol_holds a (write s x value) <-> fol_holds a s).
Proof.
  induction a; cbn [pureb]; intro Hp; try discriminate;
    intros s u value Hfresh; cbn [fol_holds formula_vars] in *; try tauto.
  - assert (map (eval_term (write s u value)) args = map (eval_term s) args) as Heq.
    { apply map_ext_in; intros t Hin; apply eval_term_fresh.
      intro H; apply Hfresh; apply in_flat_map; exists t; auto. }
    now rewrite Heq.
  - rewrite !eval_term_fresh; try tauto; intros H; apply Hfresh; apply in_app_iff; auto.
  - now rewrite IHa by assumption.
  - apply andb_true_iff in Hp as [Ha Hb].
    rewrite IHa1, IHa2; try assumption; try (intro H; apply Hfresh; apply in_app_iff; auto); tauto.
  - apply andb_true_iff in Hp as [Ha Hb].
    rewrite IHa1, IHa2; try assumption; try (intro H; apply Hfresh; apply in_app_iff; auto); tauto.
  - apply andb_true_iff in Hp as [Ha Hb].
    rewrite IHa1, IHa2; try assumption; try (intro H; apply Hfresh; apply in_app_iff; auto); tauto.
  - assert (u <> x) as Hux by (intro Heq; subst u; apply Hfresh; now left).
    assert (~ In u (formula_vars a)) as Hbody by (intro Hin; apply Hfresh; now right).
    split; intros H v; specialize (H v).
    + rewrite write_commute in H by exact Hux. apply (proj1 (IHa Hp (write s x v) u value Hbody)); exact H.
    + rewrite write_commute by exact Hux. apply (proj2 (IHa Hp (write s x v) u value Hbody)); exact H.
  - assert (u <> x) as Hux by (intro Heq; subst u; apply Hfresh; now left).
    assert (~ In u (formula_vars a)) as Hbody by (intro Hin; apply Hfresh; now right).
    split; intros [v H]; exists v.
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
  induction a; cbn [pureb]; intro Hp; try discriminate;
    intros s u t Hfree; cbn [raw_subst_fo free_forb fol_holds] in *; try tauto.
  - rewrite map_map. assert (map (fun a => eval_term s (subst_term u t a)) args =
      map (eval_term (write s u (eval_term s t))) args) as Heq.
    { apply map_ext; intro a; apply eval_term_subst. }
    now rewrite Heq.
  - now rewrite !eval_term_subst.
  - now rewrite IHa by assumption.
  - apply andb_true_iff in Hp as [Ha Hb]; apply andb_true_iff in Hfree as [Hfa Hfb].
    rewrite IHa1, IHa2 by assumption; tauto.
  - apply andb_true_iff in Hp as [Ha Hb]; apply andb_true_iff in Hfree as [Hfa Hfb].
    rewrite IHa1, IHa2 by assumption; tauto.
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
  - destruct (Nat.eqb u x) eqn:Hux.
    + apply Nat.eqb_eq in Hux; subst u. cbn [fol_holds]. setoid_rewrite write_shadow; reflexivity.
    + apply Nat.eqb_neq in Hux; apply andb_true_iff in Hfree as [Hfresh Hfree].
      apply negb_true_iff, occursb_false in Hfresh. cbn [fol_holds].
      split; intros [v H]; exists v.
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
  - destruct a; cbn [fol_size] in Hsize; lia.
  - destruct a; cbn [pureb fol_size] in Hp, Hsize; try discriminate;
      cbn [subst_fo_fuel fol_holds]; try tauto.
    + rewrite map_map. assert (map (fun a => eval_term s (subst_term u t a)) args =
        map (eval_term (write s u (eval_term s t))) args) as Heq.
      { apply map_ext; intro a; apply eval_term_subst. } now rewrite Heq.
    + now rewrite !eval_term_subst.
    + rewrite IH by (assumption || lia); tauto.
    + apply andb_true_iff in Hp as [Ha Hb]; rewrite !IH by (assumption || lia); tauto.
    + apply andb_true_iff in Hp as [Ha Hb]; rewrite !IH by (assumption || lia); tauto.
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
    + destruct (Nat.eqb u x) eqn:Hux.
      * apply Nat.eqb_eq in Hux; subst u; cbn [fol_holds]; setoid_rewrite write_shadow; reflexivity.
      * apply Nat.eqb_neq in Hux; destruct (existsb (Nat.eqb x) (term_vars t)) eqn:Hcapture.
        -- set (z := fresh_name (u :: x :: (formula_vars a ++ term_vars t))).
           assert (~ In z (u :: x :: (formula_vars a ++ term_vars t))) as Hz by apply fresh_name_not_in.
           assert (z <> u /\ z <> x /\ ~ In z (formula_vars a) /\ ~ In z (term_vars t)) as [Hzu [Hzx [Hzbody Hzt]]].
           { repeat split; intro H; apply Hz; cbn; try (left; congruence);
             try (right; left; congruence); right; right; apply in_app_iff; auto. }
           change (fol_holds (Ex z (subst_fo_fuel fuel u t (raw_subst_fo x (Var z) a))) s <-> fol_holds (Ex x a) (write s u (eval_term s t))).
           transitivity (fol_holds (Ex z (raw_subst_fo x (Var z) a)) (write s u (eval_term s t))).
           ++ apply ex_subst_congruence; try assumption.
              intro state'; apply IH; [apply raw_subst_pure; exact Hp|rewrite raw_subst_size; lia].
           ++ apply alpha_ex; assumption.
        -- apply ex_subst_congruence; [congruence|now apply occursb_false|].
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
  induction a; cbn [pureb]; intro Hp; try discriminate;
    intros s tail; cbn [formula_holds fol_holds]; try tauto.
  - rewrite IHa by exact Hp. tauto.
  - apply andb_true_iff in Hp as [Ha Hb].
    rewrite IHa1 by exact Ha. rewrite IHa2 by exact Hb. tauto.
  - apply andb_true_iff in Hp as [Ha Hb].
    rewrite IHa1 by exact Ha. rewrite IHa2 by exact Hb. tauto.
  - apply andb_true_iff in Hp as [Ha Hb].
    rewrite IHa1 by exact Ha. rewrite IHa2 by exact Hb. tauto.
  - split; intros H v; specialize (IHa Hp (write s x v) (map (fun s => write s x v) tail));
      [apply IHa; apply H | apply IHa; apply H].
  - split; intros [v H]; exists v;
      specialize (IHa Hp (write s x v) (map (fun s => write s x v) tail));
      apply IHa; exact H.
Qed.

Lemma pure_singleton a s tail : pureb a = true ->
  (formula_holds a (s :: tail) <-> formula_holds a [s]).
Proof. intro H; rewrite !pure_head by exact H; reflexivity. Qed.

(** Assertion truth explicitly requires a nonempty interpreted label.
    Sequent denotation then guards the whole implication by admissibility of
    every assertion label. An empty succedent is false, an empty antecedent
    is true. Tags have no role in any of these truth definitions. *)
Definition labelled_holds w o : Prop :=
  label_admissible w o.(occurrence_label) /\
  formula_holds o.(occurrence_formula) (eval_label w o.(occurrence_label)).
Definition admissible j w :=
  Forall (fun o => label_admissible w o.(occurrence_label)) (j.(antecedent) ++ j.(succedent)).
Definition left_holds w context := Forall (labelled_holds w) context.
Definition right_holds w context := exists o, In o context /\ labelled_holds w o.
Definition denote j w := admissible j w -> left_holds w j.(antecedent) -> right_holds w j.(succedent).
Definition Valid j := forall w, denote j w.

(** A label-map evaluation equation transports assertion truth and then the
    entire guarded sequent. The sequent proof must transport admissibility
    as well as left/right truth; forgetting that guard would lose the exact
    meaning of [denote] for arbitrary raw judgments. *)
Lemma labelled_mapping f w w' :
  (forall l, eval_label w (f l) = eval_label w' l) -> forall o,
  (labelled_holds w (map_label_occurrence f o) <-> labelled_holds w' o).
Proof.
  intros H o; unfold labelled_holds, label_admissible; cbn [map_label_occurrence occurrence_label occurrence_formula].
  now rewrite H.
Qed.

Lemma denote_mapping f w w' :
  (forall l, eval_label w (f l) = eval_label w' l) -> forall j,
  (denote (map_labels f j) w <-> denote j w').
Proof.
  intros Hmap j.
  assert (forall context, Forall (fun o => label_admissible w o.(occurrence_label))
      (map (map_label_occurrence f) context) <->
      Forall (fun o => label_admissible w' o.(occurrence_label)) context) as Hadm.
  { intro context; rewrite Forall_map, !Forall_forall.
    unfold label_admissible; cbn [map_label_occurrence occurrence_label].
    setoid_rewrite Hmap; reflexivity. }
  assert (forall context, left_holds w (map (map_label_occurrence f) context) <-> left_holds w' context) as Hl.
  { intro context; unfold left_holds; rewrite Forall_map, !Forall_forall.
    setoid_rewrite (labelled_mapping f w w' Hmap); reflexivity. }
  assert (forall context, right_holds w (map (map_label_occurrence f) context) <-> right_holds w' context) as Hr.
  { intro context; unfold right_holds; setoid_rewrite in_map_iff; split.
    - intros [o [[original [Heq Hin]] Ho]]. subst o; exists original; split; [exact Hin|].
      apply (labelled_mapping f w w' Hmap); exact Ho.
    - intros [o [Hin Ho]]. exists (map_label_occurrence f o); split.
      + exists o; auto.
      + apply (labelled_mapping f w w' Hmap); exact Ho. }
  unfold denote, admissible; cbn [map_labels antecedent succedent].
  rewrite <- map_app, Hadm, Hl, Hr; reflexivity.
Qed.

(** Truth is insensitive to tag renaming or erasure. These equations alone
    do not justify cyclic trace routing: Rules.v separately proves how ranks
    follow an explicit renaming and checks uniqueness of the resulting tags. *)
Lemma denote_tag_renaming f j w : denote (rename_tags f j) w <-> denote j w.
Proof.
  assert (forall o, labelled_holds w (rename_occurrence_tag f o) <-> labelled_holds w o) as Ho by (intro o; reflexivity).
  assert (forall context, Forall (fun o => label_admissible w o.(occurrence_label))
      (map (rename_occurrence_tag f) context) <->
      Forall (fun o => label_admissible w o.(occurrence_label)) context) as Ha.
  { intro context; rewrite Forall_map; reflexivity. }
  assert (forall context, left_holds w (map (rename_occurrence_tag f) context) <-> left_holds w context) as Hl.
  { intro context; unfold left_holds; rewrite Forall_map, !Forall_forall; reflexivity. }
  assert (forall context, right_holds w (map (rename_occurrence_tag f) context) <-> right_holds w context) as Hr.
  { intro context; unfold right_holds; setoid_rewrite in_map_iff; split.
    - intros [o [[original [Heq Hin]] Hholds]]; subst o; exists original; auto.
    - intros [o [Hin Hholds]]; exists (rename_occurrence_tag f o); split; [exists o; auto|exact Hholds]. }
  unfold denote, admissible; cbn [rename_tags antecedent succedent]; rewrite <- map_app, Ha, Hl, Hr; reflexivity.
Qed.

Lemma denote_erase_tags j w : denote (erase_tags j) w <-> denote j w.
Proof.
  assert (forall o, labelled_holds w (erase_tag o) <-> labelled_holds w o) as Ho by (intro o; reflexivity).
  assert (forall context, Forall (fun o => label_admissible w o.(occurrence_label))
      (map (erase_tag) context) <->
      Forall (fun o => label_admissible w o.(occurrence_label)) context) as Ha.
  { intro context; rewrite Forall_map; reflexivity. }
  assert (forall context, left_holds w (map (erase_tag) context) <-> left_holds w context) as Hl.
  { intro context; unfold left_holds; rewrite Forall_map, !Forall_forall; reflexivity. }
  assert (forall context, right_holds w (map (erase_tag) context) <-> right_holds w context) as Hr.
  { intro context; unfold right_holds; setoid_rewrite in_map_iff; split.
    - intros [o [[original [Heq Hin]] Hholds]]; subst o; exists original; auto.
    - intros [o [Hin Hholds]]; exists (erase_tag o); split; [exists o; auto|exact Hholds]. }
  unfold denote, admissible; cbn [erase_tags antecedent succedent]; rewrite <- map_app, Ha, Hl, Hr; reflexivity.
Qed.

Lemma backlink_eqb_denote a b w : backlink_eqb a b = true -> (denote a w <-> denote b w).
Proof.
  unfold backlink_eqb; intro Heq; apply judgment_eqb_spec in Heq.
  rewrite <- (denote_erase_tags a w), <- (denote_erase_tags b w); now rewrite Heq.
Qed.

Lemma valid_admissible j : Valid j <->
  forall w, admissible j w -> left_holds w j.(antecedent) -> right_holds w j.(succedent).
Proof. reflexivity. Qed.

(** The useful shape of a countermodel: all labels are admissible, all
    antecedents hold, and every succedent fails. Rules.v starts its backward
    semantic steps with this extraction rather than assuming admissibility. *)
Lemma false_sequent j w : ~ denote j w ->
  admissible j w /\ left_holds w j.(antecedent) /\
  forall o, In o j.(succedent) -> ~ labelled_holds w o.
Proof.
  unfold denote, right_holds; intros H.
  assert (admissible j w) as Ha by tauto.
  assert (left_holds w j.(antecedent)) as Hl by tauto.
  repeat split; try assumption. intros o Hin Ho. apply H; auto. exists o; auto.
Qed.

Lemma judgment_wfb_admissible j w : judgment_wfb j = true -> admissible j w.
Proof.
  unfold judgment_wfb, admissible. rewrite !andb_true_iff.
  intros [[Hl Hr] _]. apply Forall_app; split; apply Forall_forall;
    intros o Hin; [apply forallb_forall with (x := o) in Hl | apply forallb_forall with (x := o) in Hr];
    try assumption; unfold occurrence_wfb in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [H ?] end;
    apply label_nonemptyb_spec; assumption.
Qed.

Lemma overlap_nonempty a b c : overlap a b c -> a <> [] /\ b <> [] /\ c <> [].
Proof.
  intros [prefix [s [tail [-> [-> ->]]]]].
  repeat split; try discriminate; intro H; apply app_eq_nil in H; destruct H; discriminate.
Qed.

Lemma overlap_length a b c : overlap a b c -> length c + 1 = length a + length b.
Proof.
  intros [prefix [s [tail [-> [-> ->]]]]]. rewrite !length_app. cbn; lia.
Qed.

Lemma finite_power_length R :
  (forall tr, R tr -> 2 <= length tr) ->
  forall n tr, finite_power R n tr -> 2 <= length tr.
Proof.
  intros HR n; induction n; intros tr H.
  - destruct H as [s ->]; cbn; lia.
  - destruct H as [a [b [Ha [Hb Ho]]]].
    specialize (HR a Ha). specialize (IHn b Hb).
    pose proof (overlap_length a b tr Ho). lia.
Qed.

(** Every execution contains at least one transition, including tests and
    star-zero stutters. Overlap merges a shared state, not that transition.
    Progress.v relies on this fact when constructing execution histories. *)
Lemma program_length p : forall tr, program_holds p tr -> 2 <= length tr.
Proof.
  induction p; intros tr H; cbn [program_holds] in H.
  - destruct H as [s ->]; cbn; lia.
  - destruct H as [s [-> _]]; cbn; lia.
  - destruct H as [a [b [Ha [Hb Ho]]]].
    specialize (IHp1 a Ha). specialize (IHp2 b Hb).
    pose proof (overlap_length a b tr Ho). lia.
  - destruct H; [apply IHp1 | apply IHp2]; assumption.
  - destruct H as [n H]; eapply finite_power_length; eauto.
Qed.

Lemma overlap_snoc prefix s start rest result :
  overlap (prefix ++ [s]) (start :: rest) result <->
  start = s /\ result = (prefix ++ [s]) ++ rest.
Proof. apply overlap_list_snoc. Qed.

(** Semantic equations for rule kernels. The assignment/test equations
    expose the last state of the current trace and append the resulting
    state. Their diamond versions share the same endpoint calculation. *)
Lemma box_assignment prefix s x t a :
  formula_holds (Box (Assign x t) a) (prefix ++ [s]) <->
  formula_holds a ((prefix ++ [s]) ++ [write s x (eval_term s t)]).
Proof.
  assert (prefix ++ [s] <> []) as Hne by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  destruct (prefix ++ [s]) as [|head tail] eqn:Htr; [contradiction|].
  cbn [formula_holds]. split.
  - intro H; eapply H.
    + exists s; reflexivity.
    + rewrite <- Htr; apply overlap_snoc; auto.
  - intros Ha execution result [start ->] Ho.
    rewrite <- Htr in Ho. apply overlap_snoc in Ho as [-> ->]. now rewrite Htr.
Qed.

Lemma diamond_assignment prefix s x t a :
  formula_holds (Diamond (Assign x t) a) (prefix ++ [s]) <->
  formula_holds a ((prefix ++ [s]) ++ [write s x (eval_term s t)]).
Proof.
  assert (prefix ++ [s] <> []) as Hne by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  destruct (prefix ++ [s]) as [|head tail] eqn:Htr; [contradiction|].
  cbn [formula_holds]. split.
  - intros [execution [result [[start ->] [Ho Ha]]]].
    rewrite <- Htr in Ho. apply overlap_snoc in Ho as [-> ->]. now rewrite Htr in Ha.
  - intro Ha. exists [s; write s x (eval_term s t)], ((head :: tail) ++ [write s x (eval_term s t)]).
    split; [exists s; reflexivity|]. split; [rewrite <- Htr; apply overlap_snoc; auto|exact Ha].
Qed.

Lemma box_test prefix s guard a :
  formula_holds (Box (Test guard) a) (prefix ++ [s]) <->
  (formula_holds guard [s;s] -> formula_holds a ((prefix ++ [s]) ++ [s])).
Proof.
  assert (prefix ++ [s] <> []) as Hne by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  destruct (prefix ++ [s]) as [|head tail] eqn:Htr; [contradiction|].
  cbn [formula_holds]. split.
  - intros H Hg; eapply H.
    + exists s; auto.
    + rewrite <- Htr; apply overlap_snoc; auto.
  - intros H execution result [start [-> Hg]] Ho.
    rewrite <- Htr in Ho. apply overlap_snoc in Ho as [-> ->]. rewrite Htr; auto.
Qed.

Lemma diamond_test prefix s guard a :
  formula_holds (Diamond (Test guard) a) (prefix ++ [s]) <->
  formula_holds guard [s;s] /\ formula_holds a ((prefix ++ [s]) ++ [s]).
Proof.
  assert (prefix ++ [s] <> []) as Hne by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  destruct (prefix ++ [s]) as [|head tail] eqn:Htr; [contradiction|].
  cbn [formula_holds]. split.
  - intros [execution [result [[start [-> Hg]] [Ho Ha]]]].
    rewrite <- Htr in Ho. apply overlap_snoc in Ho as [-> ->]. rewrite <- Htr; auto.
  - intros [Hg Ha]; exists [s;s], ((head :: tail) ++ [s]); split; [exists s; auto|].
    split; [rewrite <- Htr; apply overlap_snoc; auto|exact Ha].
Qed.

(** Reassociating overlapping executions turns sequence into nested boxes.
    Choice becomes conjunction for boxes and disjunction for diamonds. The
    star equations unfold an arbitrary finite power into its zero case or
    one execution followed by a smaller finite power. *)
Lemma box_sequence a b body tr : tr <> [] ->
  (formula_holds (Box (Seq a b) body) tr <-> formula_holds (Box a (Box b body)) tr).
Proof.
  intro Hne; destruct tr as [|s tail]; [contradiction|]; cbn [formula_holds program_holds].
  split.
  - intros H execution middle Ha Ho.
    destruct (overlap_nonempty _ _ _ Ho) as [_ [_ Hmiddle]].
    destruct middle as [|m rest]; [contradiction|]; cbn [formula_holds].
    intros execution' result Hb Ho'.
    assert (exists both, overlap_list execution execution' both /\ overlap_list (s :: tail) both result) as Hcombined.
    { apply overlap_list_assoc; exists (m :: rest); auto. }
    destruct Hcombined as [both [Hboth Hresult]]. eapply H; [|exact Hresult].
    exists execution, execution'; auto.
  - intros H execution result [first [second [Ha [Hb Hexecution]]]] Ho.
    assert (exists middle, overlap_list (s :: tail) first middle /\ overlap_list middle second result) as Hmiddle.
    { apply overlap_list_assoc; exists execution; auto. }
    destruct Hmiddle as [middle [Ho1 Ho2]]. specialize (H first middle Ha Ho1).
    destruct (overlap_nonempty _ _ _ Ho1) as [_ [_ Hne']].
    destruct middle; [contradiction|]. eapply H; eauto.
Qed.

Lemma box_choice a b body tr : tr <> [] ->
  (formula_holds (Box (Choice a b) body) tr <->
   formula_holds (Box a body) tr /\ formula_holds (Box b body) tr).
Proof.
  intro Hne; destruct tr as [|s tail]; [contradiction|]; cbn [formula_holds program_holds].
  split.
  - intro H; split; intros execution result Hp Ho; eapply H; eauto.
  - intros [Ha Hb] execution result [Hp|Hp] Ho; [eapply Ha|eapply Hb]; eauto.
Qed.

Lemma box_star a body tr : tr <> [] ->
  (formula_holds (Box (Star a) body) tr <->
   formula_holds (Box (Test Truth) body) tr /\ formula_holds (Box a (Box (Star a) body)) tr).
Proof.
  intro Hne. rewrite <- box_sequence by exact Hne.
  destruct tr as [|s tail]; [contradiction|]; cbn [formula_holds program_holds].
  split.
  - intro H; split.
    + intros execution result [start [-> _]] Ho. eapply H; [exists 0, start; reflexivity|exact Ho].
    + intros execution result [first [second [Ha [[n Hn] Hex]]]] Ho.
      apply (H execution result); [exists (S n), first, second; auto|exact Ho].
  - intros [H0 HS] execution result [n Hn] Ho. destruct n.
    + destruct Hn as [start ->]. eapply H0; [exists start; auto|exact Ho].
    + destruct Hn as [first [second [Ha [Hn Hex]]]].
      eapply HS; [exists first, second; split; [exact Ha|]; split; [exists n; exact Hn|exact Hex]|exact Ho].
Qed.

Lemma diamond_sequence a b body tr : tr <> [] ->
  (formula_holds (Diamond (Seq a b) body) tr <-> formula_holds (Diamond a (Diamond b body)) tr).
Proof.
  intro Hne; destruct tr as [|s tail]; [contradiction|]; cbn [formula_holds program_holds].
  split.
  - intros [execution [result [[first [second [Ha [Hb Hexecution]]]] [Ho Hbody]]]].
    assert (exists middle, overlap_list (s :: tail) first middle /\ overlap_list middle second result) as Hmiddle.
    { apply overlap_list_assoc; exists execution; auto. }
    destruct Hmiddle as [middle [Ho1 Ho2]]. exists first, middle; split; [exact Ha|].
    split; [exact Ho1|]. destruct (overlap_nonempty _ _ _ Ho1) as [_ [_ Hne']].
    destruct middle as [|m rest]; [contradiction|]; cbn [formula_holds].
    exists second, result; auto.
  - intros [first [middle [Ha [Ho1 Hbody]]]].
    destruct (overlap_nonempty _ _ _ Ho1) as [_ [_ Hne']].
    destruct middle as [|m rest]; [contradiction|].
    destruct Hbody as [second [result [Hb [Ho2 Hbody]]]].
    assert (exists execution, overlap_list first second execution /\ overlap_list (s :: tail) execution result) as Hexecution.
    { apply overlap_list_assoc; exists (m :: rest); auto. }
    destruct Hexecution as [execution [Hex Ho]]. exists execution, result; split; [|auto].
    exists first, second; auto.
Qed.

Lemma diamond_choice a b body tr : tr <> [] ->
  (formula_holds (Diamond (Choice a b) body) tr <->
   formula_holds (Diamond a body) tr \/ formula_holds (Diamond b body) tr).
Proof.
  intro Hne; destruct tr as [|s tail]; [contradiction|]; cbn [formula_holds program_holds].
  split.
  - intros [execution [result [[Ha|Hb] [Ho Hbody]]]];
      [left|right]; exists execution, result; auto.
  - intros [[execution [result [Hp [Ho Hbody]]]]|[execution [result [Hp [Ho Hbody]]]]];
      exists execution, result; split; [now left|auto|now right|auto].
Qed.

Lemma diamond_star a body tr : tr <> [] ->
  (formula_holds (Diamond (Star a) body) tr <->
   formula_holds (Diamond (Test Truth) body) tr \/ formula_holds (Diamond a (Diamond (Star a) body)) tr).
Proof.
  intro Hne; rewrite <- diamond_sequence by exact Hne.
  destruct tr as [|s tail]; [contradiction|]; cbn [formula_holds program_holds].
  split.
  - intros [execution [result [[n Hn] [Ho Hbody]]]]. destruct n.
    + left; exists execution, result; split; [|auto]. destruct Hn as [start ->]; exists start; auto.
    + right; exists execution, result; split; [|auto].
      destruct Hn as [first [second [Ha [Hn Hex]]]].
      exists first, second; split; [exact Ha|]; split; [exists n; exact Hn|exact Hex].
  - intros [[execution [result [[start [-> _]] [Ho Hbody]]]]|
      [execution [result [[first [second [Ha [[n Hn] Hex]]]] [Ho Hbody]]]]].
    + exists [start;start], result; split; [exists 0, start; reflexivity|auto].
    + exists execution, result; split; [|auto]. exists (S n), first, second; auto.
Qed.

Lemma diamond_dual p a tr : tr <> [] ->
  (formula_holds (Diamond p a) tr <-> ~ formula_holds (Box p (Neg a)) tr).
Proof.
  intro Hne; destruct tr as [|s tail]; [contradiction|]; cbn [formula_holds].
  split.
  - intros [execution [result [Hp [Ho Ha]]]] Hbox.
    specialize (Hbox execution result Hp Ho).
    destruct (overlap_nonempty _ _ _ Ho) as [_ [_ Hresult]].
    destruct result; [contradiction|]. exact (Hbox Ha).
  - intro Hbox; apply not_all_ex_not in Hbox as [execution Hbox].
    apply not_all_ex_not in Hbox as [result Hbox].
    assert (program_holds p execution /\ overlap (s :: tail) execution result /\
      ~ formula_holds (Neg a) result) as [Hp [Ho Hbad]] by tauto.
    exists execution, result; split; [exact Hp|]; split; [exact Ho|].
    destruct (overlap_nonempty _ _ _ Ho) as [_ [_ Hresult]].
    destruct result; [contradiction|]. cbn [formula_holds] in Hbad; tauto.
Qed.

(** Instantiate the preceding trace equations at evaluated labels. These
    forms match the literal label trees in RULE_EXPANSIONS.md, including
    both the old and new assignment states and both copies of a test state. *)
Lemma assignment_label w sigma u x t body tag tag' :
  (labelled_holds w (Occ (Join sigma (StateLabel u)) (Box (Assign x t) body) tag) <->
   labelled_holds w (Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tag')).
Proof.
  unfold labelled_holds, label_admissible; cbn [occurrence_label occurrence_formula eval_label].
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
  unfold labelled_holds, label_admissible; cbn [occurrence_label occurrence_formula eval_label].
  rewrite diamond_assignment.
  assert (eval_label w sigma ++ [eval_update w u] <> []) by
    (intro H; apply app_eq_nil in H; destruct H; discriminate).
  assert ((eval_label w sigma ++ [eval_update w u]) ++
    [write (eval_update w u) x (eval_term (eval_update w u) t)] <> []) by
    (intro H'; apply app_eq_nil in H'; destruct H'; discriminate).
  tauto.
Qed.

Lemma box_test_label w sigma u guard body ta tb tg :
  labelled_holds w (Occ (Join sigma (StateLabel u)) (Box (Test guard) body) ta) <->
  (labelled_holds w (Occ (Join (StateLabel u) (StateLabel u)) guard tg) ->
   labelled_holds w (Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb)).
Proof.
  unfold labelled_holds, label_admissible; cbn [occurrence_label occurrence_formula eval_label].
  rewrite box_test.
  assert (eval_label w sigma ++ [eval_update w u] <> []) by
    (intro H; apply app_eq_nil in H; destruct H; discriminate).
  assert ((eval_label w sigma ++ [eval_update w u]) ++ [eval_update w u] <> []) by
    (intro H'; apply app_eq_nil in H'; destruct H'; discriminate).
  intuition discriminate.
Qed.

Lemma diamond_test_label w sigma u guard body ta tb tg :
  labelled_holds w (Occ (Join sigma (StateLabel u)) (Diamond (Test guard) body) ta) <->
  labelled_holds w (Occ (Join (StateLabel u) (StateLabel u)) guard tg) /\
  labelled_holds w (Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb).
Proof.
  unfold labelled_holds, label_admissible; cbn [occurrence_label occurrence_formula eval_label].
  rewrite diamond_test.
  assert (eval_label w sigma ++ [eval_update w u] <> []) by
    (intro H; apply app_eq_nil in H; destruct H; discriminate).
  assert ((eval_label w sigma ++ [eval_update w u]) ++ [eval_update w u] <> []) by
    (intro H'; apply app_eq_nil in H'; destruct H'; discriminate).
  intuition discriminate.
Qed.

(** [First] permits an arbitrary compound body at the singleton head. The
    following pure-head law instead needs purity; the public At rule uses
    its atom/equality special case. A compound temporal body cannot generally
    be moved to the head without the explicit [First] operator. *)
Lemma first_label w u sigma body tag tag' :
  labelled_holds w (Occ (Join (StateLabel u) sigma) (First body) tag) <->
  labelled_holds w (Occ (StateLabel u) body tag').
Proof.
  unfold labelled_holds, label_admissible; cbn [occurrence_label occurrence_formula eval_label formula_holds].
  split; intros [_ H]; split; try discriminate; exact H.
Qed.

Lemma pure_head_label w u sigma body tag tag' : pureb body = true ->
  (labelled_holds w (Occ (Join (StateLabel u) sigma) body tag) <->
   labelled_holds w (Occ (StateLabel u) body tag')).
Proof.
  intro Hp; unfold labelled_holds, label_admissible; cbn [occurrence_label occurrence_formula eval_label].
  rewrite (pure_singleton body (eval_update w u) (eval_label w sigma) Hp).
  split; intros [_ H]; split; try discriminate; exact H.
Qed.

Lemma proper_suffix_length a b : proper_suffix a b -> length a < length b.
Proof.
  intros [_ [prefix [Hp ->]]]. rewrite length_app.
  destruct prefix; [contradiction | cbn; lia].
Qed.

Lemma proper_suffix_step small s tail :
  proper_suffix small (s :: tail) <->
  (small = tail /\ tail <> []) \/ proper_suffix small tail.
Proof.
  split.
  - intros [Hne [prefix [Hp Heq]]]. destruct prefix as [|x prefix]; [contradiction|].
    cbn in Heq; injection Heq as Hsx Htail; subst x.
    destruct prefix as [|y prefix].
    + cbn in Htail; left; split; [symmetry; exact Htail|now rewrite Htail].
    + right; split; [exact Hne|]. exists (y :: prefix); split; [discriminate|exact Htail].
  - intros [[-> Hne]|[Hne [prefix [Hp ->]]]].
    + split; [exact Hne|]. exists [s]; split; [discriminate|reflexivity].
    + split; [exact Hne|]. exists (s :: prefix); split; [discriminate|reflexivity].
Qed.

Lemma proper_suffix_trans small middle big :
  proper_suffix small middle -> proper_suffix middle big -> proper_suffix small big.
Proof.
  intros [Hsmall [p [Hp ->]]] [_ [q [Hq ->]]].
  split; [exact Hsmall|]. exists (q ++ p); split.
  - intro H; apply app_eq_nil in H; tauto.
  - apply app_assoc.
Qed.

Lemma suffix_clause a b tr : tr <> [] ->
  (formula_holds (Suffix a b) tr <->
    exists suffix, proper_suffix suffix tr /\ formula_holds b suffix /\
      forall middle, proper_suffix suffix middle -> proper_suffix middle tr -> formula_holds a middle).
Proof. destruct tr; cbn; tauto. Qed.

(** One-state suffix unfolding: either [b] holds on the immediate tail, or
    [a] holds there and the same suffix obligation continues on that tail.
    The initial head state has no [a] obligation. The nonempty-tail premise
    separates this recurrence from the singleton boundary lemmas below. *)
Lemma suffix_step s tail a b : tail <> [] ->
  (formula_holds (Suffix a b) (s :: tail) <->
   formula_holds b tail \/ (formula_holds a tail /\ formula_holds (Suffix a b) tail)).
Proof.
  intro Hne. rewrite (suffix_clause a b tail Hne).
  cbn [formula_holds]. split.
  - intros [small [Hsmall [Hb Ha]]].
    apply proper_suffix_step in Hsmall as [[-> _]|Hproper]; [now left|].
    right; split.
    + apply (Ha tail); [exact Hproper|]. apply proper_suffix_step; auto.
    + exists small; split; [exact Hproper|]; split; [exact Hb|].
      intros middle Hsm Hmt. apply Ha; [exact Hsm|].
      apply proper_suffix_step; now right.
  - intros [Hb|[Ha [small [Hproper [Hb Hmiddle]]]]].
    + exists tail; split; [apply proper_suffix_step; auto|]. split; [exact Hb|].
      intros middle Htm Hms.
      pose proof (proper_suffix_length _ _ Htm).
      pose proof (proper_suffix_length _ _ Hms). cbn in *; lia.
    + exists small; split; [apply proper_suffix_step; now right|]. split; [exact Hb|].
      intros middle Hsm Hms. apply proper_suffix_step in Hms as [[-> _]|Hmt];
        [exact Ha|eapply Hmiddle; eauto].
Qed.

Lemma nonempty_neg a tr : tr <> [] ->
  (formula_holds (Neg a) tr <-> ~ formula_holds a tr).
Proof. destruct tr; cbn; tauto. Qed.

(** Make the negated dual definition usable as a rule equation; its later
    one-step law is obtained from suffix unfolding and classical logic. *)
Lemma dual_suffix_dual a b tr : tr <> [] ->
  (formula_holds (DualSuffix a b) tr <-> ~ formula_holds (Suffix (Neg a) (Neg b)) tr).
Proof.
  intro Hne; destruct tr as [|s tail]; [contradiction|]; cbn [formula_holds].
  assert ((exists small, proper_suffix small (s :: tail) /\ ~ formula_holds b small /\
    forall middle, proper_suffix small middle -> proper_suffix middle (s :: tail) -> ~ formula_holds a middle) <->
    (exists small, proper_suffix small (s :: tail) /\ formula_holds (Neg b) small /\
    forall middle, proper_suffix small middle -> proper_suffix middle (s :: tail) -> formula_holds (Neg a) middle)) as H.
  { split; intros [small [Hp [Hb Ha]]]; exists small; split; [exact Hp| |exact Hp|].
    - split; [apply nonempty_neg; [exact (proj1 Hp)|exact Hb]|].
      intros middle Hsm Hmt; apply nonempty_neg; [exact (proj1 Hmt)|eauto].
    - split; [apply nonempty_neg in Hb; [exact Hb|exact (proj1 Hp)]|].
      intros middle Hsm Hmt; specialize (Ha middle Hsm Hmt).
      apply nonempty_neg in Ha; [exact Ha|exact (proj1 Hmt)]. }
  tauto.
Qed.

Lemma dual_suffix_step s tail a b : tail <> [] ->
  (formula_holds (DualSuffix a b) (s :: tail) <->
   formula_holds b tail /\ (formula_holds a tail \/ formula_holds (DualSuffix a b) tail)).
Proof.
  intro Hne. rewrite dual_suffix_dual by discriminate.
  rewrite suffix_step by exact Hne.
  rewrite !nonempty_neg by exact Hne.
  rewrite (dual_suffix_dual a b tail Hne). tauto.
Qed.

Lemma suffix_label w u sigma a b ta tb tc td : label_nonemptyb sigma = true ->
  (labelled_holds w (Occ (Join (StateLabel u) sigma) (Suffix a b) ta) <->
    labelled_holds w (Occ sigma b tb) \/
    (labelled_holds w (Occ sigma a tc) /\ labelled_holds w (Occ sigma (Suffix a b) td))).
Proof.
  intro Hnonempty; apply (label_nonemptyb_spec w sigma) in Hnonempty.
  unfold label_admissible in Hnonempty.
  change (((eval_update w u :: eval_label w sigma) <> [] /\
    formula_holds (Suffix a b) (eval_update w u :: eval_label w sigma)) <->
    (eval_label w sigma <> [] /\ formula_holds b (eval_label w sigma)) \/
    ((eval_label w sigma <> [] /\ formula_holds a (eval_label w sigma)) /\
     (eval_label w sigma <> [] /\ formula_holds (Suffix a b) (eval_label w sigma)))).
  rewrite suffix_step by exact Hnonempty. intuition discriminate.
Qed.

Lemma dual_suffix_label w u sigma a b ta tb tc td : label_nonemptyb sigma = true ->
  (labelled_holds w (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta) <->
    labelled_holds w (Occ sigma b tb) /\
    (labelled_holds w (Occ sigma a tc) \/ labelled_holds w (Occ sigma (DualSuffix a b) td))).
Proof.
  intro Hnonempty; apply (label_nonemptyb_spec w sigma) in Hnonempty.
  unfold label_admissible in Hnonempty.
  change (((eval_update w u :: eval_label w sigma) <> [] /\
    formula_holds (DualSuffix a b) (eval_update w u :: eval_label w sigma)) <->
    (eval_label w sigma <> [] /\ formula_holds b (eval_label w sigma)) /\
    ((eval_label w sigma <> [] /\ formula_holds a (eval_label w sigma)) \/
     (eval_label w sigma <> [] /\ formula_holds (DualSuffix a b) (eval_label w sigma)))).
  rewrite dual_suffix_step by exact Hnonempty. intuition discriminate.
Qed.

Lemma no_singleton_suffix s suffix : ~ proper_suffix suffix [s].
Proof.
  intro H. pose proof (proper_suffix_length _ _ H).
  destruct H as [Hne _]. destruct suffix; [contradiction | cbn in *; lia].
Qed.

Lemma suffix_singleton a b s : ~ formula_holds (Suffix a b) [s].
Proof. cbn; intros [suffix [Hp _]]; now apply (no_singleton_suffix s suffix). Qed.

Lemma next_singleton a s : ~ formula_holds (Next a) [s].
Proof. apply suffix_singleton. Qed.

Lemma dual_suffix_singleton a b s : formula_holds (DualSuffix a b) [s].
Proof. cbn; intros [suffix [Hp _]]; now apply (no_singleton_suffix s suffix). Qed.

(** ** Freshness for the complete modal language

    A constant overwrite of a fresh variable can identify distinct states,
    so it cannot in general be reversed when transporting modal executions.
    Instead apply an involution [f] at that variable in every state. This
    transformation is its own inverse, preserves endpoint matches, and can
    transport executions in both directions. Later [swap_values] chooses an
    involution that installs a desired eigenvariable value at the head. *)
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
  - cbn [finite_power]; apply switch_compose; assumption.
Qed.

Lemma switch_box p a :
  (forall tr, program_holds p (map switch tr) <-> program_holds p tr) ->
  (forall tr, formula_holds a (map switch tr) <-> formula_holds a tr) -> forall tr,
  formula_holds (Box p a) (map switch tr) <-> formula_holds (Box p a) tr.
Proof.
  intros Hp Ha; apply switch_predicate_iff; intros tr Hbox.
  destruct tr as [|s tail]; [contradiction|]; cbn [map formula_holds] in *.
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
  destruct tr as [|s tail]; [contradiction|]; cbn [map formula_holds] in *.
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
  - intros Hfresh [|s tail]; reflexivity.
  - intros p args Hfresh [|s tail]; [reflexivity|]. cbn [map formula_holds].
    assert (map (eval_term (switch s)) args = map (eval_term s) args) as Heq.
    { apply map_ext_in; intros t Hin; apply switch_term.
      intro H; apply Hfresh; apply in_flat_map; exists t; auto. }
    now rewrite Heq.
  - intros a b Hfresh [|s tail]; [reflexivity|]. cbn [map formula_holds].
    rewrite !switch_term; try (intro H; apply Hfresh; apply in_app_iff; auto); reflexivity.
  - intros a IH Hfresh [|s tail]; [reflexivity|].
    change (~ formula_holds a (map switch (s :: tail)) <-> ~ formula_holds a (s :: tail)).
    now rewrite IH by exact Hfresh.
  - intros a Ha b Hb Hfresh [|s tail]; [reflexivity|].
    change ((formula_holds a (map switch (s :: tail)) /\ formula_holds b (map switch (s :: tail))) <->
      (formula_holds a (s :: tail) /\ formula_holds b (s :: tail))).
    rewrite Ha, Hb; try (intro H; apply Hfresh; apply in_app_iff; auto); tauto.
  - intros a Ha b Hb Hfresh [|s tail]; [reflexivity|].
    change ((formula_holds a (map switch (s :: tail)) \/ formula_holds b (map switch (s :: tail))) <->
      (formula_holds a (s :: tail) \/ formula_holds b (s :: tail))).
    rewrite Ha, Hb; try (intro H; apply Hfresh; apply in_app_iff; auto); tauto.
  - intros a Ha b Hb Hfresh [|s tail]; [reflexivity|].
    change ((formula_holds a (map switch (s :: tail)) -> formula_holds b (map switch (s :: tail))) <->
      (formula_holds a (s :: tail) -> formula_holds b (s :: tail))).
    rewrite Ha, Hb; try (intro H; apply Hfresh; apply in_app_iff; auto); tauto.
  - intros x a IH Hfresh tr.
    assert (x <> v) as Hx by (intro H; subst; apply Hfresh; now left).
    assert (~ In v (formula_vars a)) as Ha by (intro H; apply Hfresh; now right).
    destruct tr as [|s tail]; [reflexivity|]. cbn [formula_holds map].
    assert (forall d, map (fun s => write s x d) (map switch (s :: tail)) =
      map switch (map (fun s => write s x d) (s :: tail))) as Hmaps.
    { intro d; rewrite !map_map; apply map_ext; intro state'; symmetry; apply switch_write; exact Hx. }
    change ((forall d, formula_holds a (map (fun s => write s x d) (map switch (s :: tail)))) <->
      (forall d, formula_holds a (map (fun s => write s x d) (s :: tail)))).
    split; intros H d; specialize (H d).
    + rewrite Hmaps in H; apply (proj1 (IH Ha _)); exact H.
    + rewrite Hmaps; apply (proj2 (IH Ha _)); exact H.
  - intros x a IH Hfresh tr.
    assert (x <> v) as Hx by (intro H; subst; apply Hfresh; now left).
    assert (~ In v (formula_vars a)) as Ha by (intro H; apply Hfresh; now right).
    destruct tr as [|s tail]; [reflexivity|]. cbn [formula_holds map].
    assert (forall d, map (fun s => write s x d) (map switch (s :: tail)) =
      map switch (map (fun s => write s x d) (s :: tail))) as Hmaps.
    { intro d; rewrite !map_map; apply map_ext; intro state'; symmetry; apply switch_write; exact Hx. }
    change ((exists d, formula_holds a (map (fun s => write s x d) (map switch (s :: tail)))) <->
      (exists d, formula_holds a (map (fun s => write s x d) (s :: tail)))).
    split; intros [d H]; exists d.
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
  - intros a Ha b Hb Hfresh tr.
    assert (~ In v (formula_vars a) /\ ~ In v (formula_vars b)) as [Hfa Hfb]
      by (split; intro H; apply Hfresh; apply in_app_iff; auto).
    induction tr as [|s tail IH]; [reflexivity|]. destruct tail as [|t tail].
    + cbn [map]; split; intro H; apply dual_suffix_singleton.
    + change (formula_holds (DualSuffix a b) (switch s :: map switch (t :: tail)) <-> formula_holds (DualSuffix a b) (s :: t :: tail)).
      rewrite !dual_suffix_step by discriminate. rewrite Ha, Hb, IH by assumption; reflexivity.
  - intros p Hp a Ha Hfresh; apply switch_box;
      [apply Hp|apply Ha]; intro H; apply Hfresh; apply in_app_iff; auto.
  - intros p Hp a Ha Hfresh; apply switch_diamond;
      [apply Hp|apply Ha]; intro H; apply Hfresh; apply in_app_iff; auto.
  - intros x t Hfresh. apply switch_predicate_iff; intros tr [s ->].
    assert (x <> v) as Hx by (intro H; subst; apply Hfresh; now left).
    assert (~ In v (term_vars t)) as Ht by (intro H; apply Hfresh; now right).
    cbn [map]. exists (switch s). rewrite switch_write by exact Hx.
    rewrite switch_term by exact Ht; reflexivity.
  - intros a Ha Hfresh; apply switch_predicate_iff; intros tr [s [-> Hguard]].
    exists (switch s); split; [reflexivity|]. apply (proj2 (Ha Hfresh [s;s])); exact Hguard.
  - intros a Ha b Hb Hfresh; apply switch_compose;
      [apply Ha|apply Hb]; intro H; apply Hfresh; apply in_app_iff; auto.
  - intros a Ha b Hb Hfresh tr; cbn [program_holds].
    rewrite Ha, Hb; try (intro H; apply Hfresh; apply in_app_iff; auto); reflexivity.
  - intros a Ha Hfresh tr; cbn [program_holds].
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
  induction u; intro Hfresh; cbn [eval_update]; [reflexivity|].
  assert (x <> v) as Hx by (intro H; subst; apply Hfresh; now left).
  assert (~ In v (term_vars value)) as Ht by
    (intro H; apply Hfresh; right; apply in_app_iff; auto).
  assert (~ In v (update_vars u)) as Hu by
    (intro H; apply Hfresh; right; apply in_app_iff; auto).
  rewrite IHu by exact Hu; rewrite switch_term by exact Ht.
  symmetry; apply switch_write; exact Hx.
Qed.

Lemma switch_label w l : ~ In v (label_vars l) ->
  eval_label (switch_world w) l = map switch (eval_label w l).
Proof.
  induction l; intro Hfresh; cbn [eval_label]; try reflexivity.
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
  unfold labelled_holds, label_admissible; rewrite switch_label by exact Hl.
  rewrite (proj1 switch_semantics _ Ha).
  assert (map switch (eval_label w o.(occurrence_label)) <> [] <-> eval_label w o.(occurrence_label) <> []) as Hne.
  { split; intros H Heq; [apply H; now rewrite Heq|apply map_eq_nil in Heq; contradiction]. }
  tauto.
Qed.

Lemma switch_left_context w context :
  (forall o, In o context -> ~ In v (occurrence_vars o)) ->
  (left_holds (switch_world w) context <-> left_holds w context).
Proof.
  intro Hfresh; unfold left_holds; rewrite !Forall_forall.
  split; intros H o Hin.
  - apply (proj1 (switch_labelled w o (Hfresh o Hin))); apply H; exact Hin.
  - apply (proj2 (switch_labelled w o (Hfresh o Hin))); apply H; exact Hin.
Qed.

Lemma switch_right_context w context :
  (forall o, In o context -> ~ In v (occurrence_vars o)) ->
  (right_holds (switch_world w) context <-> right_holds w context).
Proof.
  intro Hfresh; unfold right_holds; split; intros [o [Hin Ho]]; exists o; split; try exact Hin.
  - apply (proj1 (switch_labelled w o (Hfresh o Hin))); exact Ho.
  - apply (proj2 (switch_labelled w o (Hfresh o Hin))); exact Ho.
Qed.

Lemma switch_denote w j : ~ In v (judgment_vars j) ->
  (denote j (switch_world w) <-> denote j w).
Proof.
  intro Hfresh.
  assert (forall o, In o (j.(antecedent) ++ j.(succedent)) -> ~ In v (occurrence_vars o)) as Hocc.
  { intros o Hin Hvar; apply Hfresh; apply in_flat_map; exists o; auto. }
  assert (admissible j (switch_world w) <-> admissible j w) as Hadm.
  { unfold admissible; rewrite !Forall_forall; split; intros H o Hin;
      specialize (H o Hin); unfold label_admissible in *;
      rewrite switch_label in * by (intro Hv; apply (Hocc o Hin); apply in_app_iff; auto).
    - intro Heq; apply H; now rewrite Heq.
    - intro Heq; apply map_eq_nil in Heq; contradiction. }
  assert (left_holds (switch_world w) j.(antecedent) <-> left_holds w j.(antecedent)) as Hl.
  { unfold left_holds; rewrite !Forall_forall; split; intros H o Hin;
      assert (~ In v (occurrence_vars o)) as Hfresh_o by (apply Hocc; apply in_app_iff; auto).
    - apply (proj1 (switch_labelled w o Hfresh_o)); apply H; exact Hin.
    - apply (proj2 (switch_labelled w o Hfresh_o)); apply H; exact Hin. }
  assert (right_holds (switch_world w) j.(succedent) <-> right_holds w j.(succedent)) as Hr.
  { unfold right_holds; split; intros [o [Hin Ho]]; exists o; split; try exact Hin;
      assert (~ In v (occurrence_vars o)) as Hfresh_o by (apply Hocc; apply in_app_iff; auto).
    - apply (proj1 (switch_labelled w o Hfresh_o)); exact Ho.
    - apply (proj2 (switch_labelled w o Hfresh_o)); exact Ho. }
  unfold denote; rewrite Hadm, Hl, Hr; reflexivity.
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
  rewrite subst_fo_correct by exact Hp. cbn [fol_holds]; eauto.
Qed.

(** For a pure observation, [Always] is exactly the observation at every
    visited state. The complex benchmarks use this to turn finite-trace
    safety induction into an object-language temporal validity theorem. *)
Lemma always_pure_forall a tr : pureb a = true -> tr <> [] ->
  (formula_holds (Always a) tr <-> Forall (fun s => formula_holds a [s]) tr).
Proof.
  intros Hp; induction tr as [|s tail IH]; intro Hne; [contradiction|].
  destruct tail as [|t tail].
  - unfold Always, Eventually; rewrite !nonempty_neg by discriminate.
    change (~ (~ formula_holds a [s] \/ formula_holds (Suffix Truth (Neg a)) [s]) <-> Forall (fun s => formula_holds a [s]) [s]).
    rewrite Forall_cons_iff. pose proof (suffix_singleton Truth (Neg a) s) as Hsuffix.
    split; [intro H; split; [tauto|constructor]|intros [H _]; tauto].
  - specialize (IH ltac:(discriminate)).
    unfold Always, Eventually in *.
    rewrite nonempty_neg in * by discriminate.
    change (~ (formula_holds (Neg a) (s :: t :: tail) \/
      formula_holds (Suffix Truth (Neg a)) (s :: t :: tail)) <-> Forall (fun s => formula_holds a [s]) (s :: t :: tail)).
    rewrite nonempty_neg, suffix_step by discriminate.
    rewrite nonempty_neg by discriminate.
    change (formula_holds Truth (t :: tail)) with True.
    rewrite (pure_singleton a s (t :: tail) Hp).
    change (~ (formula_holds (Neg a) (t :: tail) \/ formula_holds (Suffix Truth (Neg a)) (t :: tail)) <-> Forall (fun s => formula_holds a [s]) (t :: tail)) in IH.
    rewrite nonempty_neg in IH by discriminate.
    rewrite (pure_singleton a t tail Hp) in *.
    rewrite Forall_cons_iff. tauto.
Qed.

End Interpretation.

(** Package a chosen model for the later [ForModel] functors. This module
    type belongs to this particular syntax/semantics functor instance. *)
Module Type INTERPRETATION.
  Parameter interpretation : model.
End INTERPRETATION.
End MakeSemantics.
