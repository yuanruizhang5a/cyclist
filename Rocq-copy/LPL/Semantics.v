(** * Shallow semantics of the shared process logic.

    Frames may be infinite and nondeterministic. Only syntax is decidable.
    Extensions interpret recursive children over traces. Labels append;
    program executions overlap. T1: tests observe the two-state stutter. *)
From Stdlib Require Import List Bool Arith Lia Classical_Prop Classical_Pred_Type.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.ClassicalDescription.
From CyclistRocq.LPL Require Import Signature Syntax.
Import ListNotations.
Module MakeSemantics (L : LANGUAGE) (Syn : SYNTAX L).
Export Syn.
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

Record model : Type := Model {
  carrier : Type;
  carrier_inhabitant : carrier;
  interpret_atom : L.atom_symbol -> list L.argument -> carrier -> Prop;
  interpret_binary_atom : L.argument -> L.argument -> carrier -> Prop;
  interpret_extension : L.binder -> (list carrier -> Prop) -> list carrier -> Prop;
  interpret_coextension : L.binder -> (list carrier -> Prop) -> list carrier -> Prop;
  interpret_action : L.action_symbol -> L.action_argument -> carrier -> carrier -> Prop;
  interpret_atomic_trace : L.action_symbol -> L.action_argument -> list carrier -> Prop;
  atomic_trace_law : forall action payload tr, interpret_atomic_trace action payload tr <->
    exists s t, tr = [s;t] /\ interpret_action action payload s t;
  interpret_world_term : (nat -> carrier) -> L.world_term -> carrier;
  interpret_relation : L.relation_symbol -> list (list carrier) -> Prop;
  world_name_law : forall rho x, interpret_world_term rho (L.world_name x) = rho x;
  world_support_law : forall rho rho' u,
    (forall x, In x (L.world_support u) -> rho x = rho' x) ->
    interpret_world_term rho u = interpret_world_term rho' u;
  world_substitution_law : forall rho x replacement u,
    interpret_world_term rho (L.subst_world x replacement u) =
    interpret_world_term
      (fun y => if Nat.eqb x y then interpret_world_term rho replacement else rho y) u
}.
Section Interpretation.
Context (M : model).
Definition state := carrier M.
Definition trace := list state.
Record world : Type := World {
  world_mapping : nat -> state;
  trace_mapping : nat -> trace;
  trace_mapping_nonempty : forall x, trace_mapping x <> []
}.
Definition eval_update (w : world) (u : L.world_term) : state :=
  interpret_world_term M (world_mapping w) u.
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
  eval_update w (L.subst_world x replacement u) =
  eval_update (replace_world w x (eval_update w replacement)) u.
Proof. apply world_substitution_law. Qed.
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
  - cbn [replace_trace trace_mapping]. destruct (Nat.eqb x trace_variable); reflexivity.
  - now rewrite IHl1, IHl2.
Qed.

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
    | Atom p ts => interpret_atom M p ts s
    | BinaryAtom a b => interpret_binary_atom M a b s
    | Neg a => ~ formula_holds a tr
    | Conj a b => formula_holds a tr /\ formula_holds b tr
    | Disj a b => formula_holds a tr \/ formula_holds b tr
    | Impl a b => formula_holds a tr -> formula_holds b tr
    | Extension x a => interpret_extension M x (formula_holds a) tr
    | Coextension x a => interpret_coextension M x (formula_holds a) tr
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
  | Atomic x t => interpret_atomic_trace M x t tr
  | Test a => exists s, tr = [s; s] /\ formula_holds a [s; s]
  | Seq a b => compose (program_holds a) (program_holds b) tr
  | Choice a b => program_holds a tr \/ program_holds b tr
  | Star a => exists n, finite_power (program_holds a) n tr
  end.

Definition labelled_holds w o : Prop :=
  label_admissible w o.(occurrence_label) /\
  formula_holds o.(occurrence_formula) (eval_label w o.(occurrence_label)).
Definition relation_admissible w r := Forall (label_admissible w) (relation_labels r).
Definition relation_holds w r := match r with
  | ActionRelation action payload source target =>
      exists s t, eval_label w source = [s] /\ eval_label w target = [t] /\
        interpret_action M action payload s t
  | CustomRelation symbol arguments => interpret_relation M symbol (map (eval_label w) arguments)
  end.
Definition relations_hold w context := Forall (relation_holds w) context.
Definition admissible j w :=
  Forall (fun o => label_admissible w o.(occurrence_label)) (j.(antecedent) ++ j.(succedent)) /\
  Forall (relation_admissible w) j.(relations).
Definition left_holds w context := Forall (labelled_holds w) context.
Definition right_holds w context := exists o, In o context /\ labelled_holds w o.
Definition denote j w := admissible j w -> relations_hold w j.(relations) ->
  left_holds w j.(antecedent) -> right_holds w j.(succedent).
Definition Valid j := forall w, denote j w.
Lemma relation_mapping f w w' :
  (forall l, eval_label w (f l) = eval_label w' l) -> forall r,
  relation_holds w (map_relation f r) <-> relation_holds w' r.
Proof.
  intros H [a p s t|symbol arguments]; cbn [relation_holds map_relation].
  - now rewrite !H.
  - rewrite map_map. assert (map (fun l => eval_label w (f l)) arguments = map (eval_label w') arguments) as ->.
    { apply map_ext; exact H. } reflexivity.
Qed.
Lemma relation_admissible_mapping f w w' :
  (forall l, eval_label w (f l) = eval_label w' l) -> forall r,
  relation_admissible w (map_relation f r) <-> relation_admissible w' r.
Proof.
  intros H r; unfold relation_admissible. assert (relation_labels (map_relation f r) = map f (relation_labels r)) as -> by (destruct r; reflexivity).
  rewrite Forall_map, !Forall_forall. unfold label_admissible. setoid_rewrite H; reflexivity.
Qed.
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
  assert (relations_hold w (map (map_relation f) j.(relations)) <-> relations_hold w' j.(relations)) as Hrel.
  { unfold relations_hold; rewrite Forall_map, !Forall_forall; setoid_rewrite (relation_mapping f w w' Hmap); reflexivity. }
  assert (Forall (relation_admissible w) (map (map_relation f) j.(relations)) <-> Forall (relation_admissible w') j.(relations)) as Hra.
  { rewrite Forall_map, !Forall_forall; setoid_rewrite (relation_admissible_mapping f w w' Hmap); reflexivity. }
  unfold denote, admissible; cbn [map_labels antecedent succedent relations].
  rewrite <- map_app, Hadm, Hl, Hr, Hrel, Hra; reflexivity.
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
  unfold denote, admissible; cbn [rename_tags antecedent succedent relations]; rewrite <- map_app, Ha, Hl, Hr; reflexivity.
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
  unfold denote, admissible; cbn [erase_tags antecedent succedent relations]; rewrite <- map_app, Ha, Hl, Hr; reflexivity.
Qed.

Lemma backlink_eqb_denote a b w : backlink_eqb a b = true -> (denote a w <-> denote b w).
Proof.
  unfold backlink_eqb; intro Heq; apply judgment_eqb_spec in Heq.
  rewrite <- (denote_erase_tags a w), <- (denote_erase_tags b w); now rewrite Heq.
Qed.

Lemma valid_admissible j : Valid j <-> forall w, admissible j w ->
  relations_hold w j.(relations) -> left_holds w j.(antecedent) -> right_holds w j.(succedent).
Proof. reflexivity. Qed.
Lemma false_relations j w : ~ denote j w -> relations_hold w j.(relations).
Proof. unfold denote; tauto. Qed.
Lemma false_sequent j w : ~ denote j w ->
  admissible j w /\ left_holds w j.(antecedent) /\
  forall o, In o j.(succedent) -> ~ labelled_holds w o.
Proof.
  unfold denote, right_holds; intros H.
  assert (admissible j w) as Ha by tauto.
  assert (relations_hold w j.(relations)) as Hrel by tauto.
  assert (left_holds w j.(antecedent)) as Hl by tauto.
  split; [exact Ha|]. split; [exact Hl|].
  intros o Hin Ho. apply H; intros _ _ _; exists o; auto.
Qed.
Lemma judgment_wfb_admissible j w : judgment_wfb j = true -> admissible j w.
Proof.
  unfold judgment_wfb, admissible; rewrite !andb_true_iff.
  intros [[[Hrelations Hl] Hr] _]; split.
  - apply Forall_app; split; apply Forall_forall;
      intros o Hin; [apply forallb_forall with (x:=o) in Hl | apply forallb_forall with (x:=o) in Hr];
      try assumption; unfold occurrence_wfb in *;
      repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [H ?] end;
      apply label_nonemptyb_spec; assumption.
  - apply Forall_forall; intros r Hin.
    apply (proj1 (forallb_forall _ _) Hrelations r) in Hin.
    unfold relation_wfb in Hin; apply andb_true_iff in Hin as [_ Hlabels].
    unfold relation_admissible; apply Forall_forall; intros l Hmember.
    apply (proj1 (forallb_forall _ _) Hlabels l) in Hmember.
    apply andb_true_iff in Hmember as [_ Hne]; apply label_nonemptyb_spec; exact Hne.
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
  - apply atomic_trace_law in H. destruct H as [s [next [-> _]]]; cbn; lia.
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

Lemma atom_head_label w u sigma body tag tag' :
  (match body with Atom _ _ | BinaryAtom _ _ => true | _ => false end) = true ->
  (labelled_holds w (Occ (Join (StateLabel u) sigma) body tag) <->
   labelled_holds w (Occ (StateLabel u) body tag')).
Proof.
  destruct body; intro H; try discriminate;
    unfold labelled_holds, label_admissible;
    cbn [occurrence_label occurrence_formula eval_label formula_holds];
    split; intros [_ Hp]; split; try discriminate; exact Hp.
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
(** Fresh world names affect neither existing assertions nor relations. *)
Lemma eval_update_fresh w x value u : ~ In x (L.world_support u) ->
  eval_update (replace_world w x value) u = eval_update w u.
Proof.
  intro Hfresh; unfold eval_update; apply world_support_law.
  intros y Hin; cbn [replace_world world_mapping].
  destruct (Nat.eqb x y) eqn:Heq; [apply Nat.eqb_eq in Heq; subst; contradiction|reflexivity].
Qed.
Lemma eval_label_fresh w x value l : ~ In x (label_world_names l) ->
  eval_label (replace_world w x value) l = eval_label w l.
Proof.
  induction l; intro Hfresh; cbn [eval_label]; try reflexivity.
  - rewrite eval_update_fresh; [reflexivity|exact Hfresh].
  - rewrite IHl1, IHl2; try reflexivity; intro H; apply Hfresh; apply in_app_iff; auto.
Qed.
Lemma eval_fresh_name w x value :
  eval_update (replace_world w x value) (L.world_name x) = value.
Proof.
  unfold eval_update; rewrite world_name_law; cbn [replace_world world_mapping]; now rewrite Nat.eqb_refl.
Qed.
Lemma fresh_occurrence j x o : world_freshb x j = true ->
  In o (j.(antecedent) ++ j.(succedent)) -> ~ In x (label_world_names o.(occurrence_label)).
Proof.
  intros Hfresh Hin Hbad; apply world_freshb_spec in Hfresh; apply Hfresh.
  unfold judgment_world_names; apply in_app_iff; right; apply in_flat_map; exists o; auto.
Qed.
Lemma fresh_relation_label j x r l : world_freshb x j = true ->
  In r j.(relations) -> In l (relation_labels r) -> ~ In x (label_world_names l).
Proof.
  intros Hfresh Hr Hl Hbad; apply world_freshb_spec in Hfresh; apply Hfresh.
  unfold judgment_world_names; apply in_app_iff; left; apply in_flat_map; exists r; split; [exact Hr|].
  apply in_flat_map; exists l; auto.
Qed.
Lemma labelled_fresh w x value o : ~ In x (label_world_names o.(occurrence_label)) ->
  (labelled_holds (replace_world w x value) o <-> labelled_holds w o).
Proof. intro H; unfold labelled_holds, label_admissible; now rewrite eval_label_fresh. Qed.
Lemma relation_fresh w x value r :
  (forall l, In l (relation_labels r) -> ~ In x (label_world_names l)) ->
  (relation_holds (replace_world w x value) r <-> relation_holds w r).
Proof.
  destruct r as [a p source target|symbol args]; intro H; cbn [relation_holds].
  - rewrite !eval_label_fresh; try reflexivity; apply H; cbn; auto.
  - assert (map (eval_label (replace_world w x value)) args = map (eval_label w) args) as ->.
    { apply map_ext_in; intros l Hin; apply eval_label_fresh, H; exact Hin. }
    reflexivity.
Qed.
Lemma relations_fresh j w x value : world_freshb x j = true ->
  (relations_hold (replace_world w x value) j.(relations) <-> relations_hold w j.(relations)).
Proof.
  intro Hfresh; unfold relations_hold; rewrite !Forall_forall.
  split; intros H r Hin; specialize (H r Hin);
    assert (forall l, In l (relation_labels r) -> ~ In x (label_world_names l)) as Hlabels
      by (intros l Hl; eapply fresh_relation_label; eauto);
    apply (relation_fresh w x value r Hlabels); exact H.
Qed.
Lemma box_atomic prefix s action payload body :
  formula_holds (Box (Atomic action payload) body) (prefix ++ [s]) <->
  forall next, interpret_action M action payload s next ->
    formula_holds body ((prefix ++ [s]) ++ [next]).
Proof.
  assert (prefix ++ [s] <> []) as Hne by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  destruct (prefix ++ [s]) as [|head tail] eqn:Htr; [contradiction|].
  cbn [formula_holds]; split.
  - intros H next Hstep; eapply H.
    + cbn [program_holds]; apply atomic_trace_law; exists s, next; auto.
    + rewrite <- Htr; apply overlap_snoc; auto.
  - intros H execution result Hp Ho.
    cbn [program_holds] in Hp; apply atomic_trace_law in Hp.
    destruct Hp as [start [next [-> Hstep]]].
    rewrite <- Htr in Ho; apply overlap_snoc in Ho as [-> ->].
    rewrite Htr; apply H; exact Hstep.
Qed.
Lemma diamond_atomic prefix s action payload body :
  formula_holds (Diamond (Atomic action payload) body) (prefix ++ [s]) <->
  exists next, interpret_action M action payload s next /\
    formula_holds body ((prefix ++ [s]) ++ [next]).
Proof.
  assert (prefix ++ [s] <> []) as Hne by (intro H; apply app_eq_nil in H; destruct H; discriminate).
  destruct (prefix ++ [s]) as [|head tail] eqn:Htr; [contradiction|].
  cbn [formula_holds]; split.
  - intros [execution [result [Hp [Ho Hbody]]]].
    cbn [program_holds] in Hp; apply atomic_trace_law in Hp.
    destruct Hp as [start [next [-> Hstep]]].
    rewrite <- Htr in Ho; apply overlap_snoc in Ho as [-> ->].
    exists next; split; [exact Hstep|]. rewrite Htr in Hbody; exact Hbody.
  - intros [next [Hstep Hbody]].
    exists [s;next], ((head::tail) ++ [next]); split.
    + cbn [program_holds]; apply atomic_trace_law; exists s, next; auto.
    + split; [rewrite <- Htr; apply overlap_snoc; auto|exact Hbody].
Qed.

End Interpretation.
Module Type INTERPRETATION.
  Parameter interpretation : model.
End INTERPRETATION.
End MakeSemantics.
Module Type SEMANTICS (L : LANGUAGE) (Syn : SYNTAX L).
  Include MakeSemantics L Syn.
End SEMANTICS.
