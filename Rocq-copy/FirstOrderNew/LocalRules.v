From Stdlib Require Import List Bool Arith String Lia Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription Logic.ClassicalEpsilon.
From CyclistRocq.FirstOrderNew Require Export Simplification.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** Local certificates use classical descriptions only to select a failed
    premise. All syntactic checks and occurrence maps are constructive. *)
Lemma counter_world d j w : ~ denote d j w ->
  active_holds d j w /\ ~ eval_right d (world_model w) (world_valuation w) (succedent j).
Proof.
  unfold denote; intro H; split.
  - apply NNPP; intro Hn; apply H; contradiction.
  - intro Hr; apply H; auto.
Qed.

Lemma bounded_nth d m rho bs start p : bounded_product d m rho bs start p <->
  forall i a, nth_error p i = Some a ->
    eval_atom_with m (stage d m (bs (start + i))) rho a.
Proof.
  revert start; induction p as [|a p IH]; intros start; cbn.
  - split; [intros _ [|i] b H; discriminate|auto].
  - split.
    + intros [Ha Hp] [|i] b H; cbn in H.
      * inversion H; subst; now rewrite Nat.add_0_r.
      * replace (start + S i) with (S start + i) by lia.
        apply (proj1 (IH _) Hp i b H).
    + intro H; split.
      * specialize (H 0 a eq_refl); now rewrite Nat.add_0_r in H.
      * apply IH; intros i b Hi.
        replace (S start + i) with (start + S i) by lia; apply H; exact Hi.
Qed.

Lemma eval_atom_stage_irrelevant d m rho n a : atom_tag a = None ->
  eval_atom d m rho a -> eval_atom_with m (stage d m n) rho a.
Proof. destruct a; cbn; intros; try discriminate; assumption. Qed.

Lemma eval_term_agreement m rho sigma t :
  (forall x, In x (term_vars t) -> rho x = sigma x) ->
  eval_term m rho t = eval_term m sigma t.
Proof.
  induction t using term_induction; cbn; intro He; try reflexivity.
  - apply He; now left.
  - f_equal; apply map_ext_in; intros t Ht.
    apply Forall_forall with (x := t) in H; [|exact Ht].
    apply H; intros x Hx; apply He.
    apply in_concat; exists (term_vars t); split; [now apply in_map|exact Hx].
Qed.
Lemma eval_atom_agreement m r rho sigma a :
  (forall x, In x (atom_vars a) -> rho x = sigma x) ->
  (eval_atom_with m r rho a <-> eval_atom_with m r sigma a).
Proof.
  destruct a; cbn; intro H.
  - rewrite (eval_term_agreement m rho sigma left),
      (eval_term_agreement m rho sigma right); try reflexivity;
      intros; apply H; apply in_or_app; auto.
  - rewrite (eval_term_agreement m rho sigma left),
      (eval_term_agreement m rho sigma right); try reflexivity;
      intros; apply H; apply in_or_app; auto.
  - assert (E : map (eval_term m rho) arguments = map (eval_term m sigma) arguments).
    { apply map_ext_in; intros t Ht; apply eval_term_agreement; intros x Hx.
      apply H; apply in_concat; exists (term_vars t); split; [now apply in_map|exact Hx]. }
    now rewrite E.
Qed.
Lemma eval_product_agreement d m rho sigma p :
  (forall x, In x (product_vars p) -> rho x = sigma x) ->
  eval_product d m rho p -> eval_product d m sigma p.
Proof.
  intros He Hp; apply Forall_forall; intros a Ha.
  assert (HaE : forall x, In x (atom_vars a) -> rho x = sigma x).
  { intros x Hx; apply He; apply in_concat; exists (atom_vars a); split;
      [now apply in_map|exact Hx]. }
  apply (proj1 (eval_atom_agreement m (inductive_relation d m) rho sigma a HaE)).
  apply Forall_forall with (x := a) in Hp; auto.
Qed.

Lemma rhs_cover_sound d m rho f g :
  forallb (fun q => existsb (fun p => product_subset p q) f) g = true ->
  eval_right d m rho g -> eval_right d m rho f.
Proof.
  intros H [q [Hq [sigma [Hfree Htruth]]]].
  apply forallb_forall with (x := q) in H; [|exact Hq].
  apply existsb_exists in H; destruct H as [p [Hp Hsub]].
  exists p; split; [exact Hp|]; exists sigma; split; [exact Hfree|].
  eapply product_subset_sound; eauto.
Qed.

(** A target occurrence has exactly one source position; distinct targets may
    use the same source. This preserves multiplicities under substitution. *)
Fixpoint find_logical a p : option nat :=
  match p with [] => None | b :: p' =>
    if atom_logical_eqb a b then Some 0 else option_map S (find_logical a p') end.
Lemma find_logical_spec a p i : find_logical a p = Some i ->
  exists b, nth_error p i = Some b /\ atom_logical_eqb a b = true.
Proof.
  revert i; induction p as [|b p IH]; intros i; cbn; [discriminate|].
  destruct (atom_logical_eqb a b) eqn:E.
  - intro H; inversion H; subst; exists b; auto.
  - destruct (find_logical a p) as [n|] eqn:F; cbn; [|discriminate].
    intro H; inversion H; subst; destruct (IH n eq_refl) as [c [Hc Hac]].
    exists c; auto.
Qed.
Fixpoint find_unused start used a p : option nat :=
  match p with [] => None | b :: p' =>
    if atom_logical_eqb a b && negb (existsb (Nat.eqb start) used) then Some 0
    else option_map S (find_unused (S start) used a p') end.
Lemma find_unused_spec start used a p i : find_unused start used a p = Some i ->
  exists b, nth_error p i = Some b /\ atom_logical_eqb a b = true.
Proof.
  revert start i; induction p as [|b p IH]; intros start i; cbn; [discriminate|].
  destruct (atom_logical_eqb a b && negb (existsb (Nat.eqb start) used)) eqn:E.
  - intro H; inversion H; subst; apply andb_true_iff in E; exists b; tauto.
  - destruct (find_unused (S start) used a p) as [n|] eqn:F; cbn; [|discriminate].
    intro H; inversion H; subst; destruct (IH (S start) n F) as [c [Hc Hac]]; exists c; auto.
Qed.
Definition choose_occurrence p used a := match find_unused 0 used a p with
  | Some i => Some i | None => find_logical a p end.
Lemma choose_occurrence_spec p used a i : choose_occurrence p used a = Some i ->
  exists b, nth_error p i = Some b /\ atom_logical_eqb a b = true.
Proof.
  unfold choose_occurrence; destruct (find_unused 0 used a p) as [n|] eqn:E.
  - intro H; inversion H; subst; now apply find_unused_spec in E.
  - apply find_logical_spec.
Qed.
(** Prefer unused source occurrences so administrative normalization keeps
    duplicate predicates distinct. Reuse is needed only for contraction. *)
Fixpoint occurrence_map_from p q used : option (list nat) :=
  match q with [] => Some [] | a :: q' =>
    match (match atom_tag a with None => Some 0 | Some _ => choose_occurrence p used a end) with
    | Some i => match occurrence_map_from p q'
        (match atom_tag a with None => used | Some _ => i :: used end) with
      | Some is => Some (i :: is) | None => None end
    | None => None end end.
Definition occurrence_map p q := occurrence_map_from p q [].
Lemma occurrence_map_from_spec p q used is : occurrence_map_from p q used = Some is ->
  List.length is = List.length q /\
  forall n a, nth_error q n = Some a -> atom_tag a <> None ->
    exists i b, nth_error is n = Some i /\ nth_error p i = Some b /\
      atom_logical_eqb a b = true.
Proof.
  revert used is; induction q as [|a q IH]; intros used is; cbn.
  - intro H; inversion H; subst; split; [reflexivity|intros [|n] b Hn; discriminate].
  - destruct (match atom_tag a with None => Some 0 | Some _ => choose_occurrence p used a end)
      as [i|] eqn:E; [|discriminate].
    destruct (occurrence_map_from p q (match atom_tag a with None => used | Some _ => i::used end))
      as [js|] eqn:F; [|discriminate].
    intro H; inversion H; subst; destruct (IH _ js F) as [Hlen Hspec].
    split; [cbn; now rewrite Hlen|]. intros [|n] b Hb Htag; cbn in Hb.
    + inversion Hb; subst b. destruct (atom_tag a) eqn:T; [|contradiction].
      destruct (choose_occurrence_spec p used a i E) as [c [Hc Hac]].
      exists i,c; auto.
    + destruct (Hspec n b Hb Htag) as [k [c [Hk [Hc Hbc]]]].
      exists k,c; auto.
Qed.
Lemma occurrence_map_spec p q is : occurrence_map p q = Some is ->
  List.length is = List.length q /\
  forall n a, nth_error q n = Some a -> atom_tag a <> None ->
    exists i b, nth_error is n = Some i /\ nth_error p i = Some b /\
      atom_logical_eqb a b = true.
Proof. apply occurrence_map_from_spec. Qed.
Definition occurrence_map_dec p q :
  { is : list nat | occurrence_map p q = Some is } + { occurrence_map p q = None }.
Proof.
  destruct (occurrence_map p q) as [is|] eqn:E;
    [left; exists is; reflexivity|right; reflexivity].
Defined.
Definition occurrence_edge q is :=
  {| continuations := flat_map (fun na => match atom_tag (snd na) with
       | Some _ => [(nth (fst na) is 0, fst na)] | None => [] end)
       (combine (seq 0 (List.length q)) q);
     progressing := [] |}.
Lemma occurrence_edge_spec q is a b :
  In (a,b) (continuations (occurrence_edge q is)) -> a = nth b is 0.
Proof.
  cbn; rewrite in_flat_map; intros [na [_ H]].
  destruct (atom_tag (snd na)); cbn in H; [|contradiction].
  destruct H as [H|H]; [inversion H; reflexivity|contradiction].
Qed.
Lemma nth_error_nth_nat (xs : list nat) n x : nth_error xs n = Some x -> nth n xs 0 = x.
Proof. intro H; eapply nth_error_nth; exact H. Qed.
Lemma bounded_occurrence_map d m rho bs p q is :
  occurrence_map p q = Some is ->
  eval_product d m rho q -> bounded_product d m rho bs 0 p ->
  bounded_product d m rho (fun n => bs (nth n is 0)) 0 q.
Proof.
  intros Hmap Hq Hp; apply bounded_nth; intros n a Hn; cbn.
  destruct (atom_tag a) eqn:T.
  - destruct (proj2 (occurrence_map_spec p q is Hmap) n a Hn)
      as [i [b [Hi [Hb Heq]]]]; [congruence|].
    rewrite (nth_error_nth_nat is n i Hi).
    pose proof (proj1 (bounded_nth d m rho bs 0 p) Hp i b Hb) as Hstage.
    apply eqb_of_dec_spec in Heq; destruct a, b; cbn in Heq, T, Hstage |- *;
      try discriminate; inversion Heq; subst; exact Hstage.
  - apply (eval_atom_stage_irrelevant d m rho (bs (nth n is 0)) a); [exact T|].
    apply Forall_forall with (x := a) in Hq; [exact Hq|].
    eapply nth_error_In; exact Hn.
Qed.

Lemma eval_subst_atom_with m r s rho a :
  eval_atom_with m r rho (subst_atom s a) <->
  eval_atom_with m r (subst_valuation m s rho) a.
Proof.
  destruct a; cbn; try (rewrite !eval_subst_term; reflexivity).
  rewrite map_map; assert (E : map (fun t => eval_term m rho (subst_term s t)) arguments =
    map (eval_term m (subst_valuation m s rho)) arguments).
  { apply map_ext; apply eval_subst_term. } now rewrite E.
Qed.
Lemma bounded_subst d m s rho bs start p :
  bounded_product d m rho bs start (subst_product s p) <->
  bounded_product d m (subst_valuation m s rho) bs start p.
Proof.
  revert start; induction p as [|a p IH]; intros start; cbn; [tauto|].
  rewrite eval_subst_atom_with, IH; reflexivity.
Qed.
Lemma subst_offset s f i :
  List.length (List.concat (firstn i (subst_formula s f))) =
  List.length (List.concat (firstn i f)).
Proof.
  revert i; induction f as [|p f IH]; intros [|i]; cbn; auto.
  rewrite !length_app, subst_product_length, IH; reflexivity.
Qed.
Lemma lookup_exist_free s n : substitution_freeb s = true -> lookup s (Exist n) = Var (Exist n).
Proof.
  induction s as [|[x t] s IH]; cbn; [reflexivity|].
  rewrite !andb_true_iff; intros [[Hx Ht] Hs]; destruct x; cbn in Hx; [|discriminate].
  unfold variable_eqb, eqb_of_dec; destruct (variable_eq_dec (Exist n) (Free id));
    [discriminate|now apply IH].
Qed.
Lemma lookup_free_vars s n : substitution_freeb s = true ->
  forallb is_free (term_vars (lookup s (Free n))) = true.
Proof.
  induction s as [|[x t] s IH]; cbn; [reflexivity|].
  rewrite !andb_true_iff; intros [[Hx Ht] Hs].
  destruct (variable_eqb (Free n) x); [exact Ht|now apply IH].
Qed.
Lemma eval_term_free m rho sigma t : agrees_free m rho sigma ->
  forallb is_free (term_vars t) = true -> eval_term m sigma t = eval_term m rho t.
Proof.
  intros Hfree Hvars; apply eval_term_agreement; intros x Hx.
  apply forallb_forall with (x := x) in Hvars; [|exact Hx].
  destruct x; [apply Hfree|discriminate].
Qed.
Lemma right_free_substitution d m s rho f : substitution_freeb s = true ->
  eval_right d m (subst_valuation m s rho) f -> eval_right d m rho (subst_formula s f).
Proof.
  intros Hs [p [Hp [sigma [Hfree Htruth]]]].
  set (tau := fun x => match x with Free _ => rho x | Exist _ => sigma x end).
  assert (Htau : agrees_free m rho tau) by (intro n; reflexivity).
  assert (He : forall x, subst_valuation m s tau x = sigma x).
  { intros [n|n]; unfold subst_valuation.
    - rewrite (eval_term_free m rho tau _ Htau (lookup_free_vars s n Hs)).
      symmetry; apply Hfree.
    - rewrite lookup_exist_free by exact Hs; reflexivity. }
  exists (subst_product s p); split; [now apply in_map|].
  exists tau; split; [exact Htau|]; apply eval_subst_product.
  eapply eval_product_agreement; [intros x _; symmetry; apply He|exact Htruth].
Qed.
Definition existential_substitutionb (s : substitution) := forallb (fun xt => negb (is_free (fst xt))) s.
Lemma lookup_free_exist s n : existential_substitutionb s = true -> lookup s (Free n) = Var (Free n).
Proof.
  induction s as [|[x t] s IH]; cbn; [reflexivity|].
  rewrite andb_true_iff; intros [Hx Hs]; destruct x; cbn in Hx; [discriminate|].
  unfold variable_eqb, eqb_of_dec; destruct (variable_eq_dec (Free n) (Exist id));
    [discriminate|now apply IH].
Qed.
Lemma right_existential_instance d m rho s p : existential_substitutionb s = true ->
  (exists sigma, agrees_free m rho sigma /\ eval_product d m sigma (subst_product s p)) ->
  exists sigma, agrees_free m rho sigma /\ eval_product d m sigma p.
Proof.
  intros Hs [sigma [Hfree Hp]]; exists (subst_valuation m s sigma); split.
  - intros n; unfold subst_valuation; rewrite lookup_free_exist by exact Hs; apply Hfree.
  - now apply eval_subst_product in Hp.
Qed.

Definition singleton_label p f := {| antecedent := [p]; succedent := f |}.
Definition singleton_transport d (name : string) p q f g is
  (Hmap : occurrence_map p q = Some is)
  (Hl : forall m rho, eval_product d m rho p -> eval_product d m rho q)
  (Hr : forall m rho, eval_product d m rho p ->
    eval_right d m rho g -> eval_right d m rho f) :
  certified_application d (singleton_label p f).
Proof.
  refine {| certified_rule := unary_application name (singleton_label p f)
    (singleton_label q g) (occurrence_edge q is); certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; destruct (counter_world d _ _ Hbad) as [Ha Hf].
  destruct (constructive_indefinite_description _ Ha) as [a [Hi Hp]].
  destruct (active_product w) as [|n] eqn:E;
    cbn in Hi; [inversion Hi; subst a|destruct n; discriminate].
  unfold active_offset in Hp; cbn in Hp; rewrite E in Hp; cbn in Hp.
  pose proof (bounded_product_forget d _ _ _ _ _ Hp) as Htruth.
  exists 0; eexists; exists {| world_model := world_model w;
    world_valuation := world_valuation w; active_product := 0;
    world_bounds := fun n => world_bounds w (nth n is 0) |}.
  split; [reflexivity|]; split.
  - intro Hden; apply Hf; apply Hr; [exact Htruth|]; apply Hden.
    exists q; split; [reflexivity|]; cbn; apply bounded_occurrence_map with (p := p);
      auto.
  - split; cbn [respects rank occurrence_edge progressing]; [|contradiction].
    intros a b Hab; pose proof (occurrence_edge_spec q is a b Hab) as ->; apply Nat.le_refl.
Defined.

(** Exact atom matching (modulo semantically irrelevant logical tags), not
    variable matching, implements exchange and both directions of weakening. *)
Definition checked_weakening d (j k : sequent) : option (certified_application d j).
Proof.
  destruct j as [f g], k as [h l].
  destruct f as [|p f]; [exact None|]. destruct f as [|p' f]; [|exact None].
  destruct h as [|q h]; [exact None|]. destruct h as [|q' h]; [|exact None].
  destruct (Bool.bool_dec (product_subset q p) true) as [Hl|]; [|exact None].
  destruct (Bool.bool_dec (forallb (fun a => existsb (fun b => product_subset b a) g) l) true)
    as [Hr|]; [|exact None].
  destruct (occurrence_map_dec p q) as [[is Hmap]|]; [|exact None].
  refine (Some (singleton_transport d "Weak/Exchange" p q g l is Hmap _ _)).
  - intros; eapply product_subset_sound; eauto.
  - intros m rho _ Hright; eapply rhs_cover_sound; eauto.
Defined.

(** Reverse substitution is checked only for Free -> free-term substitutions.
    Existential renamings require an injective, scope-preserving matcher and
    are deliberately outside this checked API. *)
Definition backward_substitution d s k (Hs : substitution_freeb s = true) :
  certified_application d (subst_sequent s k).
Proof.
  refine {| certified_rule := unary_application "Subst" (subst_sequent s k) k (identity_trace k);
    certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; destruct (counter_world d _ _ Hbad) as [Ha Hr].
  destruct (constructive_indefinite_description _ Ha) as [q [Hq Htruth]].
  assert (Hinv : exists p, nth_error (antecedent k) (active_product w) = Some p /\
    q = subst_product s p).
  { change (nth_error (map (subst_product s) (antecedent k)) (active_product w) = Some q) in Hq.
    rewrite nth_error_map in Hq.
    destruct (nth_error (antecedent k) (active_product w)) as [p|] eqn:Hp.
    - exists p; split; [reflexivity|].
      assert (E : Some (subst_product s p) = Some q).
      { exact (eq_trans (eq_sym (f_equal (option_map (subst_product s)) Hp)) Hq). }
      now inversion E.
    - assert (E : @None product = Some q).
      { exact (eq_trans (eq_sym (f_equal (option_map (subst_product s)) Hp)) Hq). }
      discriminate. }
  destruct (constructive_indefinite_description _ Hinv) as [p [Hp ->]].
  exists 0; eexists; exists {| world_model := world_model w;
    world_valuation := subst_valuation (world_model w) s (world_valuation w);
    active_product := active_product w; world_bounds := world_bounds w |}.
  split; [reflexivity|]; split.
  - intro Hden; apply Hr; apply right_free_substitution; [exact Hs|]; apply Hden.
    exists p; split; [exact Hp|].
    unfold active_offset in *; cbn in *; rewrite subst_offset in Htruth.
    now apply bounded_subst in Htruth.
  - split; cbn [identity_trace progressing]; [|contradiction].
    intros a b Hab; apply in_map_iff in Hab; destruct Hab as [n [Hn _]].
    inversion Hn; subst; apply Nat.le_refl.
Defined.
Definition checked_backward_substitution d s k : option (certified_application d (subst_sequent s k)) :=
  match Bool.bool_dec (substitution_freeb s) true with
  | left H => Some (backward_substitution d s k H) | right _ => None end.

(** The first unary certificate targets [subst_sequent s companion]; the
    second targets [companion]. The caller composes their trace edges. *)
Definition backlink_prefix d j companion s :
  option (certified_application d j * certified_application d (subst_sequent s companion)) :=
  match checked_weakening d j (subst_sequent s companion),
        checked_backward_substitution d s companion with
  | Some weakening, Some substitution => Some (weakening, substitution)
  | _, _ => None end.

Lemma local_nth_combine {A B} (xs : list A) (ys : list B) n x y :
  nth_error xs n = Some x -> nth_error ys n = Some y ->
  nth_error (combine xs ys) n = Some (x,y).
Proof.
  revert xs ys; induction n as [|n IH]; intros [|a xs] [|b ys]; cbn;
    intros Hx Hy; try discriminate; [now inversion Hx; inversion Hy|now apply IH].
Qed.
Lemma local_nth_seq start len n : n < len -> nth_error (seq start len) n = Some (start+n).
Proof.
  revert start len; induction n as [|n IH]; intros start [|len] H; cbn; try lia.
  - now rewrite Nat.add_0_r.
  - replace (start + S n) with (S start + n) by lia; apply IH; lia.
Qed.

Definition left_disjunction d j : certified_application d j.
Proof.
  refine {| certified_rule := {| application_name := "OrL"; conclusion := j;
    premises := map (fun ip => {| premise_label := singleton_label (snd ip) (succedent j);
      premise_trace := {| continuations := map (fun n =>
        (List.length (List.concat (firstn (fst ip) (antecedent j))) + n, n))
        (trace_tags (singleton_label (snd ip) (succedent j))); progressing := [] |} |})
      (combine (seq 0 (List.length (antecedent j))) (antecedent j)) |};
    certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; destruct (counter_world d j w Hbad) as [Ha Hr].
  destruct (constructive_indefinite_description _ Ha) as [p [Hi Hp]].
  set (i := active_product w).
  assert (Hlen : i < List.length (antecedent j)).
  { apply nth_error_Some; unfold i; rewrite Hi; discriminate. }
  assert (Hpair : nth_error (combine (seq 0 (List.length (antecedent j))) (antecedent j)) i
    = Some (i,p)).
  { apply local_nth_combine; [apply (local_nth_seq 0 _ _ Hlen)|exact Hi]. }
  exists i; eexists; exists {| world_model := world_model w;
    world_valuation := world_valuation w; active_product := 0;
    world_bounds := fun n => world_bounds w (active_offset j w + n) |}.
  split.
  - cbn; rewrite nth_error_map, Hpair; reflexivity.
  - split.
    + intro Hden; apply Hr; apply Hden; exists p; split; [reflexivity|].
      cbn; apply bounded_nth; intros n a Hn; cbn.
      apply (proj1 (bounded_nth d _ _ _ _ _) Hp n a Hn).
    + split; cbn; [|contradiction]. intros a b Hab.
      apply in_map_iff in Hab; destruct Hab as [n [Heq Hn]]; inversion Heq; subst.
      unfold rank, active_offset, i; apply Nat.le_refl.
Defined.

Definition same_left_transport d (name : string) j g
  (Hr : forall m rho, eval_formula d m rho (antecedent j) ->
    eval_right d m rho g -> eval_right d m rho (succedent j)) : certified_application d j.
Proof.
  refine {| certified_rule := unary_application name j
    {| antecedent := antecedent j; succedent := g |} (identity_trace j);
    certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; destruct (counter_world d j w Hbad) as [Ha Hright].
  exists 0; eexists; exists w; split; [reflexivity|]; split.
  - intro Hden; apply Hright; apply Hr; [|apply Hden; exact Ha].
    destruct Ha as [p [Hp Htruth]]; exists p; split;
      [eapply nth_error_In; exact Hp|eapply bounded_product_forget; exact Htruth].
  - split; cbn [identity_trace progressing]; [|contradiction].
    intros a b H; apply in_map_iff in H; destruct H as [n [E _]];
      inversion E; subst; apply Nat.le_refl.
Defined.

Lemma first_some_spec {A B} (f : A -> option B) xs y : first_some f xs = Some y ->
  exists x, In x xs /\ f x = Some y.
Proof.
  induction xs as [|x xs IH]; cbn; [discriminate|].
  destruct (f x) as [z|] eqn:E.
  - intro H; inversion H; subst; exists x; auto.
  - intro H; destruct (IH H) as [a [Ha Ea]]; exists a; auto.
Qed.
Lemma without_trivial_equiv d m rho p :
  eval_product d m rho (without_trivial p) <-> eval_product d m rho p.
Proof.
  split; intro H; apply Forall_forall; intros a Ha.
  - destruct (reflexive_eqb a) eqn:E.
    + destruct a; cbn in E; try discriminate; apply eqb_of_dec_spec in E; subst; reflexivity.
    + apply Forall_forall with (x := a) in H; [exact H|].
      apply filter_In; split; [exact Ha|now rewrite E].
  - apply filter_In in Ha; apply Forall_forall with (x := a) in H; tauto.
Qed.
Lemma without_trivial_right d m rho f :
  eval_right d m rho (map without_trivial f) -> eval_right d m rho f.
Proof.
  intros [q [Hq [sigma [Hfree Htruth]]]]; apply in_map_iff in Hq.
  destruct Hq as [p [<- Hp]]; exists p; split; [exact Hp|].
  exists sigma; split; [exact Hfree|]; exact (proj1 (without_trivial_equiv d m sigma p) Htruth).
Qed.
Definition checked_singleton_change d (name : string) p q f g
  (Hl : forall m rho, eval_product d m rho p -> eval_product d m rho q)
  (Hr : forall m rho, eval_product d m rho p -> eval_right d m rho g -> eval_right d m rho f) :
  option (certified_application d (singleton_label p f)) :=
  match occurrence_map p q as result return occurrence_map p q = result ->
    option (certified_application d (singleton_label p f)) with
  | Some is => fun H => Some (singleton_transport d name p q f g is H Hl Hr)
  | None => fun _ => None end eq_refl.
Definition trivial_equality_rule d (j : sequent) : option (certified_application d j).
Proof.
  destruct j as [f g]; destruct f as [|p f]; [exact None|].
  destruct f as [|p' f]; [|exact None].
  refine (checked_singleton_change d "simplAllTaut" p (without_trivial p) g (map without_trivial g) _ _).
  - intros m rho H; exact (proj2 (without_trivial_equiv d m rho p) H).
  - intros m rho _; apply without_trivial_right.
Defined.

Lemma replace_product_right d m rho f p s : In p f -> existential_substitutionb s = true ->
  eval_right d m rho (replace_product p (subst_product s p) f) -> eval_right d m rho f.
Proof.
  intros Hp Hs [q [Hq [sigma [Hfree Htruth]]]].
  destruct Hq as [Hq|Hq].
  - subst q; exists p; split; [exact Hp|]; apply right_existential_instance with (s := s);
      [exact Hs|exists sigma; auto].
  - apply filter_In in Hq; exists q; split; [tauto|exists sigma; auto].
Qed.
Definition rhs_existential_instantiation d j p s (Hp : In p (succedent j))
  (Hs : existential_substitutionb s = true) : certified_application d j :=
  same_left_transport d "ExR" j (replace_product p (subst_product s p) (succedent j))
    (fun m rho _ => replace_product_right d m rho (succedent j) p s Hp Hs).
Definition checked_rhs_instantiation d j p s : option (certified_application d j) :=
  match in_dec product_eq_dec p (succedent j), Bool.bool_dec (existential_substitutionb s) true with
  | left Hp, left Hs => Some (rhs_existential_instantiation d j p s Hp Hs)
  | _, _ => None end.
Lemma ex_binding_exist a v t : ex_binding a = Some (v,t) -> is_free v = false.
Proof.
  destruct a; try discriminate; destruct right; destruct left;
    try destruct name; try destruct name0; cbn; intro H; try discriminate;
    inversion H; reflexivity.
Qed.
Definition right_equality_rule d j : option (certified_application d j).
Proof.
  destruct (first_some (fun p => match first_some ex_binding p with
    | Some vt => Some (p,vt) | None => None end) (succedent j)) as [[p [v t]]|] eqn:E;
    [|exact None].
  assert (Hp : In p (succedent j)).
  { apply first_some_spec in E; destruct E as [q [Hq Eq]].
    destruct (first_some ex_binding q); [|discriminate]; inversion Eq; subst; exact Hq. }
  assert (Hs : existential_substitutionb [(v,t)] = true).
  { apply first_some_spec in E; destruct E as [q [Hq Eq]].
    destruct (first_some ex_binding q) as [[u r]|] eqn:F; [|discriminate].
    inversion Eq; subst; apply first_some_spec in F; destruct F as [a [_ Ha]].
    cbn; rewrite (ex_binding_exist a v t Ha); reflexivity. }
  exact (Some (rhs_existential_instantiation d j p [(v,t)] Hp Hs)).
Defined.

Lemma lookup_single v t x : lookup [(v,t)] x =
  if variable_eq_dec x v then t else Var x.
Proof.
  cbn; unfold variable_eqb, eqb_of_dec; destruct (variable_eq_dec x v); reflexivity.
Qed.
Lemma eq_binding_sound d m rho a v t : eq_binding a = Some (v,t) ->
  eval_atom d m rho a -> rho v = eval_term m rho t.
Proof.
  destruct a; try discriminate; destruct right as [z|u|f ts].
  - destruct left; cbn; try discriminate; intros H Ha; inversion H; subst; exact Ha.
  - destruct left as [z'|x|g us]; cbn.
    + intros H Ha; inversion H; subst; symmetry; exact Ha.
    + destruct (term_eqb (Var x) (Var u)); [discriminate|].
      intros H Ha; inversion H; subst; symmetry; exact Ha.
    + intros H Ha; inversion H; subst; symmetry; exact Ha.
  - destruct left; cbn; try discriminate; intros H Ha; inversion H; subst; exact Ha.
Qed.
Lemma bounded_valuation_agreement d m rho sigma bs start p :
  (forall x, rho x = sigma x) -> bounded_product d m rho bs start p ->
  bounded_product d m sigma bs start p.
Proof.
  intros He Hp; apply bounded_nth; intros i a Ha.
  apply (proj1 (eval_atom_agreement m (stage d m (bs (start+i))) rho sigma a
    (fun x _ => He x))).
  exact (proj1 (bounded_nth d m rho bs start p) Hp i a Ha).
Qed.
Lemma singleton_subst_identity m rho v t : rho v = eval_term m rho t ->
  forall x, subst_valuation m [(v,t)] rho x = rho x.
Proof.
  intros H x; unfold subst_valuation; rewrite lookup_single;
    destruct (variable_eq_dec x v) as [->|]; cbn; [symmetry; exact H|reflexivity].
Qed.
Lemma right_equality_substitution d m rho f v t :
  forallb is_free (term_vars t) = true -> rho v = eval_term m rho t ->
  eval_right d m rho (subst_formula [(v,t)] f) -> eval_right d m rho f.
Proof.
  intros Ht He [q [Hq [sigma [Hfree Htruth]]]].
  apply in_map_iff in Hq; destruct Hq as [p [<- Hp]].
  exists p; split; [exact Hp|]; exists (subst_valuation m [(v,t)] sigma); split.
  - intros n; unfold subst_valuation; rewrite lookup_single.
    destruct (variable_eq_dec (Free n) v) as [E|E]; cbn.
    + rewrite (eval_term_free m rho sigma t Hfree Ht); rewrite <- He, <- E; reflexivity.
    + apply Hfree.
  - now apply eval_subst_product in Htruth.
Qed.
Definition left_equality_substitution d p f v t
  (Hbinding : exists a, In a p /\ eq_binding a = Some (v,t))
  (Ht : forallb is_free (term_vars t) = true) : certified_application d (singleton_label p f).
Proof.
  refine {| certified_rule := unary_application "simplEq" (singleton_label p f)
    (subst_sequent [(v,t)] (singleton_label p f)) (identity_trace (singleton_label p f));
    certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; destruct (counter_world d _ _ Hbad) as [Ha Hright].
  assert (Hholds : bounded_product d (world_model w) (world_valuation w) (world_bounds w) 0 p).
  { destruct Ha as [q [Hq Htruth]]; destruct (active_product w) as [|n] eqn:E;
      cbn in Hq; [inversion Hq; subst q|destruct n; discriminate].
    unfold active_offset in Htruth; cbn in Htruth; rewrite E in Htruth; exact Htruth. }
  assert (Hvalue : world_valuation w v = eval_term (world_model w) (world_valuation w) t).
  { destruct Hbinding as [a [Hin Hbind]]; apply (eq_binding_sound d _ _ a v t Hbind).
    pose proof (bounded_product_forget d _ _ _ _ _ Hholds) as Htruth.
    apply Forall_forall with (x := a) in Htruth; auto. }
  exists 0; eexists; exists {| world_model := world_model w; world_valuation := world_valuation w;
    active_product := 0; world_bounds := world_bounds w |}.
  split; [reflexivity|]; split.
  - intro Hden; apply Hright; apply right_equality_substitution with (v := v) (t := t);
      [exact Ht|exact Hvalue|]; apply Hden.
    exists (subst_product [(v,t)] p); split; [reflexivity|].
    cbn; apply bounded_subst; eapply bounded_valuation_agreement;
      [intros x; symmetry; apply singleton_subst_identity; exact Hvalue|exact Hholds].
  - split; cbn [identity_trace progressing]; [|contradiction].
    intros a b H; apply in_map_iff in H; destruct H as [n [E _]];
      inversion E; subst; apply Nat.le_refl.
Defined.
Definition left_equality_rule d (j : sequent) : option (certified_application d j).
Proof.
  destruct j as [f g]; destruct f as [|p f]; [exact None|]; destruct f as [|p' f]; [|exact None].
  destruct (first_some eq_binding p) as [[v t]|] eqn:E; [|exact None].
  destruct (Bool.bool_dec (forallb is_free (term_vars t)) true) as [Ht|]; [|exact None].
  exact (Some (left_equality_substitution d p g v t (first_some_spec eq_binding p (v,t) E) Ht)).
Defined.

Lemma product_free_agreement d m rho sigma p : forallb is_free (product_vars p) = true ->
  agrees_free m rho sigma -> eval_product d m rho p -> eval_product d m sigma p.
Proof.
  intros Hvars Hfree; apply eval_product_agreement; intros x Hx.
  apply forallb_forall with (x := x) in Hvars; [|exact Hx].
  destruct x; [symmetry; apply Hfree|discriminate].
Qed.
Lemma discharge_product d m rho p q : eval_product d m rho p ->
  eval_product d m rho (filter (fun a => negb (logical_mem a p)) q) -> eval_product d m rho q.
Proof.
  intros Hp Hq; apply Forall_forall; intros a Ha.
  destruct (logical_mem a p) eqn:E.
  - apply existsb_exists in E; destruct E as [b [Hb Hab]].
    apply (proj2 (eval_atom_logical_eq d m rho a b Hab));
      apply Forall_forall with (x := b) in Hp; auto.
  - apply Forall_forall with (x := a) in Hq; [exact Hq|].
    apply filter_In; split; [exact Ha|now rewrite E].
Qed.
Lemma discharge_right d m rho p f : forallb is_free (product_vars p) = true ->
  eval_product d m rho p ->
  eval_right d m rho (map (fun q => filter (fun a => negb (logical_mem a p)) q) f) ->
  eval_right d m rho f.
Proof.
  intros Hvars Hp [q [Hq [sigma [Hfree Htruth]]]].
  apply in_map_iff in Hq; destruct Hq as [r [<- Hr]].
  exists r; split; [exact Hr|]; exists sigma; split; [exact Hfree|].
  eapply discharge_product; [eapply product_free_agreement; eauto|exact Htruth].
Qed.
Definition right_discharge_rule d (j : sequent) : option (certified_application d j).
Proof.
  destruct j as [f g]; destruct f as [|p f]; [exact None|]; destruct f as [|p' f]; [|exact None].
  destruct (Bool.bool_dec (forallb is_free (product_vars p)) true) as [Hvars|]; [|exact None].
  refine (Some (same_left_transport d "simplRHS" (singleton_label p g)
    (map (fun q => filter (fun a => negb (logical_mem a p)) q) g) _)).
  intros m rho [q [[E|H] Htruth]] Hright; [subst q|contradiction].
  eapply discharge_right; eauto.
Defined.

Definition argument_equalities ts us := map (fun tu => Eq (fst tu) (snd tu)) (combine ts us).
Lemma argument_equalities_sound d m rho ts us : List.length ts = List.length us ->
  eval_product d m rho (argument_equalities ts us) ->
  map (eval_term m rho) ts = map (eval_term m rho) us.
Proof.
  revert us; induction ts as [|t ts IH]; intros [|u us] Hlen Hp; cbn in Hlen; try discriminate;
    [reflexivity|].
  inversion Hp; subst; cbn; f_equal; [assumption|apply IH; [lia|assumption]].
Qed.
Lemma constructor_eqs_congruence d m rho a eqs : constructor_eqs false a = Some eqs ->
  eval_product d m rho eqs -> eval_atom d m rho a.
Proof.
  destruct a; try discriminate; destruct left; try discriminate; destruct right; try discriminate.
  cbn; match goal with |- context [if ?test then _ else _] => destruct test eqn:E end;
    [|discriminate].
  intros H Hp; inversion H; subst eqs.
  apply andb_true_iff in E; destruct E as [E _]; apply andb_true_iff in E;
    destruct E as [Hname Hlen]; apply String.eqb_eq in Hname; apply Nat.eqb_eq in Hlen; subst.
  f_equal; apply argument_equalities_sound with (d := d); auto.
Qed.
Definition injectivity_guard p := forallb (fun a => match a with
  | Eq t u => term_wfb t && term_wfb u | _ => true end) p.
Lemma constructor_eqs_injective d m rho a eqs : constructor_eqs true a = Some eqs ->
  (match a with Eq t u => term_wfb t && term_wfb u | _ => true end) = true ->
  eval_atom d m rho a -> eval_product d m rho eqs.
Proof.
  destruct a; try discriminate; destruct left; try discriminate; destruct right; try discriminate.
  cbn [constructor_eqs]; match goal with |- context [if ?test then _ else _] => destruct test eqn:E end;
    [|discriminate].
  intros H Hwf Htruth; inversion H; subst eqs.
  apply andb_true_iff in E; destruct E as [E Hctor]; apply andb_true_iff in E;
    destruct E as [Hname Hlen]; apply String.eqb_eq in Hname; apply Nat.eqb_eq in Hlen; subst symbol0.
  apply andb_true_iff in Hwf; destruct Hwf as [Hwf _].
  cbn in Hctor; apply orb_true_iff in Hctor; destruct Hctor as [Hs|Hc];
    apply String.eqb_eq in Hs || apply String.eqb_eq in Hc.
  - subst symbol; cbn in Hwf; apply andb_true_iff in Hwf; destruct Hwf as [Harity _];
      apply Nat.eqb_eq in Harity.
    destruct arguments as [|t [|u ts]]; cbn in Harity; try discriminate.
    destruct arguments0 as [|v [|w us]]; cbn in Hlen; try discriminate.
    cbn in Htruth |- *; constructor; [now apply successor_injective in Htruth|constructor].
  - subst symbol; cbn in Hwf; apply andb_true_iff in Hwf; destruct Hwf as [Harity _];
      apply Nat.eqb_eq in Harity.
    destruct arguments as [|t [|u [|v ts]]]; cbn in Harity; try discriminate.
    destruct arguments0 as [|x [|y [|z us]]]; cbn in Hlen; try discriminate.
    cbn in Htruth |- *; apply cons_injective in Htruth; destruct Htruth as [Ht Hu];
      repeat constructor; assumption.
Qed.
Lemma expand_first_congruence d m rho p q : expand_first false p = Some q ->
  eval_product d m rho q -> eval_product d m rho p.
Proof.
  revert q; induction p as [|a p IH]; intros q; cbn; [discriminate|].
  destruct (constructor_eqs false a) as [eqs|] eqn:E.
  - intros H Htruth; inversion H; subst; apply Forall_app in Htruth;
      destruct Htruth as [Heqs Hp]; constructor; [eapply constructor_eqs_congruence; eauto|exact Hp].
  - destruct (expand_first false p) as [p'|] eqn:F; [|discriminate].
    intros H Htruth; inversion H; subst; inversion Htruth; subst; constructor; [assumption|].
    eapply IH; [reflexivity|assumption].
Qed.
Lemma expand_first_injective d m rho p q : expand_first true p = Some q ->
  injectivity_guard p = true -> eval_product d m rho p -> eval_product d m rho q.
Proof.
  revert q; induction p as [|a p IH]; intros q; cbn; [discriminate|].
  destruct (constructor_eqs true a) as [eqs|] eqn:E.
  - intros H Hguard Htruth; inversion H; subst; apply andb_true_iff in Hguard;
      destruct Hguard as [Ha Hp]; inversion Htruth; subst; apply Forall_app; split;
      [eapply constructor_eqs_injective; eauto|assumption].
  - destruct (expand_first true p) as [p'|] eqn:F; [|discriminate].
    intros H Hguard Htruth; inversion H; subst; apply andb_true_iff in Hguard;
      destruct Hguard as [Ha Hp]; inversion Htruth; subst; constructor; [assumption|].
    eapply IH; [reflexivity|exact Hp|assumption].
Qed.
Definition left_injectivity_rule d (j : sequent) : option (certified_application d j).
Proof.
  destruct j as [f g]; destruct f as [|p f]; [exact None|]; destruct f as [|p' f]; [|exact None].
  destruct (expand_first true p) as [q|] eqn:E; [|exact None].
  destruct (Bool.bool_dec (injectivity_guard p) true) as [Hguard|]; [|exact None].
  refine (checked_singleton_change d "simplLHSInj" p q g g _ _).
  - intros m rho Hp; eapply expand_first_injective; eauto.
  - intros m rho _ H; exact H.
Defined.
Lemma replace_congruence_right d m rho f p q : In p f -> expand_first false p = Some q ->
  eval_right d m rho (replace_product p q f) -> eval_right d m rho f.
Proof.
  intros Hp E [r [Hr [sigma [Hfree Htruth]]]]; destruct Hr as [Hr|Hr].
  - subst r; exists p; split; [exact Hp|]; exists sigma; split; [exact Hfree|].
    eapply expand_first_congruence; eauto.
  - apply filter_In in Hr; exists r; split; [tauto|exists sigma; auto].
Qed.
Definition right_congruence_rule d j : option (certified_application d j).
Proof.
  destruct (first_some (fun p => match expand_first false p with
    | Some q => Some (p,q) | None => None end) (succedent j)) as [[p q]|] eqn:E; [|exact None].
  assert (Hspec : In p (succedent j) /\ expand_first false p = Some q).
  { apply first_some_spec in E; destruct E as [r [Hr Er]].
    destruct (expand_first false r) as [s|] eqn:F; [|discriminate]; inversion Er; subst; auto. }
  refine (Some (same_left_transport d "simplRHSInj" j (replace_product p q (succedent j)) _)).
  intros m rho _; apply replace_congruence_right; tauto.
Defined.

(** Witnesses may be merged only when shared variables are Free. Merely
    splitting a RHS product is unsound when the two halves share an Exist. *)
Definition existential_independentb p q := forallb (fun x =>
  is_free x || negb (existsb (variable_eqb x) (product_vars q))) (product_vars p).
Lemma independence_shared_free p q x : existential_independentb p q = true ->
  In x (product_vars p) -> In x (product_vars q) -> is_free x = true.
Proof.
  intros H Hp Hq; apply forallb_forall with (x := x) in H; [|exact Hp].
  apply orb_true_iff in H; destruct H as [H|H]; [exact H|].
  assert (E : existsb (variable_eqb x) (product_vars q) = true).
  { apply existsb_exists; exists x; split; [exact Hq|apply eqb_of_dec_spec; reflexivity]. }
  rewrite E in H; discriminate.
Qed.
Lemma merge_right_witnesses d m rho p q : existential_independentb p q = true ->
  eval_right d m rho [p] -> eval_right d m rho [q] -> eval_right d m rho [p++q].
Proof.
  intros Hind [p' [[Ep|Hp] [sigma [Hs Htruthp]]]] [q' [[Eq|Hq] [tau [Ht Htruthq]]]];
    try contradiction; subst p' q'.
  set (gamma := fun x => if in_dec variable_eq_dec x (product_vars p) then sigma x else tau x).
  exists (p++q); split; [now left|]; exists gamma; split.
  - intro n; unfold gamma; destruct (in_dec variable_eq_dec (Free n) (product_vars p));
      [apply Hs|apply Ht].
  - apply Forall_app; split.
    + eapply eval_product_agreement; [|exact Htruthp].
      intros x Hx; unfold gamma; destruct (in_dec variable_eq_dec x (product_vars p));
        [reflexivity|contradiction].
    + eapply eval_product_agreement; [|exact Htruthq].
      intros x Hx; unfold gamma; destruct (in_dec variable_eq_dec x (product_vars p)) as [Hp|Hp];
        [|reflexivity].
      pose proof (independence_shared_free p q x Hind Hp Hx) as E; destruct x; [|discriminate].
      rewrite (Hs id), (Ht id); reflexivity.
Qed.
Lemma identity_respects d j k w : respects d j k w w (identity_trace j).
Proof.
  split; cbn [identity_trace progressing]; [|contradiction].
  intros a b H; apply in_map_iff in H; destruct H as [n [E _]];
    inversion E; subst; apply Nat.le_refl.
Qed.
Definition guarded_right_conjunction d f p q (Hind : existential_independentb p q = true) :
  certified_application d {| antecedent := f; succedent := [p++q] |}.
Proof.
  set (j := {| antecedent := f; succedent := [p++q] |}).
  set (k0 := {| antecedent := f; succedent := [p] |}).
  set (k1 := {| antecedent := f; succedent := [q] |}).
  refine {| certified_rule := {| application_name := "AndR"; conclusion := j;
    premises := [{| premise_label := k0; premise_trace := identity_trace j |};
                 {| premise_label := k1; premise_trace := identity_trace j |}] |};
    certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; destruct (counter_world d j w Hbad) as [Ha Hr].
  destruct (excluded_middle_informative (eval_right d (world_model w) (world_valuation w) [p]))
    as [Hp|Hp].
  - assert (Hq : ~ eval_right d (world_model w) (world_valuation w) [q]).
    { intro Hq; apply Hr; apply merge_right_witnesses; assumption. }
    exists 1; eexists; exists w; split; [reflexivity|]; split.
    + intro Hden; apply Hq; apply Hden; exact Ha.
    + apply identity_respects.
  - exists 0; eexists; exists w; split; [reflexivity|]; split.
    + intro Hden; apply Hp; apply Hden; exact Ha.
    + apply identity_respects.
Defined.
Definition retarget_certificate d j k (E : k = j) (c : certified_application d k) :
  certified_application d j :=
  {| certified_rule := certified_rule d k c;
     certified_conclusion := eq_trans (certified_conclusion d k c) E;
     certified_evidence := certified_evidence d k c |}.
Definition checked_right_split d (j : sequent) (n : nat) : option (certified_application d j).
Proof.
  destruct j as [f g]; destruct g as [|p g]; [exact None|]; destruct g as [|p' g]; [|exact None].
  destruct (Bool.bool_dec (Nat.ltb 0 n && Nat.ltb n (List.length p)) true); [|exact None].
  destruct (Bool.bool_dec (existential_independentb (firstn n p) (skipn n p)) true) as [Hind|];
    [|exact None].
  refine (Some (retarget_certificate d _ _ _
    (guarded_right_conjunction d f (firstn n p) (skipn n p) Hind))).
  f_equal; f_equal; apply firstn_skipn.
Defined.

Definition option_rules {A} (x : option A) : list A := match x with Some a => [a] | None => [] end.
Definition structural_rules d j : list (certified_application d j) :=
  (if Nat.leb 2 (List.length (antecedent j)) then [left_disjunction d j] else []) ++
  flat_map (fun n => option_rules (checked_right_split d j n))
    (seq 1 (match succedent j with [p] => List.length p - 1 | _ => 0 end)).
Definition changed_rule d j (c : option (certified_application d j)) : list (certified_application d j) :=
  match c with None => [] | Some c =>
    if existsb (fun p => negb (sequent_eqb j (premise_label p)))
      (premises (certified_rule d j c)) then [c] else [] end.

(** LHS-changing simplifications currently require one antecedent disjunct;
    [left_disjunction] supplies that normalization step. The scope checks are
    intentional: source antecedent truths do not constrain RHS Exist witnesses.
    Constructor injectivity additionally checks the supported arities. *)
Definition simplification_rules d j : list (certified_application d j) :=
  flat_map (fun rule => changed_rule d j (rule d j))
    [trivial_equality_rule; left_equality_rule; right_equality_rule;
     right_discharge_rule; left_injectivity_rule; right_congruence_rule].

Theorem certified_local_sound d j (c : certified_application d j) :
  (forall p, In p (premises (certified_rule d j c)) -> valid d (premise_label p)) -> valid d j.
Proof.
  intro H; rewrite <- (certified_conclusion d j c);
    apply local_sound; [exact (certified_evidence d j c)|exact H].
Qed.

Lemma checked_weakening_target d j k c : checked_weakening d j k = Some c ->
  exists edge, premises (certified_rule d j c) = [{| premise_label := k; premise_trace := edge |}].
Proof.
  destruct j as [f g], k as [h l].
  destruct f as [|p [|p' f]], h as [|q [|q' h]]; cbn [checked_weakening];
    try discriminate.
  destruct (Bool.bool_dec (product_subset q p) true) as [Hl|]; [|discriminate].
  destruct (Bool.bool_dec (forallb (fun a => existsb (fun b => product_subset b a) g) l) true)
    as [Hr|]; [|discriminate].
  destruct (occurrence_map_dec p q) as [[is Hmap]|]; [|discriminate].
  intro H; inversion H; subst c; exists (occurrence_edge q is); reflexivity.
Qed.
Lemma checked_backward_substitution_target d s k c : checked_backward_substitution d s k = Some c ->
  premises (certified_rule d (subst_sequent s k) c) = [{| premise_label := k;
    premise_trace := identity_trace k |}].
Proof.
  unfold checked_backward_substitution; destruct (Bool.bool_dec (substitution_freeb s) true);
    intro H; [inversion H; reflexivity|discriminate].
Qed.
Lemma certified_unary_sound d j k (c : certified_application d j) :
  (exists edge, premises (certified_rule d j c) = [{| premise_label := k; premise_trace := edge |}]) ->
  valid d k -> valid d j.
Proof.
  intros [edge Hps] Hvalid; apply (certified_local_sound d j c).
  intros p Hp; rewrite Hps in Hp; destruct Hp as [<-|Hp]; [exact Hvalid|contradiction].
Qed.
Theorem backlink_prefix_sound d j companion s weakening substitution :
  backlink_prefix d j companion s = Some (weakening, substitution) ->
  valid d companion -> valid d j.
Proof.
  unfold backlink_prefix; destruct (checked_weakening d j (subst_sequent s companion)) as [cw|] eqn:E;
    destruct (checked_backward_substitution d s companion) as [cs|] eqn:F; try discriminate.
  intros H Hvalid; inversion H; subst weakening substitution.
  apply (certified_unary_sound d j (subst_sequent s companion) cw).
  - now apply checked_weakening_target.
  - apply (certified_unary_sound d (subst_sequent s companion) companion cs).
    + exists (identity_trace companion); now apply checked_backward_substitution_target.
    + exact Hvalid.
Qed.

(** Folding consumes every logical copy of an instantiated body atom. The
    inserted head is a new occurrence at position zero, with no incoming trace
    edge; only unchanged remainder occurrences inherit source bounds. *)
Definition fold_head (c : clause) theta tag :=
  Pred tag (clause_name c) (map (subst_term theta) (head c)).
Definition fold_remainder p c theta :=
  filter (fun a => negb (logical_mem a (subst_product theta (body c)))) p.
Definition fold_label p g c theta tag :=
  singleton_label (fold_head c theta tag :: fold_remainder p c theta) g.
Definition fold_edge remainder is :=
  {| continuations := map (fun ab => (fst ab, S (snd ab)))
       (continuations (occurrence_edge remainder is)); progressing := [] |}.
Definition fold_bounds (bs : nat -> nat) is head_bound n :=
  match n with 0 => head_bound | S i => bs (nth i is 0) end.
Lemma fold_remainder_holds d m rho p c theta : eval_product d m rho p ->
  eval_product d m rho (fold_remainder p c theta).
Proof.
  intro H; apply Forall_forall; intros a Ha; apply filter_In in Ha;
    apply Forall_forall with (x := a) in H; tauto.
Qed.
Lemma fold_remainder_bounded d m rho bs p c theta is n :
  occurrence_map p (fold_remainder p c theta) = Some is ->
  bounded_product d m rho bs 0 p ->
  bounded_product d m rho (fold_bounds bs is n) 1 (fold_remainder p c theta).
Proof.
  intros Hmap Hp; pose proof (bounded_product_forget d m rho bs 0 p Hp) as Htruth.
  pose proof (bounded_occurrence_map d m rho bs p (fold_remainder p c theta) is Hmap
    (fold_remainder_holds d m rho p c theta Htruth) Hp) as Hrest.
  apply bounded_nth; intros i a Hi; cbn [fold_bounds Nat.add].
  exact (proj1 (bounded_nth d m rho (fun k => bs (nth k is 0)) 0 _) Hrest i a Hi).
Qed.
Definition fold_application d p g c theta (tag : nat) is
  (Hc : In c d) (Hbody : product_subset (subst_product theta (body c)) p = true)
  (Hmap : occurrence_map p (fold_remainder p c theta) = Some is) :
  certified_application d (singleton_label p g).
Proof.
  refine {| certified_rule := unary_application "Fold" (singleton_label p g)
    (fold_label p g c theta tag) (fold_edge (fold_remainder p c theta) is);
    certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; destruct (counter_world d _ _ Hbad) as [Ha Hright].
  assert (Hp : bounded_product d (world_model w) (world_valuation w) (world_bounds w) 0 p).
  { destruct Ha as [q [Hq Hqtruth]]; destruct (active_product w) as [|i] eqn:E;
      cbn in Hq; [inversion Hq; subst q|destruct i; discriminate].
    unfold active_offset in Hqtruth; cbn in Hqtruth; rewrite E in Hqtruth; exact Hqtruth. }
  assert (Hhead : inductive_relation d (world_model w) (clause_name c)
    (map (eval_term (world_model w) (world_valuation w)) (map (subst_term theta) (head c)))).
  { apply fold_instance; [exact Hc|]; eapply product_subset_sound; [exact Hbody|].
    eapply bounded_product_forget; exact Hp. }
  destruct (constructive_indefinite_description _ Hhead) as [n Hn].
  exists 0; eexists; exists {| world_model := world_model w; world_valuation := world_valuation w;
    active_product := 0; world_bounds := fold_bounds (world_bounds w) is n |}.
  split; [reflexivity|]; split.
  - intro Hden; apply Hright; apply Hden.
    exists (fold_head c theta tag :: fold_remainder p c theta); split; [reflexivity|].
    change (stage d (world_model w) n (clause_name c)
      (map (eval_term (world_model w) (world_valuation w)) (map (subst_term theta) (head c))) /\
      bounded_product d (world_model w) (world_valuation w)
        (fold_bounds (world_bounds w) is n) 1 (fold_remainder p c theta)).
    split; [exact Hn|eapply fold_remainder_bounded; eauto].
  - split; cbn [fold_edge progressing]; [|contradiction].
    intros a b Hab; apply in_map_iff in Hab; destruct Hab as [[x y] [E Hxy]].
    pose proof (occurrence_edge_spec (fold_remainder p c theta) is x y Hxy) as Horig.
    cbn in E; inversion E; subst; unfold rank; cbn [world_bounds fold_bounds]; apply Nat.le_refl.
Defined.
Definition fold_clause_eq_dec (c e : clause) : {c = e} + {c <> e}.
Proof.
  decide equality; try apply string_dec; try apply product_eq_dec;
    apply list_eq_dec; apply term_eq_dec.
Defined.
(** Check the actual source and instantiated head for Free-only LHS scope.
    Substitution domains may contain clause-local Exist variables: the raw
    clause witness supplied by [fold_instance] handles those soundly. *)
Definition checked_fold d (j : sequent) (c : clause) (theta : substitution) (tag : nat) :
  option (certified_application d j).
Proof.
  destruct j as [f g]; destruct f as [|p f]; [exact None|]; destruct f as [|p' f]; [|exact None].
  destruct (in_dec fold_clause_eq_dec c d) as [Hc|]; [|exact None].
  destruct (Bool.bool_dec (forallb is_free (product_vars p) &&
    forallb is_free (atom_vars (fold_head c theta tag))) true); [|exact None].
  destruct (Bool.bool_dec (product_subset (subst_product theta (body c)) p) true) as [Hbody|];
    [|exact None].
  destruct (occurrence_map_dec p (fold_remainder p c theta)) as [[is Hmap]|]; [|exact None].
  exact (Some (fold_application d p g c theta tag is Hc Hbody Hmap)).
Defined.
Lemma checked_fold_target d j c theta tag cert : checked_fold d j c theta tag = Some cert ->
  exists p is, j = singleton_label p (succedent j) /\
    premises (certified_rule d j cert) = [{| premise_label := fold_label p (succedent j) c theta tag;
      premise_trace := fold_edge (fold_remainder p c theta) is |}].
Proof.
  destruct j as [f g]; destruct f as [|p [|p' f]]; cbn [checked_fold]; try discriminate.
  destruct (in_dec fold_clause_eq_dec c d); [|discriminate].
  destruct (Bool.bool_dec (forallb is_free (product_vars p) &&
    forallb is_free (atom_vars (fold_head c theta tag))) true); [|discriminate].
  destruct (Bool.bool_dec (product_subset (subst_product theta (body c)) p) true); [|discriminate].
  destruct (occurrence_map_dec p (fold_remainder p c theta)) as [[is Hmap]|]; [|discriminate].
  intro H; inversion H; subst cert; exists p,is; split; reflexivity.
Qed.

(** Scoped backwards substitution checks every Exist occurring in the whole
    companion, not only the explicit substitution domain. Thus an unmapped
    Exist still reserves its identity image. Variables outside the companion
    are irrelevant to witness reconstruction. *)
Definition scoped_entryb (xt : variable * term) := match fst xt with
  | Free _ => forallb is_free (term_vars (snd xt))
  | Exist _ => match snd xt with Var (Exist _) => true | _ => false end end.
Definition scoped_entriesb (s : substitution) := forallb scoped_entryb s.
Definition existential_scope k := filter (fun x => negb (is_free x))
  (nodup variable_eq_dec (sequent_vars k)).
Fixpoint distinct_termsb ts := match ts with [] => true | t::ts' =>
  negb (existsb (term_eqb t) ts') && distinct_termsb ts' end.
Definition scoped_substitutionb s k := scoped_entriesb s &&
  distinct_termsb (map (lookup s) (existential_scope k)).
Lemma distinct_termsb_sound ts : distinct_termsb ts = true -> NoDup ts.
Proof.
  induction ts as [|t ts IH]; cbn; [constructor|].
  rewrite andb_true_iff; intros [Hnot Htail]; constructor; [|now apply IH].
  intro Hin; assert (E : existsb (term_eqb t) ts = true).
  { apply existsb_exists; exists t; split; [exact Hin|apply eqb_of_dec_spec; reflexivity]. }
  rewrite E in Hnot; discriminate.
Qed.
Lemma nodup_map_injective {A B} (f : A -> B) xs x y : NoDup (map f xs) ->
  In x xs -> In y xs -> f x = f y -> x = y.
Proof.
  induction xs as [|a xs IH]; cbn; [tauto|].
  intros Hnodup Hx Hy E; inversion Hnodup as [|b bs Hnot Htail]; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | |now apply IH].
  - exfalso; apply Hnot; rewrite E; now apply in_map.
  - exfalso; apply Hnot; rewrite <- E; now apply in_map.
Qed.
Lemma scoped_substitution_injective s k x y : scoped_substitutionb s k = true ->
  In x (existential_scope k) -> In y (existential_scope k) ->
  lookup s x = lookup s y -> x = y.
Proof.
  unfold scoped_substitutionb; rewrite andb_true_iff; intros [_ Hdistinct] Hx Hy E.
  apply (nodup_map_injective (lookup s) (existential_scope k));
    [now apply distinct_termsb_sound|exact Hx|exact Hy|exact E].
Qed.
Lemma existential_scope_member k n : In (Exist n) (sequent_vars k) ->
  In (Exist n) (existential_scope k).
Proof.
  intro H; apply filter_In; split; [now apply nodup_In|reflexivity].
Qed.
Lemma lookup_scoped_free s n : scoped_entriesb s = true ->
  forallb is_free (term_vars (lookup s (Free n))) = true.
Proof.
  induction s as [|[x t] s IH]; cbn; [reflexivity|].
  rewrite andb_true_iff; intros [Hxt Hs]; destruct (variable_eqb (Free n) x) eqn:E.
  - apply eqb_of_dec_spec in E; subst x; exact Hxt.
  - now apply IH.
Qed.
Lemma lookup_scoped_exist s n : scoped_entriesb s = true ->
  exists i, lookup s (Exist n) = Var (Exist i).
Proof.
  induction s as [|[x t] s IH]; cbn; [intros _; exists n; reflexivity|].
  rewrite andb_true_iff; intros [Hxt Hs]; destruct (variable_eqb (Exist n) x) eqn:E.
  - apply eqb_of_dec_spec in E; subst x; cbn in Hxt.
    destruct t; try discriminate; destruct name; [discriminate|exists id; reflexivity].
  - now apply IH.
Qed.
Definition inverse_exist s xs n := find (fun x => term_eqb (lookup s x) (Var (Exist n))) xs.
Definition scoped_witness m s k (rho sigma : valuation m) : valuation m := fun x =>
  match x with Free _ => rho x | Exist n =>
    match inverse_exist s (existential_scope k) n with Some y => sigma y | None => rho x end end.
Lemma scoped_witness_free m s k rho sigma : agrees_free m rho (scoped_witness m s k rho sigma).
Proof. intro n; reflexivity. Qed.
Lemma scoped_witness_lookup m s k rho sigma : scoped_substitutionb s k = true ->
  agrees_free m (subst_valuation m s rho) sigma ->
  forall x, In x (sequent_vars k) ->
    subst_valuation m s (scoped_witness m s k rho sigma) x = sigma x.
Proof.
  unfold scoped_substitutionb; rewrite andb_true_iff; intros [Hentries Hdistinct] Hfree x Hx.
  destruct x as [n|n].
  - unfold subst_valuation; rewrite (eval_term_free m rho (scoped_witness m s k rho sigma)
      _ (scoped_witness_free m s k rho sigma) (lookup_scoped_free s n Hentries)).
    symmetry; apply Hfree.
  - destruct (lookup_scoped_exist s n Hentries) as [i Hi].
    unfold subst_valuation; rewrite Hi; cbn [eval_term scoped_witness].
    destruct (inverse_exist s (existential_scope k) i) as [y|] eqn:E.
    + unfold inverse_exist in E; apply find_some in E; destruct E as [Hy He].
      apply eqb_of_dec_spec in He.
      assert (Ey : y = Exist n).
      { apply (nodup_map_injective (lookup s) (existential_scope k));
          [now apply distinct_termsb_sound|exact Hy|now apply existential_scope_member|congruence]. }
      now subst y.
    + unfold inverse_exist in E; apply find_none with (x := Exist n) in E;
        [|now apply existential_scope_member].
      assert (He : term_eqb (lookup s (Exist n)) (Var (Exist i)) = true).
      { apply eqb_of_dec_spec; exact Hi. } congruence.
Qed.
Lemma right_scoped_substitution d m s rho k : scoped_substitutionb s k = true ->
  eval_right d m (subst_valuation m s rho) (succedent k) ->
  eval_right d m rho (subst_formula s (succedent k)).
Proof.
  intros Hscope [p [Hp [sigma [Hfree Htruth]]]].
  exists (subst_product s p); split; [now apply in_map|].
  exists (scoped_witness m s k rho sigma); split; [apply scoped_witness_free|].
  apply eval_subst_product; eapply eval_product_agreement; [|exact Htruth].
  intros x Hx; symmetry; apply scoped_witness_lookup; [exact Hscope|exact Hfree|].
  apply in_or_app; right; apply in_concat; exists (product_vars p); split; [now apply in_map|exact Hx].
Qed.
Definition backward_substitution_scoped d s k (Hs : scoped_substitutionb s k = true) :
  certified_application d (subst_sequent s k).
Proof.
  refine {| certified_rule := unary_application "SubstScoped" (subst_sequent s k) k (identity_trace k);
    certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; destruct (counter_world d _ _ Hbad) as [Ha Hr].
  destruct (constructive_indefinite_description _ Ha) as [q [Hq Htruth]].
  assert (Hinv : exists p, nth_error (antecedent k) (active_product w) = Some p /\
    q = subst_product s p).
  { change (nth_error (map (subst_product s) (antecedent k)) (active_product w) = Some q) in Hq.
    rewrite nth_error_map in Hq.
    destruct (nth_error (antecedent k) (active_product w)) as [p|] eqn:Hp.
    - exists p; split; [reflexivity|].
      assert (E : Some (subst_product s p) = Some q).
      { exact (eq_trans (eq_sym (f_equal (option_map (subst_product s)) Hp)) Hq). }
      now inversion E.
    - assert (E : @None product = Some q).
      { exact (eq_trans (eq_sym (f_equal (option_map (subst_product s)) Hp)) Hq). }
      discriminate. }
  destruct (constructive_indefinite_description _ Hinv) as [p [Hp ->]].
  exists 0; eexists; exists {| world_model := world_model w;
    world_valuation := subst_valuation (world_model w) s (world_valuation w);
    active_product := active_product w; world_bounds := world_bounds w |}.
  split; [reflexivity|]; split.
  - intro Hden; apply Hr; apply right_scoped_substitution; [exact Hs|]; apply Hden.
    exists p; split; [exact Hp|].
    unfold active_offset in *; cbn in *; rewrite subst_offset in Htruth;
      now apply bounded_subst in Htruth.
  - split; cbn [identity_trace progressing]; [|contradiction].
    intros a b Hab; apply in_map_iff in Hab; destruct Hab as [n [Hn _]];
      inversion Hn; subst; apply Nat.le_refl.
Defined.
Definition checked_backward_substitution_scoped d s k :
  option (certified_application d (subst_sequent s k)) :=
  match Bool.bool_dec (scoped_substitutionb s k) true with
  | left H => Some (backward_substitution_scoped d s k H) | right _ => None end.
Lemma checked_backward_substitution_scoped_target d s k c :
  checked_backward_substitution_scoped d s k = Some c ->
  premises (certified_rule d (subst_sequent s k) c) = [{| premise_label := k;
    premise_trace := identity_trace k |}].
Proof.
  unfold checked_backward_substitution_scoped; destruct (Bool.bool_dec (scoped_substitutionb s k) true);
    intro H; [inversion H; reflexivity|discriminate].
Qed.
Definition backlink_prefix_scoped d j companion s :
  option (certified_application d j * certified_application d (subst_sequent s companion)) :=
  match checked_weakening d j (subst_sequent s companion),
        checked_backward_substitution_scoped d s companion with
  | Some weakening, Some substitution => Some (weakening, substitution)
  | _, _ => None end.
Theorem backlink_prefix_scoped_sound d j companion s weakening substitution :
  backlink_prefix_scoped d j companion s = Some (weakening, substitution) ->
  valid d companion -> valid d j.
Proof.
  unfold backlink_prefix_scoped; destruct (checked_weakening d j (subst_sequent s companion)) as [cw|] eqn:E;
    destruct (checked_backward_substitution_scoped d s companion) as [cs|] eqn:F; try discriminate.
  intros H Hvalid; inversion H; subst weakening substitution.
  apply (certified_unary_sound d j (subst_sequent s companion) cw).
  - now apply checked_weakening_target.
  - apply (certified_unary_sound d (subst_sequent s companion) companion cs).
    + exists (identity_trace companion); now apply checked_backward_substitution_scoped_target.
    + exact Hvalid.
Qed.
