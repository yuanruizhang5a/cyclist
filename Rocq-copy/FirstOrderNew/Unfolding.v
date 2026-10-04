From Stdlib Require Import List Bool Arith String Lia Classical_Prop.
From Stdlib Require Import Logic.ClassicalEpsilon.
From CyclistRocq.FirstOrderNew Require Export Rules.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** Unfolding uses occurrence positions for traces, and logical annotations only
    for display.  The informative counterstep uses the standard-library
    [constructive_indefinite_description] to select a clause witness and its
    premise index.  No model-specific or project axioms are assumed.

    Assumption audit ([Print Assumptions]): [left_unfold_at_evidence] uses only
    [Classical_Prop.classic] and
    [ClassicalEpsilon.constructive_indefinite_description];
    [right_unfold_evidence] and [right_unfold_instance_evidence] are closed
    under the global context.

    Public search API:
      - [unfold_atom_descriptor], [atom_descriptors]: proof-free atom positions;
      - [left_unfold_at_application d j product_index descriptor] and
        [right_unfold_application j descriptor clause]: proof-free applications;
      - [checked_left_unfold_at] / [checked_right_unfold]: option certification;
      - [left_unfold_rules d j] / [right_unfold_rules d j]: certified enumeration.
      - [right_unfold_instance_application j descriptor clause theta] and
        [checked_right_unfold_instance d j descriptor clause theta]: arbitrary
        substitution instances of the fresh right clause;
      - [checked_right_unfold_matched fuel d j descriptor clause] and
        [right_unfold_matched_rules fuel d j]: head-matcher guided instances.

    Checked left side conditions: free antecedent, exact selected product at
    its index, matching arity for EVERY clause with that symbol, and fresh
    universalized clause variables.  Checked right side conditions: free
    antecedent, selected product membership, clause membership/name/arity,
    and fresh class-preserving clause variables.  Freshness is guaranteed by
    construction and also validated by the clause freshness booleans.  No head
    matcher is required: every head/argument pair contributes an equality. *)

Definition variable_code x := match x with Free n => 2*n | Exist n => 2*n+1 end.
Definition variable_decode n := if Nat.even n then Free (Nat.div2 n) else Exist (Nat.div2 n).
Lemma variable_decode_code x : variable_decode (variable_code x) = x.
Proof.
  destruct x; unfold variable_decode, variable_code.
  - assert (E : Nat.even (2*id) = true) by (rewrite Nat.even_mul; reflexivity).
    rewrite E, Nat.div2_double. reflexivity.
  - replace (2*id+1) with (S (2*id)) by lia.
    assert (E : Nat.even (S (2*id)) = false).
    { rewrite Nat.even_succ, Nat.odd_mul; reflexivity. }
    rewrite E, Nat.div2_succ_double. reflexivity.
Qed.
Definition left_variable start x := Free (start + variable_code x).
Definition right_variable start x := match x with
  | Free n => Free (start+n) | Exist n => Exist (start+n) end.
Lemma variable_code_injective x y : variable_code x = variable_code y -> x = y.
Proof. intro E; rewrite <- (variable_decode_code x), <- (variable_decode_code y), E; reflexivity. Qed.
Lemma left_variable_injective start x y : left_variable start x = left_variable start y -> x = y.
Proof. intro E; apply variable_code_injective; unfold left_variable in E; inversion E; lia. Qed.
Lemma right_variable_injective start x y : right_variable start x = right_variable start y -> x = y.
Proof. destruct x, y; cbn; intro E; inversion E; f_equal; lia. Qed.
Lemma left_variable_fresh xs x : ~ In (left_variable (fresh_id xs) x) xs.
Proof.
  intro H; pose proof (fresh_id_gt xs _ H) as E.
  change (fresh_id xs + variable_code x < fresh_id xs) in E; lia.
Qed.
Lemma right_variable_fresh xs x : ~ In (right_variable (fresh_id xs) x) xs.
Proof.
  intro H; pose proof (fresh_id_gt xs _ H) as E.
  destruct x; change (fresh_id xs + id < fresh_id xs) in E; lia.
Qed.
Definition fresh_variableb xs x := negb (existsb (variable_eqb x) xs).
Lemma fresh_variableb_spec xs x : fresh_variableb xs x = true <-> ~ In x xs.
Proof.
  unfold fresh_variableb; rewrite negb_true_iff.
  split.
  - intros H Hin; assert (existsb (variable_eqb x) xs = true) as E.
    { apply existsb_exists; exists x; split; [exact Hin|apply eqb_of_dec_spec; reflexivity]. }
    congruence.
  - intro H; destruct (existsb (variable_eqb x) xs) eqn:E; [|reflexivity].
    apply existsb_exists in E; destruct E as [y [Hy E]];
      apply eqb_of_dec_spec in E; subst y; contradiction.
Qed.
Fixpoint rename_term (f : variable -> variable) t := match t with
  | Const z => Const z | Var x => Var (f x)
  | Fun s ts => Fun s (map (rename_term f) ts) end.
Definition rename_atom f a := match a with
  | Eq t u => Eq (rename_term f t) (rename_term f u)
  | Deq t u => Deq (rename_term f t) (rename_term f u)
  | Pred tag s ts => Pred tag s (map (rename_term f) ts) end.
Definition rename_product f p := map (rename_atom f) p.
Definition left_clause start c := {| clause_name := clause_name c;
  head := map (rename_term (left_variable start)) (head c);
  body := rename_product (left_variable start) (body c) |}.
Definition right_clause start c := {| clause_name := clause_name c;
  head := map (rename_term (right_variable start)) (head c);
  body := rename_product (right_variable start) (body c) |}.

Definition extend_left m start (rho witness : valuation m) : valuation m :=
  fun x => match x with
  | Free n => if Nat.leb start n then witness (variable_decode (n-start)) else rho x
  | Exist _ => rho x end.
Lemma extend_left_new m start rho witness x :
  extend_left m start rho witness (left_variable start x) = witness x.
Proof.
  unfold extend_left, left_variable.
  rewrite (proj2 (Nat.leb_le _ _) (Nat.le_add_r _ _)).
  replace (start + variable_code x - start) with (variable_code x) by lia.
  now rewrite variable_decode_code.
Qed.
Lemma extend_left_old m start rho witness x : variable_id x < start ->
  extend_left m start rho witness x = rho x.
Proof.
  destruct x; cbn; intro H; [|reflexivity].
  rewrite (proj2 (Nat.leb_gt _ _) H). reflexivity.
Qed.
Lemma eval_term_ext m rho sigma t :
  (forall x, In x (term_vars t) -> rho x = sigma x) ->
  eval_term m rho t = eval_term m sigma t.
Proof.
  induction t using term_induction; intro He; cbn in *; try reflexivity.
  - apply He; now left.
  - f_equal. apply map_ext_in; intros t Ht.
    apply Forall_forall with (x:=t) in H; [|exact Ht].
    apply H; intros x Hx; apply He. apply in_concat.
    exists (term_vars t); split; [apply in_map; exact Ht|exact Hx].
Qed.
Lemma eval_atom_ext m r rho sigma a :
  (forall x, In x (atom_vars a) -> rho x = sigma x) ->
  (eval_atom_with m r rho a <-> eval_atom_with m r sigma a).
Proof.
  destruct a; cbn; intro He.
  - rewrite (eval_term_ext m rho sigma left), (eval_term_ext m rho sigma right).
    + reflexivity.
    + intros; apply He; apply in_or_app; auto.
    + intros; apply He; apply in_or_app; auto.
  - rewrite (eval_term_ext m rho sigma left), (eval_term_ext m rho sigma right).
    + reflexivity.
    + intros; apply He; apply in_or_app; auto.
    + intros; apply He; apply in_or_app; auto.
  - assert (map (eval_term m rho) arguments = map (eval_term m sigma) arguments) as E.
    { apply map_ext_in; intros t Ht; apply eval_term_ext; intros x Hx.
      apply He; apply in_concat; exists (term_vars t); split;
        [apply in_map; exact Ht|exact Hx]. }
    now rewrite E.
Qed.
Lemma eval_product_ext m r rho sigma p :
  (forall x, In x (product_vars p) -> rho x = sigma x) ->
  (eval_product_with m r rho p <-> eval_product_with m r sigma p).
Proof.
  intro He; unfold eval_product_with; rewrite !Forall_forall.
  assert (forall a, In a p -> eval_atom_with m r rho a <-> eval_atom_with m r sigma a) as E.
  { intros a Ha; apply eval_atom_ext; intros x Hx; apply He.
    apply in_concat; exists (atom_vars a); split; [apply in_map; exact Ha|exact Hx]. }
  split; intros H a Ha; [apply (proj1 (E a Ha))|apply (proj2 (E a Ha))]; auto.
Qed.
Lemma eval_rename_term m f rho t :
  eval_term m rho (rename_term f t) = eval_term m (fun x => rho (f x)) t.
Proof.
  induction t using term_induction; cbn; auto.
  f_equal; rewrite map_map; apply map_ext_in; intros t Ht.
  apply Forall_forall with (x:=t) in H; auto.
Qed.
Lemma eval_rename_atom m r f rho a :
  eval_atom_with m r rho (rename_atom f a) <->
  eval_atom_with m r (fun x => rho (f x)) a.
Proof.
  destruct a; cbn; try (rewrite !eval_rename_term; reflexivity).
  rewrite map_map. assert (map (fun t => eval_term m rho (rename_term f t)) arguments =
    map (eval_term m (fun x => rho (f x))) arguments) as E.
  { apply map_ext; apply eval_rename_term. } now rewrite E.
Qed.
Lemma eval_rename_product m r f rho p :
  eval_product_with m r rho (rename_product f p) <->
  eval_product_with m r (fun x => rho (f x)) p.
Proof.
  unfold eval_product_with, rename_product; rewrite Forall_map, !Forall_forall.
  split; intros H a Ha; [apply (proj1 (eval_rename_atom m r f rho a))|
    apply (proj2 (eval_rename_atom m r f rho a))]; auto.
Qed.
Lemma eval_left_term m start rho witness t :
  eval_term m (extend_left m start rho witness) (rename_term (left_variable start) t) =
  eval_term m witness t.
Proof.
  rewrite eval_rename_term; apply eval_term_ext; intros; apply extend_left_new.
Qed.
Lemma eval_left_body m r start rho witness p :
  eval_product_with m r witness p ->
  eval_product_with m r (extend_left m start rho witness)
    (rename_product (left_variable start) p).
Proof.
  rewrite eval_rename_product. intro H.
  apply (proj2 (eval_product_ext m r _ witness p
    ltac:(intros; apply extend_left_new))); exact H.
Qed.

(** Only free variables occurring in a right formula affect its satisfaction;
    existential variables are selected anew by [eval_right]. *)
Lemma eval_right_ext d m rho tau f :
  (forall n, In (Free n) (formula_vars f) -> rho (Free n) = tau (Free n)) ->
  (eval_right d m rho f <-> eval_right d m tau f).
Proof.
  intro He. assert (forall rho tau : valuation m,
    (forall n, In (Free n) (formula_vars f) -> rho (Free n) = tau (Free n)) ->
    eval_right d m rho f -> eval_right d m tau f) as Hdir.
  { intros r t E [p [Hp [sigma [Hfree Htruth]]]].
    exists p; split; [exact Hp|].
    set (sigma' := fun x : variable => match x with
      Free n => t (Free n) | Exist _ => sigma x end).
    exists sigma'.
    split; [intro n; reflexivity|].
    apply (proj1 (eval_product_ext m (inductive_relation d m) sigma sigma' p
      ltac:(intros x Hx; destruct x; [|reflexivity]; cbn [sigma']; rewrite Hfree; apply E;
        apply in_concat; exists (product_vars p); split;
        [apply in_map; exact Hp|exact Hx]))); exact Htruth. }
  split; apply Hdir; auto. intros n Hn; symmetry; auto.
Qed.

Definition head_equations xs ys := map (fun tu => Eq (fst tu) (snd tu)) (combine xs ys).
Lemma head_equations_length xs ys : List.length xs = List.length ys ->
  List.length (head_equations xs ys) = List.length xs.
Proof. unfold head_equations; rewrite length_map, length_combine; lia. Qed.
Lemma head_equations_eval m r rho xs ys : List.length xs = List.length ys ->
  (eval_product_with m r rho (head_equations xs ys) <->
   map (eval_term m rho) xs = map (eval_term m rho) ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] Hlen; cbn in Hlen;
    try discriminate; cbn [head_equations combine map eval_product_with].
  - split; intro H; [reflexivity|constructor].
  - change (Forall (eval_atom_with m r rho) (Eq x y :: head_equations xs ys) <->
      eval_term m rho x :: map (eval_term m rho) xs =
      eval_term m rho y :: map (eval_term m rho) ys).
    rewrite Forall_cons_iff. unfold eval_product_with in IH.
    rewrite IH by lia. cbn [eval_atom_with].
    split; [intros [E Es]; now rewrite E, Es|intro E; inversion E; auto].
Qed.
Lemma eval_retag_atom m r rho tag a :
  eval_atom_with m r rho (retag tag a) <-> eval_atom_with m r rho a.
Proof. destruct a; reflexivity. Qed.
Lemma eval_retag_product m r rho tag p :
  eval_product_with m r rho (map (retag tag) p) <-> eval_product_with m r rho p.
Proof.
  unfold eval_product_with; rewrite Forall_map, !Forall_forall.
  split; intros H a Ha; [apply (proj1 (eval_retag_atom m r rho tag a))|
    apply (proj2 (eval_retag_atom m r rho tag a))]; auto.
Qed.
Lemma bounded_product_app d m rho bounds start p q :
  bounded_product d m rho bounds start (p++q) <->
  bounded_product d m rho bounds start p /\
  bounded_product d m rho bounds (start+List.length p) q.
Proof.
  revert start; induction p as [|a p IH]; intro start; cbn.
  - replace (start+0) with start by lia; tauto.
  - rewrite IH. replace (S start + List.length p) with (start+S (List.length p)) by lia.
    tauto.
Qed.
Lemma bounded_product_ext d m rho sigma bounds bounds' start start' p :
  (forall x, In x (product_vars p) -> rho x = sigma x) ->
  (forall k, k < List.length p -> bounds (start+k) = bounds' (start'+k)) ->
  (bounded_product d m rho bounds start p <->
   bounded_product d m sigma bounds' start' p).
Proof.
  revert start start'; induction p as [|a p IH]; intros start start' Hr Hb; cbn; [tauto|].
  assert (bounds start = bounds' start') as Eb.
  { specialize (Hb 0); rewrite !Nat.add_0_r in Hb; apply Hb; cbn; lia. }
  rewrite Eb, (eval_atom_ext m (stage d m (bounds' start')) rho sigma a).
  - rewrite (IH (S start) (S start')); [tauto| |].
    + intros x Hx; apply Hr; unfold product_vars; cbn; apply in_or_app; now right.
    + intros k Hk; specialize (Hb (S k)); replace (start+S k) with (S start+k) in Hb by lia.
      replace (start'+S k) with (S start'+k) in Hb by lia; apply Hb; cbn; lia.
  - intros x Hx; apply Hr; unfold product_vars; cbn; apply in_or_app; now left.
Qed.
Lemma counterexample_parts d j w : ~ denote d j w ->
  active_holds d j w /\ ~ eval_right d (world_model w) (world_valuation w) (succedent j).
Proof. unfold denote; tauto. Qed.

(** Predicate positions in an arbitrary product, with their global offset. *)
Fixpoint predicate_positions start p := match p with
  | [] => [] | a::p => match a with Pred _ _ _ => [start] | _ => [] end ++
      predicate_positions (S start) p end.
Lemma predicate_positions_range start p k : In k (predicate_positions start p) ->
  start <= k < start + List.length p.
Proof.
  revert start; induction p as [|a p IH]; intros start H; cbn in H; [contradiction|].
  destruct a; cbn in H; try (specialize (IH (S start) H); cbn; lia).
  destruct H as [<-|H]; [cbn; lia|specialize (IH (S start) H); cbn; lia].
Qed.
Definition identity_trace j := {| continuations := map (fun k => (k,k)) (trace_tags j);
  progressing := [] |}.
Lemma identity_trace_respects d j k w : respects d j k w w (identity_trace j).
Proof.
  split; cbn; intros a b H; [|contradiction].
  apply in_map_iff in H; destruct H as [t [E Ht]]; inversion E; subst; unfold rank; lia.
Qed.

(** Proof-free descriptors are deliberately separate from certification, so
    search can enumerate applications without constructing proof terms. *)
Record unfold_atom_descriptor := {
  unfold_prefix : product;
  unfold_suffix : product;
  unfold_logical_tag : nat;
  unfold_symbol : string;
  unfold_arguments : list term
}.
Definition unfold_principal u := Pred (unfold_logical_tag u)
  (unfold_symbol u) (unfold_arguments u).
Definition unfold_source_product u := unfold_prefix u ++ unfold_principal u :: unfold_suffix u.
Definition unfolding_start j := fresh_id (sequent_vars j).
Definition left_clause_freshb j c := forallb
  (fun x => is_free (left_variable (unfolding_start j) x) &&
    fresh_variableb (sequent_vars j) (left_variable (unfolding_start j) x)) (clause_vars c).
Definition right_clause_freshb j c := forallb
  (fun x => fresh_variableb (sequent_vars j) (right_variable (unfolding_start j) x)) (clause_vars c).
Lemma left_clause_freshb_true j c : left_clause_freshb j c = true.
Proof.
  apply forallb_forall; intros x Hx; apply andb_true_iff; split; [reflexivity|].
  apply fresh_variableb_spec; apply left_variable_fresh.
Qed.
Lemma right_clause_freshb_true j c : right_clause_freshb j c = true.
Proof. apply forallb_forall; intros x Hx; apply fresh_variableb_spec; apply right_variable_fresh. Qed.
Definition right_unfold_product j u c :=
  unfold_prefix u ++
  head_equations (unfold_arguments u) (head (right_clause (unfolding_start j) c)) ++
  body (right_clause (unfolding_start j) c) ++ unfold_suffix u.
Definition right_unfold_label j u c := {| antecedent := antecedent j;
  succedent := replace_product (unfold_source_product u) (right_unfold_product j u c)
    (succedent j) |}.
Definition right_unfold_application j u c := {| application_name := "right_unfold";
  conclusion := j;
  premises := [{| premise_label := right_unfold_label j u c;
    premise_trace := identity_trace j |}] |}.
Definition clause_eq_dec (c c' : clause) : {c=c'}+{c<>c'}.
Proof. decide equality; [apply product_eq_dec|apply list_eq_dec; apply term_eq_dec|apply string_dec]. Defined.
Definition clause_eqb := eqb_of_dec clause_eq_dec.
Definition right_unfold_check d j u c :=
  antecedent_freeb j &&
  existsb (product_eqb (unfold_source_product u)) (succedent j) &&
  existsb (clause_eqb c) d &&
  String.eqb (clause_name c) (unfold_symbol u) &&
  Nat.eqb (List.length (head c)) (List.length (unfold_arguments u)) && right_clause_freshb j c.

Lemma right_unfold_product_folds d j u c m rho : In c d ->
  clause_name c = unfold_symbol u ->
  List.length (head c) = List.length (unfold_arguments u) ->
  eval_product d m rho (right_unfold_product j u c) ->
  eval_product d m rho (unfold_source_product u).
Proof.
  intros Hc Hname Hlen Htruth.
  unfold right_unfold_product, eval_product, eval_product_with in Htruth.
  rewrite !Forall_app in Htruth.
  destruct Htruth as [Hpre [Heqs [Hbody Hpost]]].
  unfold unfold_source_product, eval_product, eval_product_with.
  rewrite Forall_app, Forall_cons_iff. split; [exact Hpre|].
  split; [|exact Hpost]. unfold unfold_principal; cbn [eval_atom_with].
  apply inductive_unfold. exists c; split; [exact Hc|]. split; [exact Hname|].
  exists (fun x => rho (right_variable (unfolding_start j) x)); split.
  - apply head_equations_eval in Heqs.
    + change (map (eval_term m rho) (unfold_arguments u) =
        map (eval_term m rho) (map (rename_term (right_variable (unfolding_start j)))
          (head c))) in Heqs. rewrite map_map in Heqs.
      rewrite Heqs; apply map_ext; symmetry; apply eval_rename_term.
    + change (List.length (unfold_arguments u) =
        List.length (map (rename_term (right_variable (unfolding_start j))) (head c))).
      rewrite length_map; lia.
  - exact (proj1 (eval_rename_product m (inductive_relation d m)
      (right_variable (unfolding_start j)) rho (body c)) Hbody).
Qed.
Lemma right_unfold_implies d j u c : In c d ->
  In (unfold_source_product u) (succedent j) ->
  clause_name c = unfold_symbol u ->
  List.length (head c) = List.length (unfold_arguments u) ->
  forall m rho, eval_right d m rho (succedent (right_unfold_label j u c)) ->
    eval_right d m rho (succedent j).
Proof.
  intros Hc Hsource Hname Hlen m rho [p [Hp [sigma [Hfree Htruth]]]].
  cbn [right_unfold_label replace_product] in Hp.
  destruct Hp as [<-|Hp].
  - exists (unfold_source_product u); split; [exact Hsource|].
    exists sigma; split; [exact Hfree|]. eapply right_unfold_product_folds; eauto.
  - apply filter_In in Hp; destruct Hp as [Hp _].
    exists p; split; [exact Hp|]. exists sigma; auto.
Qed.
Theorem right_unfold_evidence d j u c : In c d ->
  In (unfold_source_product u) (succedent j) ->
  clause_name c = unfold_symbol u ->
  List.length (head c) = List.length (unfold_arguments u) ->
  local_evidence d (right_unfold_application j u c).
Proof.
  intros Hc Hp Hname Hlen; constructor; intros w Hbad.
  exists 0, {| premise_label := right_unfold_label j u c;
    premise_trace := identity_trace j |}, w.
  split; [reflexivity|]. split.
  - intro Hden; apply Hbad; intro Hleft.
    eapply right_unfold_implies; eauto.
  - apply identity_trace_respects.
Qed.

Definition fresh_logical_tag j := S (fold_right Nat.max 0 (logical_tags j)).
Lemma fresh_logical_tag_gt j tag : In tag (logical_tags j) -> tag < fresh_logical_tag j.
Proof.
  unfold fresh_logical_tag; induction (logical_tags j) as [|t ts IH]; cbn; [contradiction|].
  intros [<-|H].
  - pose proof (Nat.le_max_l t (fold_right Nat.max 0 ts)); lia.
  - specialize (IH H); pose proof (Nat.le_max_r t (fold_right Nat.max 0 ts)); lia.
Qed.
Lemma fresh_logical_tag_fresh j : ~ In (fresh_logical_tag j) (logical_tags j).
Proof. intro H; pose proof (fresh_logical_tag_gt j _ H); lia. Qed.
Definition left_unfold_body j u c :=
  map (retag (unfold_logical_tag u)) (body (left_clause (unfolding_start j) c)).
Definition left_unfold_equalities j u c :=
  head_equations (unfold_arguments u) (head (left_clause (unfolding_start j) c)).
Definition left_copy_position j u c :=
  List.length (left_unfold_body j u c) + List.length (left_unfold_equalities j u c).
Definition left_unfold_product j u c :=
  left_unfold_body j u c ++ left_unfold_equalities j u c ++
  [Pred (fresh_logical_tag j) (unfold_symbol u) (unfold_arguments u)] ++
  unfold_prefix u ++ unfold_suffix u.
Definition left_body_edges u c := map
  (fun k => (List.length (unfold_prefix u), k)) (predicate_positions 0 (body c)).
Definition left_context_edges j u c :=
  map (fun k => (k, S (left_copy_position j u c) + k))
    (predicate_positions 0 (unfold_prefix u)) ++
  map (fun k => (S (List.length (unfold_prefix u)) + k,
    S (left_copy_position j u c) + List.length (unfold_prefix u) + k))
    (predicate_positions 0 (unfold_suffix u)).
Definition left_unfold_trace j u c := {|
  continuations := left_body_edges u c ++
    [(List.length (unfold_prefix u), left_copy_position j u c)] ++
    left_context_edges j u c;
  progressing := left_body_edges u c |}.
Definition left_unfold_premise j u c := {|
  premise_label := {| antecedent := [left_unfold_product j u c]; succedent := succedent j |};
  premise_trace := left_unfold_trace j u c |}.
Definition left_unfold_application d j u := {| application_name := "left_unfold_contract";
  conclusion := j;
  premises := map (left_unfold_premise j u) (clauses_for d (unfold_symbol u)) |}.

(** The basic left schema has a single antecedent product.  All matching
    clauses, including base clauses with no predicate children, are premises.
    A disjunctive antecedent can first be decomposed with [lhs_split]. *)
Definition left_unfold_check d j u :=
  antecedent_freeb j &&
  sequent_eqb j {| antecedent := [unfold_source_product u]; succedent := succedent j |} &&
  forallb (fun c => Nat.eqb (List.length (head c)) (List.length (unfold_arguments u)) &&
    left_clause_freshb j c)
    (clauses_for d (unfold_symbol u)).
Definition left_unfold_bounds j u c (old : nat -> nat) n k :=
  let copy := left_copy_position j u c in
  if Nat.ltb k copy then n else
  if Nat.eqb k copy then old (List.length (unfold_prefix u)) else
  if Nat.ltb k (S copy + List.length (unfold_prefix u)) then old (k - S copy) else
  old (S (List.length (unfold_prefix u)) + (k - (S copy + List.length (unfold_prefix u)))).
Lemma left_body_length j u c : List.length (left_unfold_body j u c) = List.length (body c).
Proof. unfold left_unfold_body, left_clause, rename_product; cbn; now rewrite !length_map. Qed.
Lemma left_bounds_child j u c old n k : k < left_copy_position j u c ->
  left_unfold_bounds j u c old n k = n.
Proof. intro H; unfold left_unfold_bounds; rewrite (proj2 (Nat.ltb_lt _ _) H); reflexivity. Qed.
Lemma left_bounds_copy j u c old n :
  left_unfold_bounds j u c old n (left_copy_position j u c) = old (List.length (unfold_prefix u)).
Proof. unfold left_unfold_bounds; rewrite Nat.ltb_irrefl, Nat.eqb_refl; reflexivity. Qed.
Lemma left_bounds_prefix j u c old n k : k < List.length (unfold_prefix u) ->
  left_unfold_bounds j u c old n (S (left_copy_position j u c)+k) = old k.
Proof.
  intro H; unfold left_unfold_bounds.
  set (cp := left_copy_position j u c).
  rewrite (proj2 (Nat.ltb_ge (S cp+k) cp) ltac:(lia)),
    (proj2 (Nat.eqb_neq (S cp+k) cp) ltac:(lia)),
    (proj2 (Nat.ltb_lt (S cp+k) (S cp+List.length (unfold_prefix u))) ltac:(lia)).
  f_equal; lia.
Qed.
Lemma left_bounds_suffix j u c old n k :
  left_unfold_bounds j u c old n
    (S (left_copy_position j u c)+List.length (unfold_prefix u)+k) =
  old (S (List.length (unfold_prefix u))+k).
Proof.
  unfold left_unfold_bounds.
  set (cp := left_copy_position j u c).
  rewrite (proj2 (Nat.ltb_ge (S cp+List.length (unfold_prefix u)+k) cp) ltac:(lia)),
    (proj2 (Nat.eqb_neq (S cp+List.length (unfold_prefix u)+k) cp) ltac:(lia)),
    (proj2 (Nat.ltb_ge (S cp+List.length (unfold_prefix u)+k)
      (S cp+List.length (unfold_prefix u))) ltac:(lia)).
  f_equal; lia.
Qed.
Lemma left_unfold_respects d j u c m rho tau old n :
  old (List.length (unfold_prefix u)) = S n ->
  respects d j (premise_label (left_unfold_premise j u c))
    {| world_model := m; world_valuation := rho; active_product := 0; world_bounds := old |}
    {| world_model := m; world_valuation := tau; active_product := 0;
       world_bounds := left_unfold_bounds j u c old n |}
    (left_unfold_trace j u c).
Proof.
  intro Hn.
  assert (forall a b, In (a,b) (left_body_edges u c) ->
    left_unfold_bounds j u c old n b < old a) as Hbody.
  { intros a b H; apply in_map_iff in H; destruct H as [k [E Hk]]; inversion E; subst.
    apply predicate_positions_range in Hk.
    rewrite left_bounds_child, Hn; [lia|]. unfold left_copy_position.
    rewrite left_body_length; lia. }
  split; unfold rank; cbn [world_bounds]; intros a b H.
  - change (In (a,b) (left_body_edges u c ++
      (List.length (unfold_prefix u), left_copy_position j u c) ::
      left_context_edges j u c)) in H.
    apply in_app_or in H; destruct H as [H|H]; [pose proof (Hbody _ _ H); lia|].
    destruct H as [E|H].
    + inversion E; subst; rewrite left_bounds_copy; lia.
    + unfold left_context_edges in H; apply in_app_or in H; destruct H as [H|H];
        apply in_map_iff in H; destruct H as [k [E Hk]]; inversion E; subst.
      * change (left_unfold_bounds j u c old n (S (left_copy_position j u c)+a) <= old a).
        rewrite (left_bounds_prefix j u c old n a); [lia|].
        apply predicate_positions_range in Hk; lia.
      * change (left_unfold_bounds j u c old n
          (S (left_copy_position j u c)+List.length (unfold_prefix u)+k) <=
          old (S (List.length (unfold_prefix u))+k)).
        rewrite left_bounds_suffix; lia.
  - exact (Hbody _ _ H).
Qed.

Lemma left_unfold_truth d j u c m rho witness old n :
  In (unfold_source_product u) (antecedent j) ->
  List.length (head c) = List.length (unfold_arguments u) ->
  bounded_product d m rho old 0 (unfold_source_product u) ->
  old (List.length (unfold_prefix u)) = S n ->
  map (eval_term m witness) (head c) = map (eval_term m rho) (unfold_arguments u) ->
  eval_product_with m (stage d m n) witness (body c) ->
  bounded_product d m (extend_left m (unfolding_start j) rho witness)
    (left_unfold_bounds j u c old n) 0 (left_unfold_product j u c).
Proof.
  intros Hj Hlen Hsource Hn Hhead Hbody.
  set (tau := extend_left m (unfolding_start j) rho witness).
  assert (forall x, In x (sequent_vars j) -> tau x = rho x) as Hold.
  { intros x Hx; apply extend_left_old; apply fresh_id_gt; exact Hx. }
  assert (forall x, In x (product_vars (unfold_source_product u)) -> rho x = tau x) as Hvars.
  { intros x Hx; symmetry; apply Hold. unfold sequent_vars; apply in_or_app; left.
    unfold formula_vars; apply in_concat; exists (product_vars (unfold_source_product u));
      split; [apply in_map; exact Hj|exact Hx]. }
  assert (forall x, In x (List.concat (map term_vars (unfold_arguments u))) -> rho x = tau x) as Hargs.
  { intros x Hx; apply Hvars. unfold unfold_source_product, product_vars.
    rewrite map_app, concat_app; apply in_or_app; right; cbn [unfold_principal atom_vars].
    apply in_or_app; now left. }
  assert (map (eval_term m tau) (unfold_arguments u) =
    map (eval_term m rho) (unfold_arguments u)) as Eargs.
  { apply map_ext_in; intros t Ht; apply eval_term_ext; intros x Hx; symmetry; apply Hargs.
    apply in_concat; exists (term_vars t); split; [apply in_map; exact Ht|exact Hx]. }
  unfold unfold_source_product in Hsource.
  apply bounded_product_app in Hsource; destruct Hsource as [Hpre [Hprincipal Hpost]].
  cbn in Hprincipal. rewrite Nat.add_0_l in Hpost.
  unfold left_unfold_product. rewrite !bounded_product_app.
  split.
  - assert (eval_product_with m (stage d m n) tau (left_unfold_body j u c)) as HB.
    { apply (proj2 (eval_retag_product m (stage d m n) tau (unfold_logical_tag u) _)).
      apply eval_left_body; exact Hbody. }
    apply (proj1 (bounded_product_ext d m tau tau (fun _ => n)
      (left_unfold_bounds j u c old n) 0 0 (left_unfold_body j u c)
      ltac:(intros; reflexivity) ltac:(intros k Hk; cbn; symmetry; apply left_bounds_child;
        unfold left_copy_position; lia))).
    apply bounded_product_uniform; exact HB.
  - split.
    + assert (eval_product_with m (stage d m n) tau (left_unfold_equalities j u c)) as HE.
      { apply head_equations_eval.
        - unfold left_unfold_equalities; cbn [left_clause head]; rewrite length_map; lia.
        - unfold left_unfold_equalities. change (map (eval_term m tau) (unfold_arguments u) =
            map (eval_term m tau) (map (rename_term (left_variable (unfolding_start j))) (head c))).
          rewrite Eargs, map_map. rewrite <- Hhead. apply map_ext; intro t; symmetry; apply eval_left_term. }
      apply (proj1 (bounded_product_ext d m tau tau (fun _ => n)
        (left_unfold_bounds j u c old n) (List.length (left_unfold_body j u c))
        (0+List.length (left_unfold_body j u c)) (left_unfold_equalities j u c)
        ltac:(intros; reflexivity) ltac:(intros k Hk; symmetry; apply left_bounds_child;
          unfold left_copy_position; lia))).
      apply bounded_product_uniform; exact HE.
    + replace (0 + List.length (left_unfold_body j u c) +
        List.length (left_unfold_equalities j u c)) with (left_copy_position j u c) by reflexivity.
      split.
      * cbn [bounded_product eval_atom_with]. split; [|exact I].
        rewrite left_bounds_copy, Eargs. exact Hprincipal.
      * split.
        -- apply (proj1 (bounded_product_ext d m rho tau old (left_unfold_bounds j u c old n)
             0 (left_copy_position j u c + 1) (unfold_prefix u)
             ltac:(intros x Hx; apply Hvars; unfold unfold_source_product, product_vars;
               rewrite map_app, concat_app; apply in_or_app; now left)
             ltac:(intros k Hk; rewrite Nat.add_0_l; symmetry;
               replace (left_copy_position j u c+1+k) with (S (left_copy_position j u c)+k) by lia;
               apply left_bounds_prefix; exact Hk))); exact Hpre.
        -- apply (proj1 (bounded_product_ext d m rho tau old (left_unfold_bounds j u c old n)
             (S (List.length (unfold_prefix u)))
             (left_copy_position j u c + 1 + List.length (unfold_prefix u)) (unfold_suffix u)
             ltac:(intros x Hx; apply Hvars; unfold unfold_source_product, product_vars;
               rewrite map_app, concat_app; apply in_or_app; right; cbn;
               apply in_or_app; now right)
             ltac:(intros k Hk; symmetry;
               replace (left_copy_position j u c+1+List.length (unfold_prefix u)+k) with
                 (S (left_copy_position j u c)+List.length (unfold_prefix u)+k) by lia;
               apply left_bounds_suffix))); exact Hpost.
Qed.

Lemma clauses_for_member d name c : In c d -> clause_name c = name -> In c (clauses_for d name).
Proof. intros Hc Hn; unfold clauses_for; apply filter_In; split; auto; apply String.eqb_eq; exact Hn. Qed.
Definition informative_index {A : Type} (xs : list A) x (H : In x xs) :
  {k : nat | nth_error xs k = Some x} :=
  constructive_indefinite_description _ (In_nth_error xs x H).

Theorem left_unfold_evidence d j u :
  antecedent j = [unfold_source_product u] ->
  (forall c, In c (clauses_for d (unfold_symbol u)) ->
    List.length (head c) = List.length (unfold_arguments u)) ->
  local_evidence d (left_unfold_application d j u).
Proof.
  intros Hj Harity; constructor; intros [m rho active old] Hbad.
  pose proof (counterexample_parts d j _ Hbad) as Hparts.
  assert (active = 0) as Eactive.
  { destruct Hparts as [[p [Hp _]] _]; cbn in Hp; rewrite Hj in Hp.
    destruct active as [|active]; [reflexivity|destruct active; discriminate]. }
  subst active.
  assert (bounded_product d m rho old 0 (unfold_source_product u)) as Htruth.
  { destruct Hparts as [[p [Hp Htruth]] _]; cbn in Hp; rewrite Hj in Hp.
    inversion Hp; subst p; exact Htruth. }
  pose proof (proj2 Hparts) as Hright.
  assert (stage d m (old (List.length (unfold_prefix u))) (unfold_symbol u)
    (map (eval_term m rho) (unfold_arguments u))) as Hprincipal.
  { unfold unfold_source_product in Htruth. apply bounded_product_app in Htruth.
    destruct Htruth as [_ [H _]]; exact H. }
  destruct (old (List.length (unfold_prefix u))) as [|n] eqn:En;
    [contradiction|].
  assert (exists cr : clause * valuation m,
    In (fst cr) (clauses_for d (unfold_symbol u)) /\
    map (eval_term m (snd cr)) (head (fst cr)) =
      map (eval_term m rho) (unfold_arguments u) /\
    eval_product_with m (stage d m n) (snd cr) (body (fst cr))) as Hchoose.
  { destruct Hprincipal as [c [Hc [Hname [witness [Hhead Hbody]]]]].
    exists (c,witness); cbn; split; [apply clauses_for_member; assumption|auto]. }
  destruct (constructive_indefinite_description _ Hchoose) as [[c witness] [Hc [Hhead Hbody]]].
  cbn in Hc, Hhead, Hbody.
  destruct (informative_index (clauses_for d (unfold_symbol u)) c Hc) as [k Hk].
  set (tau := extend_left m (unfolding_start j) rho witness).
  set (w' := {| world_model := m; world_valuation := tau; active_product := 0;
    world_bounds := left_unfold_bounds j u c old n |}).
  exists k, (left_unfold_premise j u c), w'.
  split.
  - change (nth_error (map (left_unfold_premise j u) (clauses_for d (unfold_symbol u))) k =
      Some (left_unfold_premise j u c)).
    rewrite nth_error_map, Hk; reflexivity.
  - split.
    + intro Hden. apply Hright.
      apply (proj2 (eval_right_ext d m rho tau (succedent j)
        ltac:(intros id Hid; symmetry; apply extend_left_old; apply fresh_id_gt;
          unfold sequent_vars; apply in_or_app; now right))).
      apply Hden. exists (left_unfold_product j u c); split; [reflexivity|].
      eapply left_unfold_truth; [rewrite Hj; now left|apply Harity; exact Hc|exact Htruth|exact En|exact Hhead|exact Hbody].
    + apply left_unfold_respects; exact En.
Qed.

Theorem right_unfold_check_sound d j u c : right_unfold_check d j u c = true ->
  local_evidence d (right_unfold_application j u c).
Proof.
  intro H; unfold right_unfold_check in H; rewrite !andb_true_iff in H.
  destruct H as [[[[[_ Hp] Hc] Hname] Hlen] _].
  assert (In (unfold_source_product u) (succedent j)) as Hp'.
  { apply existsb_exists in Hp; destruct Hp as [p [Hp Ep]];
      apply eqb_of_dec_spec in Ep; subst p; exact Hp. }
  assert (In c d) as Hc'.
  { apply existsb_exists in Hc; destruct Hc as [c' [Hc Ec]];
      apply eqb_of_dec_spec in Ec; subst c'; exact Hc. }
  apply String.eqb_eq in Hname; apply Nat.eqb_eq in Hlen.
  apply right_unfold_evidence; assumption.
Qed.
Theorem left_unfold_check_sound d j u : left_unfold_check d j u = true ->
  local_evidence d (left_unfold_application d j u).
Proof.
  intro H; unfold left_unfold_check in H; rewrite !andb_true_iff in H.
  destruct H as [[_ Hj] Ha].
  apply sequent_eqb_spec in Hj.
  apply left_unfold_evidence.
  - rewrite Hj; reflexivity.
  - intros c Hc; apply forallb_forall with (x:=c) in Ha; auto.
    apply andb_true_iff in Ha; destruct Ha as [Ha _]; now apply Nat.eqb_eq.
Qed.

Definition certify_left_unfold d j u (H : left_unfold_check d j u = true) :
  certified_application d j := {| certified_rule := left_unfold_application d j u;
  certified_conclusion := eq_refl; certified_evidence := left_unfold_check_sound d j u H |}.
Definition certify_right_unfold d j u c (H : right_unfold_check d j u c = true) :
  certified_application d j := {| certified_rule := right_unfold_application j u c;
  certified_conclusion := eq_refl; certified_evidence := right_unfold_check_sound d j u c H |}.
Definition checked_left_unfold d j u : option (certified_application d j) :=
  match left_unfold_check d j u as b return left_unfold_check d j u = b -> _ with
  | true => fun H => Some (certify_left_unfold d j u H)
  | false => fun _ => None end eq_refl.
Definition checked_right_unfold d j u c : option (certified_application d j) :=
  match right_unfold_check d j u c as b return right_unfold_check d j u c = b -> _ with
  | true => fun H => Some (certify_right_unfold d j u c H)
  | false => fun _ => None end eq_refl.

(** [atom_descriptors] enumerates positions, not atom equality classes: repeated
    identical predicates yield separate candidates with different prefixes. *)
Fixpoint atom_descriptors_from pre p : list unfold_atom_descriptor := match p with
  | [] => []
  | a::post =>
    (match a with Pred tag name args => [{| unfold_prefix := pre; unfold_suffix := post;
      unfold_logical_tag := tag; unfold_symbol := name; unfold_arguments := args |}]
    | _ => [] end) ++ atom_descriptors_from (pre++[a]) post end.
Definition atom_descriptors p := atom_descriptors_from [] p.
Definition option_list {A} (o : option A) := match o with Some a => [a] | None => [] end.
Definition singleton_left_unfold_rules d j : list (certified_application d j) :=
  flat_map (fun u => option_list (checked_left_unfold d j u))
    (flat_map atom_descriptors (antecedent j)).
Definition right_unfold_rules d j : list (certified_application d j) :=
  flat_map (fun u => flat_map (fun c => option_list (checked_right_unfold d j u c)) d)
    (flat_map atom_descriptors (succedent j)).

(** Disjunctive left unfolding.  The chosen product is unfolded into all its
    clause cases; each other product has a pass-through premise.  This is
    necessary even when the chosen symbol has no defining clauses. *)
Definition product_offset j i := List.length (List.concat (firstn i (antecedent j))).
Definition rebase_edge offset e := {|
  continuations := map (fun ab => (offset+fst ab, snd ab)) (continuations e);
  progressing := map (fun ab => (offset+fst ab, snd ab)) (progressing e) |}.
Definition rebase_premise offset p := {| premise_label := premise_label p;
  premise_trace := rebase_edge offset (premise_trace p) |}.
Lemma rebase_respects d source target w relative w' offset e :
  (forall k, world_bounds relative k = world_bounds w (offset+k)) ->
  respects d source target relative w' e ->
  respects d source target w w' (rebase_edge offset e).
Proof.
  intros Hbounds [Hle Hlt]; split; intros a b H;
    apply in_map_iff in H; destruct H as [[x y] [E Hin]]; cbn in E; inversion E; subst;
    unfold rank in *; rewrite <- Hbounds; [apply Hle|apply Hlt]; exact Hin.
Qed.
Definition passthrough_trace offset p := {|
  continuations := map (fun k => (offset+k,k)) (predicate_positions 0 p);
  progressing := [] |}.
Definition passthrough_premise j i := {| premise_label := {|
  antecedent := [nth i (antecedent j) []]; succedent := succedent j |};
  premise_trace := passthrough_trace (product_offset j i) (nth i (antecedent j) []) |}.
Definition other_product_indices j selected :=
  filter (fun i => negb (Nat.eqb i selected)) (seq 0 (List.length (antecedent j))).
Definition passthrough_premises j selected := map (passthrough_premise j)
  (other_product_indices j selected).
Definition left_unfold_at_application d j selected u := {|
  application_name := "left_unfold_contract"; conclusion := j;
  premises := map (fun c => rebase_premise (product_offset j selected) (left_unfold_premise j u c))
    (clauses_for d (unfold_symbol u)) ++ passthrough_premises j selected |}.
Definition left_unfold_at_check d j selected u :=
  antecedent_freeb j &&
  (match nth_error (antecedent j) selected with
    | Some p => product_eqb p (unfold_source_product u) | None => false end) &&
  forallb (fun c => Nat.eqb (List.length (head c)) (List.length (unfold_arguments u)) &&
    left_clause_freshb j c)
    (clauses_for d (unfold_symbol u)).

Lemma bounded_product_relocate d m rho old offset p :
  bounded_product d m rho old offset p ->
  bounded_product d m rho (fun k => old (offset+k)) 0 p.
Proof.
  intro H; apply (proj1 (bounded_product_ext d m rho rho old
    (fun k => old (offset+k)) offset 0 p ltac:(intros; reflexivity)
    ltac:(intros; rewrite Nat.add_0_l; reflexivity))); exact H.
Qed.
Lemma passthrough_respects d j i m rho active old :
  respects d j (premise_label (passthrough_premise j i))
    {| world_model := m; world_valuation := rho; active_product := active; world_bounds := old |}
    {| world_model := m; world_valuation := rho; active_product := 0;
      world_bounds := fun k => old (product_offset j i+k) |}
    (premise_trace (passthrough_premise j i)).
Proof.
  split; intros a b H; [|contradiction].
  apply in_map_iff in H; destruct H as [k [E Hk]]; inversion E; subst; unfold rank; cbn; lia.
Qed.

Theorem left_unfold_at_evidence d j selected u :
  nth_error (antecedent j) selected = Some (unfold_source_product u) ->
  (forall c, In c (clauses_for d (unfold_symbol u)) ->
    List.length (head c) = List.length (unfold_arguments u)) ->
  local_evidence d (left_unfold_at_application d j selected u).
Proof.
  intros Hselected Harity; constructor; intros [m rho active old] Hbad.
  pose proof (counterexample_parts d j _ Hbad) as Hparts.
  pose proof (proj2 Hparts) as Hright.
  destruct (Nat.eq_dec active selected) as [Eactive|Eactive].
  - subst active.
    set (offset := product_offset j selected).
    set (relative := fun k => old (offset+k)).
    assert (bounded_product d m rho relative 0 (unfold_source_product u)) as Htruth.
    { destruct Hparts as [[p [Hp Htruth]] _]; cbn in Hp.
      rewrite Hselected in Hp; inversion Hp; subst p.
      apply bounded_product_relocate; exact Htruth. }
    assert (stage d m (relative (List.length (unfold_prefix u))) (unfold_symbol u)
      (map (eval_term m rho) (unfold_arguments u))) as Hprincipal.
    { unfold unfold_source_product in Htruth. apply bounded_product_app in Htruth.
      destruct Htruth as [_ [H _]]; exact H. }
    destruct (relative (List.length (unfold_prefix u))) as [|n] eqn:En; [contradiction|].
    assert (exists cr : clause * valuation m,
      In (fst cr) (clauses_for d (unfold_symbol u)) /\
      map (eval_term m (snd cr)) (head (fst cr)) = map (eval_term m rho) (unfold_arguments u) /\
      eval_product_with m (stage d m n) (snd cr) (body (fst cr))) as Hchoose.
    { destruct Hprincipal as [c [Hc [Hname [witness [Hhead Hbody]]]]].
      exists (c,witness); cbn; split; [apply clauses_for_member; assumption|auto]. }
    destruct (constructive_indefinite_description _ Hchoose) as [[c witness] [Hc [Hhead Hbody]]].
    cbn in Hc, Hhead, Hbody.
    destruct (informative_index (clauses_for d (unfold_symbol u)) c Hc) as [k Hk].
    set (tau := extend_left m (unfolding_start j) rho witness).
    set (w' := {| world_model := m; world_valuation := tau; active_product := 0;
      world_bounds := left_unfold_bounds j u c relative n |}).
    exists k, (rebase_premise offset (left_unfold_premise j u c)), w'.
    split.
    + change (nth_error (map (fun c => rebase_premise offset (left_unfold_premise j u c))
        (clauses_for d (unfold_symbol u)) ++ passthrough_premises j selected) k =
        Some (rebase_premise offset (left_unfold_premise j u c))).
      rewrite nth_error_app1.
      * rewrite nth_error_map, Hk; reflexivity.
      * rewrite length_map. apply nth_error_Some; rewrite Hk; discriminate.
    + split.
      * intro Hden; apply Hright.
        apply (proj2 (eval_right_ext d m rho tau (succedent j)
          ltac:(intros id Hid; symmetry; apply extend_left_old; apply fresh_id_gt;
            unfold sequent_vars; apply in_or_app; now right))).
        apply Hden. exists (left_unfold_product j u c); split; [reflexivity|].
        eapply left_unfold_truth; [eapply nth_error_In; exact Hselected|apply Harity; exact Hc|
          exact Htruth|exact En|exact Hhead|exact Hbody].
      * eapply rebase_respects with
          (relative := {| world_model := m; world_valuation := rho;
             active_product := 0; world_bounds := relative |}).
        -- intros k'; reflexivity.
        -- apply left_unfold_respects; exact En.
  - assert (active < List.length (antecedent j)) as Hactive.
    { destruct Hparts as [[p [Hp _]] _]; cbn in Hp.
      apply nth_error_Some; rewrite Hp; discriminate. }
    assert (In active (other_product_indices j selected)) as Hin.
    { unfold other_product_indices; apply filter_In; split;
        [apply in_seq; lia|apply negb_true_iff; apply Nat.eqb_neq; exact Eactive]. }
    destruct (informative_index (other_product_indices j selected) active Hin) as [k Hk].
    set (w' := {| world_model := m; world_valuation := rho; active_product := 0;
      world_bounds := fun k => old (product_offset j active+k) |}).
    exists (List.length (clauses_for d (unfold_symbol u))+k), (passthrough_premise j active), w'.
    split.
    + change (nth_error (map (fun c => rebase_premise (product_offset j selected)
          (left_unfold_premise j u c)) (clauses_for d (unfold_symbol u)) ++
          passthrough_premises j selected) (List.length (clauses_for d (unfold_symbol u))+k) =
          Some (passthrough_premise j active)).
      rewrite nth_error_app2, length_map by (rewrite length_map; lia).
      replace (List.length (clauses_for d (unfold_symbol u))+k-
        List.length (clauses_for d (unfold_symbol u))) with k by lia.
      unfold passthrough_premises; rewrite nth_error_map, Hk; reflexivity.
    + split.
      * intro Hden; apply Hright; apply Hden.
        exists (nth active (antecedent j) []); split; [reflexivity|].
        apply bounded_product_relocate.
        destruct Hparts as [[p [Hp Htruth]] _]; cbn in Hp.
        change (bounded_product d m rho old (product_offset j active) (nth active (antecedent j) [])).
        replace (nth active (antecedent j) []) with p by
          (symmetry; exact (nth_error_nth _ _ [] Hp)); exact Htruth.
      * apply passthrough_respects.
Qed.
Theorem left_unfold_at_check_sound d j selected u : left_unfold_at_check d j selected u = true ->
  local_evidence d (left_unfold_at_application d j selected u).
Proof.
  intro H; unfold left_unfold_at_check in H; rewrite !andb_true_iff in H.
  destruct H as [[_ Hselected] Ha].
  assert (nth_error (antecedent j) selected = Some (unfold_source_product u)) as Hsel.
  { destruct (nth_error (antecedent j) selected) as [p|] eqn:E; [|discriminate].
    apply eqb_of_dec_spec in Hselected; now subst p. }
  apply left_unfold_at_evidence; [exact Hsel|].
  intros c Hc; apply forallb_forall with (x:=c) in Ha; auto.
  apply andb_true_iff in Ha; destruct Ha as [Ha _]; now apply Nat.eqb_eq.
Qed.
Definition certify_left_unfold_at d j selected u (H : left_unfold_at_check d j selected u = true) :
  certified_application d j := {| certified_rule := left_unfold_at_application d j selected u;
    certified_conclusion := eq_refl; certified_evidence := left_unfold_at_check_sound d j selected u H |}.
Definition checked_left_unfold_at d j selected u : option (certified_application d j) :=
  match left_unfold_at_check d j selected u as b return left_unfold_at_check d j selected u = b -> _ with
  | true => fun H => Some (certify_left_unfold_at d j selected u H)
  | false => fun _ => None end eq_refl.
Definition left_unfold_rules d j : list (certified_application d j) :=
  flat_map (fun i => flat_map (fun u => option_list (checked_left_unfold_at d j i u))
    (atom_descriptors (nth i (antecedent j) []))) (seq 0 (List.length (antecedent j))).

(** An arbitrary simultaneous substitution is applied ONLY to the fresh clause,
    not to the goal or its context.  No restriction on [theta] is needed for
    soundness: all instantiated-head/occurrence equalities are retained.
    In particular, duplicate bindings, non-matching substitutions, and bindings
    to goal variables are covered by the same folding theorem. *)
Definition right_unfold_instance_clause j c theta :=
  subst_clause theta (right_clause (unfolding_start j) c).
Definition right_unfold_instance_product j u c theta :=
  unfold_prefix u ++
  head_equations (unfold_arguments u) (head (right_unfold_instance_clause j c theta)) ++
  body (right_unfold_instance_clause j c theta) ++ unfold_suffix u.
Definition right_unfold_instance_label j u c theta := {| antecedent := antecedent j;
  succedent := replace_product (unfold_source_product u) (right_unfold_instance_product j u c theta)
    (succedent j) |}.
Definition right_unfold_instance_application j u c theta := {|
  application_name := "right_unfold_instance"; conclusion := j;
  premises := [{| premise_label := right_unfold_instance_label j u c theta;
    premise_trace := identity_trace j |}] |}.
Definition right_unfold_instance_check d j u c (_ : substitution) := right_unfold_check d j u c.

Lemma eval_right_instance_term m start theta rho t :
  eval_term m rho (subst_term theta (rename_term (right_variable start) t)) =
  eval_term m (fun x => subst_valuation m theta rho (right_variable start x)) t.
Proof. rewrite eval_subst_term, eval_rename_term; reflexivity. Qed.
Lemma eval_right_instance_body d m start theta rho p :
  eval_product d m rho (subst_product theta (rename_product (right_variable start) p)) <->
  eval_product d m (fun x => subst_valuation m theta rho (right_variable start x)) p.
Proof.
  rewrite eval_subst_product.
  apply eval_rename_product.
Qed.
Lemma right_unfold_instance_product_folds d j u c theta m rho : In c d ->
  clause_name c = unfold_symbol u ->
  List.length (head c) = List.length (unfold_arguments u) ->
  eval_product d m rho (right_unfold_instance_product j u c theta) ->
  eval_product d m rho (unfold_source_product u).
Proof.
  intros Hc Hname Hlen Htruth.
  unfold right_unfold_instance_product, eval_product, eval_product_with in Htruth.
  rewrite !Forall_app in Htruth.
  destruct Htruth as [Hpre [Heqs [Hbody Hpost]]].
  unfold unfold_source_product, eval_product, eval_product_with.
  rewrite Forall_app, Forall_cons_iff. split; [exact Hpre|].
  split; [|exact Hpost]. unfold unfold_principal; cbn [eval_atom_with].
  apply inductive_unfold. exists c; split; [exact Hc|]. split; [exact Hname|].
  exists (fun x => subst_valuation m theta rho (right_variable (unfolding_start j) x)); split.
  - apply head_equations_eval in Heqs.
    + change (map (eval_term m rho) (unfold_arguments u) =
        map (eval_term m rho) (map (subst_term theta)
          (map (rename_term (right_variable (unfolding_start j))) (head c)))) in Heqs.
      rewrite !map_map in Heqs.
      rewrite Heqs; apply map_ext; intro t; symmetry; apply eval_right_instance_term.
    + change (List.length (unfold_arguments u) = List.length (map (subst_term theta)
        (map (rename_term (right_variable (unfolding_start j))) (head c)))).
      rewrite !length_map; lia.
  - exact (proj1 (eval_right_instance_body d m (unfolding_start j) theta rho (body c)) Hbody).
Qed.
Lemma right_unfold_instance_implies d j u c theta : In c d ->
  In (unfold_source_product u) (succedent j) ->
  clause_name c = unfold_symbol u ->
  List.length (head c) = List.length (unfold_arguments u) ->
  forall m rho, eval_right d m rho (succedent (right_unfold_instance_label j u c theta)) ->
    eval_right d m rho (succedent j).
Proof.
  intros Hc Hsource Hname Hlen m rho [p [Hp [sigma [Hfree Htruth]]]].
  cbn [right_unfold_instance_label replace_product] in Hp.
  destruct Hp as [<-|Hp].
  - exists (unfold_source_product u); split; [exact Hsource|].
    exists sigma; split; [exact Hfree|]. eapply right_unfold_instance_product_folds; eauto.
  - apply filter_In in Hp; destruct Hp as [Hp _].
    exists p; split; [exact Hp|]. exists sigma; auto.
Qed.
Theorem right_unfold_instance_evidence d j u c theta : In c d ->
  In (unfold_source_product u) (succedent j) ->
  clause_name c = unfold_symbol u ->
  List.length (head c) = List.length (unfold_arguments u) ->
  local_evidence d (right_unfold_instance_application j u c theta).
Proof.
  intros Hc Hp Hname Hlen; constructor; intros w Hbad.
  exists 0, {| premise_label := right_unfold_instance_label j u c theta;
    premise_trace := identity_trace j |}, w.
  split; [reflexivity|]. split.
  - intro Hden; apply Hbad; intro Hleft.
    eapply right_unfold_instance_implies; eauto.
  - apply identity_trace_respects.
Qed.
Theorem right_unfold_instance_check_sound d j u c theta :
  right_unfold_instance_check d j u c theta = true ->
  local_evidence d (right_unfold_instance_application j u c theta).
Proof.
  intro H; unfold right_unfold_instance_check, right_unfold_check in H.
  rewrite !andb_true_iff in H; destruct H as [[[[[_ Hp] Hc] Hname] Hlen] _].
  assert (In (unfold_source_product u) (succedent j)) as Hp'.
  { apply existsb_exists in Hp; destruct Hp as [p [Hp Ep]];
      apply eqb_of_dec_spec in Ep; subst p; exact Hp. }
  assert (In c d) as Hc'.
  { apply existsb_exists in Hc; destruct Hc as [c' [Hc Ec]];
      apply eqb_of_dec_spec in Ec; subst c'; exact Hc. }
  apply String.eqb_eq in Hname; apply Nat.eqb_eq in Hlen.
  apply right_unfold_instance_evidence; assumption.
Qed.
Definition certify_right_unfold_instance d j u c theta
  (H : right_unfold_instance_check d j u c theta = true) : certified_application d j := {|
  certified_rule := right_unfold_instance_application j u c theta;
  certified_conclusion := eq_refl;
  certified_evidence := right_unfold_instance_check_sound d j u c theta H |}.
Definition checked_right_unfold_instance d j u c theta : option (certified_application d j) :=
  match right_unfold_instance_check d j u c theta as b
    return right_unfold_instance_check d j u c theta = b -> _ with
  | true => fun H => Some (certify_right_unfold_instance d j u c theta H)
  | false => fun _ => None end eq_refl.

(** The repeated-head matcher is only a candidate generator.  Its returned
    equalities can be ignored because the instance schema reconstructs EVERY
    head equality after applying the final simultaneous substitution.  Thus
    neither matching success nor a matcher correctness theorem is trusted. *)
Definition right_unfold_matched_substitution fuel j u c : option substitution :=
  match head_match_terms fuel [] (head (right_clause (unfolding_start j) c)) (unfold_arguments u) with
  | Some (theta, _) => Some theta | None => None end.
Definition right_unfold_matched_application fuel j u c : option application :=
  match right_unfold_matched_substitution fuel j u c with
  | Some theta => Some (right_unfold_instance_application j u c theta) | None => None end.
Definition checked_right_unfold_matched fuel d j u c : option (certified_application d j) :=
  match right_unfold_matched_substitution fuel j u c with
  | Some theta => checked_right_unfold_instance d j u c theta | None => None end.
Definition right_unfold_matched_rules fuel d j : list (certified_application d j) :=
  flat_map (fun u => flat_map (fun c => option_list (checked_right_unfold_matched fuel d j u c)) d)
    (flat_map atom_descriptors (succedent j)).
