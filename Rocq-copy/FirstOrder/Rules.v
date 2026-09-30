From Stdlib Require Import List Bool Arith Lia String Classical_Prop.
From Stdlib Require Import Logic.ClassicalEpsilon Logic.ClassicalDescription.

From CyclistRocq.FirstOrder Require Import Syntax Semantics.

Import ListNotations.
Open Scope string_scope.

Definition empty_edge : Cyclic.edge_info :=
  {| Cyclic.edge_valid := []; Cyclic.edge_progress := [] |}.

Definition identity_edge (j : judgment) : Cyclic.edge_info :=
  {| Cyclic.edge_valid := Cyclic.identity_pairs (judgment_tags j);
     Cyclic.edge_progress := [] |}.

Lemma in_identity_pairs_eq a b ts :
  In (a, b) (Cyclic.identity_pairs ts) -> a = b.
Proof.
  unfold Cyclic.identity_pairs. intro H. apply in_map_iff in H.
  destruct H as [t [H _]]. inversion H. reflexivity.
Qed.

Lemma empty_edge_respects source target w w' :
  Cyclic.respects_edge source target w w' empty_edge.
Proof. split; intros a b H; inversion H. Qed.

Lemma identity_edge_respects_same_lhs ds lhs rhs rhs' w :
  Cyclic.respects_edge
    (mk_judgment ds (mk_sequent lhs rhs))
    (mk_judgment ds (mk_sequent lhs rhs'))
    w w (identity_edge (mk_judgment ds (mk_sequent lhs rhs))).
Proof.
  split.
  - intros a b Hin. apply in_identity_pairs_eq in Hin. subst b.
    apply Nat.le_refl.
  - intros a b Hin. inversion Hin.
Qed.

Lemma product_holds_atom i rho p a :
  product_holds i rho p -> In a p -> atom_holds i rho a.
Proof.
  revert a. induction p as [|x p IH]; simpl; intros a Hp Hin.
  - contradiction.
  - destruct Hp as [Hx Hp]. destruct Hin as [-> | Hin]; auto.
Qed.

Lemma product_holds_subset i rho small big :
  (forall a, In a small -> In a big) ->
  product_holds i rho big ->
  product_holds i rho small.
Proof.
  intros Hsub Hbig. induction small as [|a small IH]; simpl; [exact I|].
  split.
  - eapply product_holds_atom; [exact Hbig|]. apply Hsub. now left.
  - apply IH. intros x Hx. apply Hsub. now right.
Qed.

Lemma formula_holds_cons_intro i rho p rest :
  product_holds i rho p -> formula_holds i rho (p :: rest).
Proof. intro H. exists p. split; [now left|exact H]. Qed.

Lemma formula_holds_singleton_inv i rho p :
  formula_holds i rho [p] -> product_holds i rho p.
Proof.
  intros [q [[-> | H] Hq]]; [exact Hq|contradiction].
Qed.

Definition choose_formula_product i rho f
    (H : formula_holds i rho f)
    : { p : product | In p f /\ product_holds i rho p }.
Proof.
  refine (exist _
    (epsilon (inhabits [])
      (fun p => In p f /\ product_holds i rho p)) _).
  apply epsilon_spec. exact H.
Defined.

(** One-clause right unfolding.  The selected predicate product is kept at
    the front of the disjunction; the remaining products are [alternatives].
    Definition variables become fresh existential witnesses. *)
Definition right_unfold_product
    (offset : nat) (name : string) (args : list term)
    (context : product) (c : clause) : product :=
  (existential_shift_product offset c.(clause_body) ++
   equation_product args (map (existential_shift_term offset) c.(clause_head)) ++
   context)%list.

Definition right_unfold_judgment
    (ds : definitions) (offset : nat) (lhs : formula)
    (name : string) (args : list term) (context : product)
    (alternatives : formula) (c : clause) : judgment :=
  mk_judgment ds
    (mk_sequent lhs
      (right_unfold_product offset name args context c :: alternatives)).

Lemma right_unfold_product_holds
    ds i base witness offset tag name args context c :
  models ds i ->
  In c (lookup_definition name ds) ->
  List.length args = List.length c.(clause_head) ->
  product_holds i (merge_valuation base witness)
    (right_unfold_product offset name args context c) ->
  product_holds i (merge_valuation base witness)
    (Pred tag name args :: context).
Proof.
  intros Hmodel Hin Harity Htarget.
  unfold right_unfold_product in Htarget.
  apply (proj1 (product_holds_app _ _ _ _)) in Htarget as [Hbody Hrest].
  apply (proj1 (product_holds_app _ _ _ _)) in Hrest as [Hequations Hcontext].
  simpl. split; [|exact Hcontext].
  destruct Hmodel as [Hintro _]. unfold atom_holds.
  pose proof (proj1 (product_holds_existential_shift offset i base witness
    c.(clause_body)) Hbody) as Hclause.
  pose proof (Hintro name c (existential_clause_valuation offset base witness)
    Hin Hclause) as Hpredicate.
  unfold predicate_holds in Hpredicate |- *.
  destruct Hpredicate as [height Hheight]. exists height.
  pose proof (equation_product_holds_inv i (merge_valuation base witness)
    args (map (existential_shift_term offset) c.(clause_head))
    ltac:(now rewrite length_map) Hequations) as Heval.
  rewrite eval_existential_shift_terms in Heval.
  now rewrite Heval.
Qed.

Lemma right_unfold_right_transfer
    ds i base offset tag name args context alternatives c :
  models ds i ->
  In c (lookup_definition name ds) ->
  List.length args = List.length c.(clause_head) ->
  right_holds i base
    (right_unfold_product offset name args context c :: alternatives) ->
  right_holds i base ((Pred tag name args :: context) :: alternatives).
Proof.
  intros Hmodel Hin Harity [witness [p [[Hp | Hp] HpHolds]]].
  - subst p. exists witness.
    exists (Pred tag name args :: context). split; [now left|].
    eapply right_unfold_product_holds; eauto.
  - exists witness. exists p. split; [right; exact Hp|exact HpHolds].
Qed.

Definition right_unfold_rule
    (ds : definitions) (offset : nat) (lhs : formula)
    (tag : option nat) (name : string) (args : list term)
    (context : product) (alternatives : formula) (c : clause)
    (Hin : In c (lookup_definition name ds))
    (Harity : List.length args = List.length c.(clause_head))
  : Cyclic.rule_instance.
Proof.
  set (source := mk_judgment ds
    (mk_sequent lhs ((Pred tag name args :: context) :: alternatives))).
  set (target := right_unfold_judgment ds offset lhs name args context
    alternatives c).
  set (p := {| Cyclic.premise_judgment := target;
               Cyclic.premise_edge := identity_edge source |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "R.Unfold";
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := [p] |}.
  - intros Hvalid [i base]. unfold source, denote, sequent_holds; simpl.
    intros Hmodel Hlhs.
    pose proof (Hvalid p ltac:(now left) (i, base)) as Htarget.
    unfold p, target, right_unfold_judgment, denote, sequent_holds in Htarget;
      simpl in Htarget.
    apply right_unfold_right_transfer with (ds := ds) (offset := offset)
      (c := c); try assumption.
    now apply Htarget.
  - intros [i base] Hfalse.
    exists 0, p, (i, base). split; [reflexivity|]. split.
    + unfold p, target, right_unfold_judgment.
      intro Htarget. apply Hfalse.
      unfold source, denote, sequent_holds in *; simpl in *.
      intros Hmodel Hlhs.
      eapply right_unfold_right_transfer with (ds := ds); eauto.
    + unfold p. apply identity_edge_respects_same_lhs.
Defined.

Lemma false_world_parts ds q i rho :
  ~ denote (mk_judgment ds q) (i, rho) ->
  models ds i /\
  formula_holds i rho q.(antecedent) /\
  ~ right_holds i rho q.(succedent).
Proof.
  unfold denote, sequent_holds; simpl.
  intro H.
  destruct (classic (models ds i)) as [Hm|Hm].
  2: exfalso; apply H; tauto.
  destruct (classic (formula_holds i rho q.(antecedent))) as [Hl|Hl].
  2: exfalso; apply H; tauto.
  split; [exact Hm|]. split; [exact Hl|].
  intro Hr. apply H. exact (fun _ _ => Hr).
Qed.

Lemma make_false_world ds q i rho :
  models ds i ->
  formula_holds i rho q.(antecedent) ->
  ~ right_holds i rho q.(succedent) ->
  ~ denote (mk_judgment ds q) (i, rho).
Proof.
  unfold denote, sequent_holds; simpl. intros Hm Hl Hr H.
  apply Hr. apply H; assumption.
Qed.

(** Identity for a singleton antecedent.  The selected right product may be a
    strict subset of the antecedent product. *)
Definition identity_axiom
    (ds : definitions) (big small : product) (right_rest : formula)
    (Hsubset : forall a, In a small -> In a big)
    (Hfree : product_freeb small = true) : Cyclic.axiom_instance.
Proof.
  refine
    {| Cyclic.axiom_name := "Id";
       Cyclic.axiom_conclusion :=
         mk_judgment ds (mk_sequent [big] (small :: right_rest)) |}.
  intros [i rho]. unfold denote, sequent_holds; simpl.
  intros _ Hlhs. apply formula_holds_singleton_inv in Hlhs.
  exists rho. apply formula_holds_cons_intro.
  apply (proj2 (product_holds_merge_free i rho rho small Hfree)).
  eapply product_holds_subset; eauto.
Defined.

Definition identity_axiom_from_check
    (ds : definitions) (big small : product) (right_rest : formula)
    (Hsubset : product_subsetb small big = true)
    (Hfree : product_freeb small = true) : Cyclic.axiom_instance :=
  identity_axiom ds big small right_rest
    (proj1 (product_subsetb_spec small big) Hsubset) Hfree.

Lemma product_holds_neq_refl_false i rho p t :
  In (Neq t t) p -> product_holds i rho p -> False.
Proof.
  intros Hin Hp. pose proof (product_holds_atom i rho p (Neq t t) Hp Hin).
  simpl in H. contradiction.
Qed.

Definition disequality_axiom
    (ds : definitions) (p : product) (rhs : formula) (t : term)
    (Hin : In (Neq t t) p) : Cyclic.axiom_instance.
Proof.
  refine
    {| Cyclic.axiom_name := "Ex Falso";
       Cyclic.axiom_conclusion := mk_judgment ds (mk_sequent [p] rhs) |}.
  intros [i rho]. unfold denote, sequent_holds; simpl.
  intros _ Hlhs. exfalso. apply formula_holds_singleton_inv in Hlhs.
  eapply product_holds_neq_refl_false; eauto.
Defined.

(** Split a disjunctive antecedent one product at a time. *)
Definition left_disjunction_rule
    (ds : definitions) (p : product) (ps rhs : formula)
    : Cyclic.rule_instance.
Proof.
  pose (conclusion := mk_judgment ds (mk_sequent (p :: ps) rhs)).
  pose (leftj := mk_judgment ds (mk_sequent [p] rhs)).
  pose (rightj := mk_judgment ds (mk_sequent ps rhs)).
  set (lp := {| Cyclic.premise_judgment := leftj;
                Cyclic.premise_edge := empty_edge |} : Cyclic.premise).
  set (rp := {| Cyclic.premise_judgment := rightj;
                Cyclic.premise_edge := empty_edge |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "L.Or";
       Cyclic.rule_conclusion := conclusion;
       Cyclic.rule_premises := [lp; rp] |}.
  - intros Hvalid [i rho]. unfold denote, sequent_holds; simpl.
    intros Hmodel [q [[Hq | Hq] Hholds]].
    + subst q.
      pose proof (Hvalid lp ltac:(now left) (i, rho)) as Hv.
      unfold lp, leftj, denote, sequent_holds in Hv; simpl in Hv.
      apply Hv; [exact Hmodel|]. exists p. split; [now left|exact Hholds].
    + pose proof (Hvalid rp ltac:(right; now left) (i, rho)) as Hv.
      unfold rp, rightj, denote, sequent_holds in Hv; simpl in Hv.
      apply Hv; [exact Hmodel|]. exists q. split; assumption.
  - intros [i rho] Hfalse.
    destruct (false_world_parts ds (mk_sequent (p :: ps) rhs) i rho Hfalse)
      as [Hm [Hl Hr]].
    destruct (choose_formula_product i rho (p :: ps) Hl)
      as [q [Hq Hqholds]].
    destruct (product_eq_dec q p) as [-> | Hneq].
    + exists 0, lp, (i, rho). split; [reflexivity|]. split.
      * apply make_false_world; auto. exists p. split; [now left|assumption].
      * apply empty_edge_respects.
    + assert (Hinps : In q ps).
      { destruct Hq as [Heq | Hin].
        - exfalso. apply Hneq. now symmetry.
        - exact Hin. }
      exists 1, rp, (i, rho). split; [reflexivity|]. split.
      * apply make_false_world; auto. exists q. split; [exact Hinps|assumption].
      * apply empty_edge_respects.
Defined.

(** Split a right-hand conjunction.  The rule is used only on the free-variable
    fragment, so the two premise witnesses combine pointwise. *)
Definition right_conjunction_rule
    (ds : definitions) (lhs : formula) (a : atom) (rest : product)
    (Hlhsfree : formula_freeb lhs = true)
    (Hafree : atom_freeb a = true)
    (Hrestfree : product_freeb rest = true) : Cyclic.rule_instance.
Proof.
  pose (conclusion := mk_judgment ds (mk_sequent lhs [a :: rest])).
  pose (aj := mk_judgment ds (mk_sequent lhs [[a]])).
  pose (restj := mk_judgment ds (mk_sequent lhs [rest])).
  set (ap := {| Cyclic.premise_judgment := aj;
                Cyclic.premise_edge := identity_edge conclusion |}
      : Cyclic.premise).
  set (restp := {| Cyclic.premise_judgment := restj;
                   Cyclic.premise_edge := identity_edge conclusion |}
      : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "R.And";
       Cyclic.rule_conclusion := conclusion;
       Cyclic.rule_premises := [ap; restp] |}.
  - intros Hvalid [i rho]. unfold denote, sequent_holds; simpl.
    intros Hmodel Hleft.
    pose proof (Hvalid ap ltac:(now left) (i, rho)) as Hvalid_a.
    pose proof (Hvalid restp ltac:(right; now left) (i, rho)) as Hvalid_rest.
    unfold ap, aj, denote, sequent_holds in Hvalid_a; simpl in Hvalid_a.
    unfold restp, restj, denote, sequent_holds in Hvalid_rest;
      simpl in Hvalid_rest.
    specialize (Hvalid_a Hmodel Hleft).
    specialize (Hvalid_rest Hmodel Hleft).
    apply (proj1 (right_holds_free i rho [[a]] ltac:(simpl; now rewrite Hafree)))
      in Hvalid_a.
    apply (proj1 (right_holds_free i rho [rest]
      ltac:(simpl; now rewrite Hrestfree))) in Hvalid_rest.
    apply formula_holds_singleton_inv in Hvalid_a.
    apply formula_holds_singleton_inv in Hvalid_rest.
    simpl in Hvalid_a. destruct Hvalid_a as [Ha _].
    apply (proj2 (right_holds_free i rho [a :: rest]
      ltac:(simpl; now rewrite Hafree, Hrestfree))).
    exists (a :: rest). split; [now left|]. simpl.
    split; [exact Ha|exact Hvalid_rest].
  - intros [i rho] Hfalse.
    destruct (false_world_parts ds (mk_sequent lhs [a :: rest]) i rho Hfalse)
      as [Hm [Hl Hr]].
    assert (Hprod : ~ product_holds i rho (a :: rest)).
    {
      intro Hp. apply Hr. apply (proj2 (right_holds_free i rho [a :: rest]
        ltac:(simpl; now rewrite Hafree, Hrestfree))).
      exists (a :: rest). split; [now left|exact Hp].
    }
    destruct (excluded_middle_informative (atom_holds i rho a)) as [Ha | Ha].
    + assert (Hrest : ~ product_holds i rho rest).
      { intro Hrest. apply Hprod. simpl. auto. }
      exists 1, restp, (i, rho). split; [reflexivity|]. split.
      * apply make_false_world; auto.
        intro Hright. apply Hrest.
        apply (proj1 (right_holds_free i rho [rest]
          ltac:(simpl; now rewrite Hrestfree))) in Hright.
        now apply formula_holds_singleton_inv in Hright.
      * apply identity_edge_respects_same_lhs.
    + exists 0, ap, (i, rho). split; [reflexivity|]. split.
      * apply make_false_world; auto.
        intro Hright. apply Ha.
        apply (proj1 (right_holds_free i rho [[a]]
          ltac:(simpl; now rewrite Hafree))) in Hright.
        apply formula_holds_singleton_inv in Hright. exact (proj1 Hright).
      * apply identity_edge_respects_same_lhs.
Defined.

(** Exact logical backlink; source and target may differ only in tags.  The
    executable search supplies an occurrence-wise rank-preserving edge. *)
Definition backlink_rule
    (source target : judgment) (edge : Cyclic.edge_info)
    (Hsemantic : forall w, denote source w <-> denote target w)
    (Hrespect : forall w, ~ denote source w ->
       Cyclic.respects_edge source target w w edge) : Cyclic.rule_instance.
Proof.
  set (p := {| Cyclic.premise_judgment := target;
               Cyclic.premise_edge := edge |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "Backlink";
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := [p] |}.
  - intros Hvalid w. apply (proj2 (Hsemantic w)).
    apply Hvalid with (p := p). now left.
  - intros w Hfalse. exists 0, p, w. split; [reflexivity|]. split.
    + intro Htarget. apply Hfalse. apply (proj2 (Hsemantic w)). exact Htarget.
    + apply Hrespect. exact Hfalse.
Defined.

Definition left_unfold_edge (tag fresh : nat) (recursive : bool)
  : Cyclic.edge_info :=
  {| Cyclic.edge_valid :=
       (tag, fresh) :: if recursive then [(tag, tag)] else [];
     Cyclic.edge_progress := if recursive then [(tag, tag)] else [] |}.

Definition left_unfold_product
    (offset tag fresh : nat) (name : string) (args : list term)
    (context : product) (c : clause) : product :=
  let body := retag_product tag (shift_product offset c.(clause_body)) in
  let head := map (shift_term offset) c.(clause_head) in
  (body ++
    Pred (Some fresh) name args ::
    equation_product args head ++ context)%list.

Definition left_unfold_judgment
    (ds : definitions) (offset tag fresh : nat)
    (name : string) (args : list term) (context : product)
    (rhs : formula) (c : clause) : judgment :=
  mk_judgment ds
    (mk_sequent [left_unfold_product offset tag fresh name args context c] rhs).

Definition left_unfold_premise
    (ds : definitions) (offset tag fresh : nat)
    (name : string) (args : list term) (context : product)
    (rhs : formula) (c : clause) : Cyclic.premise :=
  {| Cyclic.premise_judgment :=
       left_unfold_judgment ds offset tag fresh name args context rhs c;
     Cyclic.premise_edge :=
       left_unfold_edge tag fresh (product_has_pred c.(clause_body)) |}.

Definition left_unfold_premises
    (ds : definitions) (offset tag fresh : nat)
    (name : string) (args : list term) (context : product)
    (rhs : formula) (clauses : list clause) : list Cyclic.premise :=
  map (left_unfold_premise ds offset tag fresh name args context rhs) clauses.

Definition default_valuation : valuation := fun _ => VConst 0.

Definition default_clause : clause :=
  {| clause_body := []; clause_head := [] |}.

Definition choose_predicate_height i name args
    (H : predicate_holds i name args)
    : { height : nat | i.(predicate_rank) name args = Some height }.
Proof.
  refine (exist _
    (epsilon (inhabits 0)
      (fun height => i.(predicate_rank) name args = Some height)) _).
  apply epsilon_spec. exact H.
Defined.

Definition choose_model_case ds i name args height
    (Hmodel : models ds i)
    (Hrank : i.(predicate_rank) name args = Some height)
    : { cr : clause * valuation |
        In (fst cr) (lookup_definition name ds) /\
        eval_terms (snd cr) (fst cr).(clause_head) = args /\
        product_holds i (snd cr) (fst cr).(clause_body) /\
        body_decreases i (snd cr) (fst cr).(clause_body) height }.
Proof.
  destruct Hmodel as [_ Helim].
  refine (exist _
    (epsilon (inhabits (default_clause, default_valuation))
      (fun cr =>
        In (fst cr) (lookup_definition name ds) /\
        eval_terms (snd cr) (fst cr).(clause_head) = args /\
        product_holds i (snd cr) (fst cr).(clause_body) /\
        body_decreases i (snd cr) (fst cr).(clause_body) height)) _).
  apply epsilon_spec.
  destruct (Helim name args height Hrank) as [c [rho H]].
  now exists (c, rho).
Defined.

Definition choose_clause_index (c : clause) (clauses : list clause)
    (Hin : In c clauses) :
    { index : nat | nth_error clauses index = Some c }.
Proof.
  refine (exist _
    (epsilon (inhabits 0) (fun index => nth_error clauses index = Some c)) _).
  apply epsilon_spec. now apply In_nth_error.
Defined.

Lemma left_unfold_lhs_holds
    i old clause_env offset tag fresh name args context c height :
  product_belowb offset (Pred (Some tag) name args :: context) = true ->
  List.length args = List.length c.(clause_head) ->
  i.(predicate_rank) name (eval_terms old args) = Some height ->
  product_holds i old context ->
  eval_terms clause_env c.(clause_head) = eval_terms old args ->
  product_holds i clause_env c.(clause_body) ->
  product_holds i (combine_valuation offset old clause_env)
    (left_unfold_product offset tag fresh name args context c).
Proof.
  intros Hbelow Harity Hrank Hcontext Hhead Hbody.
  unfold left_unfold_product.
  apply (proj2 (product_holds_app _ _ _ _)). split.
  - apply (proj2 (product_holds_retag _ _ _ _)).
    apply (proj2 (product_holds_shift offset i old clause_env c.(clause_body))).
    exact Hbody.
  - simpl. split.
    + unfold atom_holds, predicate_holds.
      exists height. rewrite eval_old_terms.
      * exact Hrank.
      * simpl in Hbelow. apply Bool.andb_true_iff in Hbelow as [Hargs _].
        exact Hargs.
    + apply (proj2 (product_holds_app _ _ _ _)). split.
      * apply equation_product_holds_any.
        -- now rewrite length_map.
        -- rewrite eval_old_terms.
           ++ rewrite eval_shift_terms. now symmetry.
           ++ simpl in Hbelow. now apply Bool.andb_true_iff in Hbelow as [Hargs _].
      * assert (Hcontextbelow : product_belowb offset context = true).
        { simpl in Hbelow. now apply Bool.andb_true_iff in Hbelow as [_ Hc]. }
        apply (proj2 (product_holds_old offset i old clause_env context
          Hcontextbelow)). exact Hcontext.
Qed.

Lemma left_unfold_right_transfer i old clause_env offset rhs :
  formula_freeb rhs = true ->
  formula_belowb offset rhs = true ->
  right_holds i (combine_valuation offset old clause_env) rhs ->
  right_holds i old rhs.
Proof.
  intros Hfree Hbelow Hright.
  apply (proj1 (right_holds_free i _ rhs Hfree)) in Hright.
  apply (proj1 (formula_holds_old offset i old clause_env rhs Hbelow)) in Hright.
  apply (proj2 (right_holds_free i old rhs Hfree)). exact Hright.
Qed.

Lemma left_unfold_respects
    ds i old clause_env offset tag fresh name args context rhs c height :
  tag <> fresh ->
  product_belowb offset (Pred (Some tag) name args :: context) = true ->
  i.(predicate_rank) name (eval_terms old args) = Some height ->
  body_decreases i clause_env c.(clause_body) height ->
  Cyclic.respects_edge
    (mk_judgment ds
      (mk_sequent [Pred (Some tag) name args :: context] rhs))
    (left_unfold_judgment ds offset tag fresh name args context rhs c)
    (i, old) (i, combine_valuation offset old clause_env)
    (left_unfold_edge tag fresh (product_has_pred c.(clause_body))).
Proof.
  intros Hneq Hbelow Hrank Hdec.
  assert (Hargsbelow : forallb (term_belowb offset) args = true).
  { simpl in Hbelow. now apply Bool.andb_true_iff in Hbelow as [Hargs _]. }
  unfold Cyclic.respects_edge, left_unfold_edge.
  destruct (product_has_pred (clause_body c)) eqn:Hrecursive; split; simpl.
  - intros a b [Hab | [Hab | Hfalse]].
    + inversion Hab; subst a b.
      assert (Hrank_combined :
        predicate_rank i name
          (eval_terms (combine_valuation offset old clause_env) args) =
        Some height).
      { rewrite eval_old_terms by exact Hargsbelow. exact Hrank. }
      pose proof (rank_unfold_contraction i
        (combine_valuation offset old clause_env) tag fresh
        (shift_product offset (clause_body c)) name args
        (equation_product args (map (shift_term offset) (clause_head c)) ++ context)%list
        height Hneq Hrank_combined) as Hfresh.
      change
        ((match rank_product i (combine_valuation offset old clause_env) fresh
           (left_unfold_product offset tag fresh name args context c) with
          | Some n => n | None => 0 end) <=
         (match rank_product i old tag (Pred (Some tag) name args :: context) with
          | Some n => n | None => 0 end)).
      unfold left_unfold_product. rewrite Hfresh. simpl.
      rewrite Nat.eqb_refl, Hrank. lia.
    + inversion Hab; subst a b.
      destruct (rank_shift_retag_body_progress i old clause_env offset
        c.(clause_body) tag height Hdec Hrecursive)
        as [child [Hchild Hlt]].
      pose proof (rank_product_app_some i
        (combine_valuation offset old clause_env) tag
        (retag_product tag (shift_product offset (clause_body c)))
        (Pred (Some fresh) name args ::
          equation_product args (map (shift_term offset) (clause_head c)) ++ context)%list
        (S child) Hchild) as Htarget.
      unfold FirstOrderTheory.rank, rank_of_tag, left_unfold_judgment,
        mk_judgment, mk_sequent.
      simpl.
      unfold left_unfold_product. rewrite Htarget. simpl.
      rewrite Nat.eqb_refl, Hrank. lia.
    + contradiction.
  - intros a b [Hab | Hfalse].
    + inversion Hab; subst a b.
      destruct (rank_shift_retag_body_progress i old clause_env offset
        c.(clause_body) tag height Hdec Hrecursive)
        as [child [Hchild Hlt]].
      pose proof (rank_product_app_some i
        (combine_valuation offset old clause_env) tag
        (retag_product tag (shift_product offset (clause_body c)))
        (Pred (Some fresh) name args ::
          equation_product args (map (shift_term offset) (clause_head c)) ++ context)%list
        (S child) Hchild) as Htarget.
      unfold FirstOrderTheory.rank, rank_of_tag, left_unfold_judgment,
        mk_judgment, mk_sequent.
      simpl.
      unfold left_unfold_product. rewrite Htarget. simpl.
      rewrite Nat.eqb_refl, Hrank. lia.
    + contradiction.
  - intros a b [Hab | Hfalse].
    + inversion Hab; subst a b.
      assert (Hrank_combined :
        predicate_rank i name
          (eval_terms (combine_valuation offset old clause_env) args) =
        Some height).
      { rewrite eval_old_terms by exact Hargsbelow. exact Hrank. }
      pose proof (rank_unfold_contraction i
        (combine_valuation offset old clause_env) tag fresh
        (shift_product offset (clause_body c)) name args
        (equation_product args (map (shift_term offset) (clause_head c)) ++ context)%list
        height Hneq Hrank_combined) as Hfresh.
      change
        ((match rank_product i (combine_valuation offset old clause_env) fresh
           (left_unfold_product offset tag fresh name args context c) with
          | Some n => n | None => 0 end) <=
         (match rank_product i old tag (Pred (Some tag) name args :: context) with
          | Some n => n | None => 0 end)).
      unfold left_unfold_product. rewrite Hfresh. simpl.
      rewrite Nat.eqb_refl, Hrank. lia.
    + contradiction.
  - intros a b Hfalse. contradiction.
Qed.

(** Invert one tagged predicate on the left.  All definition clauses become
    premises.  Clause variables are shifted above [offset], and [fresh]
    keeps the contracted copy of the unfolded predicate traceable. *)
Definition left_unfold_rule
    (ds : definitions) (offset tag fresh : nat)
    (name : string) (args : list term) (context : product) (rhs : formula)
    (Htag : tag <> fresh)
    (Hbelow : product_belowb offset
      (Pred (Some tag) name args :: context) = true)
    (Hrhsfree : formula_freeb rhs = true)
    (Hrhsbelow : formula_belowb offset rhs = true)
  : Cyclic.rule_instance.
Proof.
  set (clauses := lookup_definition name ds).
  set (source := mk_judgment ds
    (mk_sequent [Pred (Some tag) name args :: context] rhs)).
  set (premises := left_unfold_premises ds offset tag fresh name args
    context rhs clauses).
  refine
    {| Cyclic.rule_name := "L.Unfold";
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := premises |}.
  - intros Hvalid [i old]. unfold source, denote, sequent_holds; simpl.
    intros Hmodel Hlhs.
    apply formula_holds_singleton_inv in Hlhs.
    simpl in Hlhs. destruct Hlhs as [Hpred Hcontext].
    destruct (choose_predicate_height i name (eval_terms old args) Hpred)
      as [height Hrank].
    destruct (choose_model_case ds i name (eval_terms old args) height
      Hmodel Hrank) as [[c clause_env]
        [Hin [Hhead [Hbody Hdecreases]]]].
    destruct (choose_clause_index c clauses) as [index Hindex].
    { unfold clauses. exact Hin. }
    set (p := left_unfold_premise ds offset tag fresh name args context rhs c).
    assert (Hnth : nth_error premises index = Some p).
    {
      unfold premises, left_unfold_premises, p.
      rewrite nth_error_map, Hindex. reflexivity.
    }
    pose proof (Hvalid p (nth_error_In _ _ Hnth)
      (i, combine_valuation offset old clause_env)) as Htarget.
    unfold p, left_unfold_premise, denote, sequent_holds in Htarget;
      simpl in Htarget.
    apply left_unfold_right_transfer with (clause_env := clause_env)
      (offset := offset); [exact Hrhsfree|exact Hrhsbelow|].
    apply Htarget; [exact Hmodel|].
    apply formula_holds_cons_intro.
    apply left_unfold_lhs_holds with (height := height); try assumption.
    unfold eval_terms in Hhead.
    apply (f_equal (@List.length value)) in Hhead.
    now rewrite !length_map in Hhead.
  - intros [i old] Hfalse.
    assert (Hsource : ~ denote
      (mk_judgment ds
        (mk_sequent [Pred (Some tag) name args :: context] rhs)) (i, old)).
    { now unfold source in Hfalse. }
    destruct (false_world_parts ds
      (mk_sequent [Pred (Some tag) name args :: context] rhs) i old Hsource)
      as [Hmodel [Hlhs Hright]].
    apply formula_holds_singleton_inv in Hlhs.
    simpl in Hlhs. destruct Hlhs as [Hpred Hcontext].
    destruct (choose_predicate_height i name (eval_terms old args) Hpred)
      as [height Hrank].
    destruct (choose_model_case ds i name (eval_terms old args) height
      Hmodel Hrank) as [[c clause_env]
        [Hin [Hhead [Hbody Hdecreases]]]].
    destruct (choose_clause_index c clauses) as [index Hindex].
    { unfold clauses. exact Hin. }
    set (p := left_unfold_premise ds offset tag fresh name args context rhs c).
    assert (Hnth : nth_error premises index = Some p).
    {
      unfold premises, left_unfold_premises, p.
      rewrite nth_error_map, Hindex. reflexivity.
    }
    exists index, p, (i, combine_valuation offset old clause_env).
    split; [exact Hnth|]. split.
    + unfold p, left_unfold_premise.
      apply make_false_world; [exact Hmodel| |].
      * apply formula_holds_cons_intro.
        apply left_unfold_lhs_holds with (height := height); try assumption.
        unfold eval_terms in Hhead.
        apply (f_equal (@List.length value)) in Hhead.
        now rewrite !length_map in Hhead.
      * intro Htarget_right. apply Hright.
        apply left_unfold_right_transfer with (clause_env := clause_env)
          (offset := offset); assumption.
    + unfold p, left_unfold_premise.
      apply left_unfold_respects with (height := height); assumption.
Defined.
