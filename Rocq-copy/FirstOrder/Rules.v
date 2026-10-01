From Stdlib Require Import List Bool Arith Lia String Classical_Prop.
From Stdlib Require Import Logic.ClassicalEpsilon Logic.ClassicalDescription.
From Stdlib Require Import Logic.FunctionalExtensionality.

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

(** A matched right unfolding is the verified counterpart of
    [uni_ruf_pred_in_prod] in the OCaml implementation.  Instead of adding
    head equations and simplifying them later, a checked directional match is
    applied directly to the clause body. *)
Definition substitution_valuation (rho : valuation) (s : substitution)
    : valuation :=
  fun x => eval_term rho (subst_term s (Var x)).

Lemma eval_term_substitution_valuation rho s t :
  eval_term rho (subst_term s t) = eval_term (substitution_valuation rho s) t.
Proof.
  induction t using term_nested_ind; simpl; auto.
  f_equal. rewrite map_map. apply map_ext_in.
  intros u Hu. apply (proj1 (Forall_forall _ args) H u Hu).
Qed.

Lemma eval_terms_substitution_valuation rho s terms :
  eval_terms rho (map (subst_term s) terms) =
  eval_terms (substitution_valuation rho s) terms.
Proof.
  unfold eval_terms. rewrite map_map. apply map_ext_in.
  intros t Ht. apply eval_term_substitution_valuation.
Qed.

Lemma atom_holds_substitution_valuation i rho s a :
  atom_holds i rho (subst_atom s a) <->
  atom_holds i (substitution_valuation rho s) a.
Proof.
  destruct a as [x y|x y|tag name args]; simpl.
  - now rewrite !eval_term_substitution_valuation.
  - now rewrite !eval_term_substitution_valuation.
  - now rewrite eval_terms_substitution_valuation.
Qed.

Lemma product_holds_substitution_valuation i rho s p :
  product_holds i rho (subst_product s p) <->
  product_holds i (substitution_valuation rho s) p.
Proof.
  induction p as [|a p IH]; simpl; [tauto|].
  rewrite atom_holds_substitution_valuation, IH. tauto.
Qed.

Lemma formula_holds_substitution_valuation i rho s f :
  formula_holds i rho (subst_formula s f) <->
  formula_holds i (substitution_valuation rho s) f.
Proof.
  unfold formula_holds, subst_formula. split; intros [p [Hin Hp]].
  - apply in_map_iff in Hin. destruct Hin as [original [<- Hin]].
    exists original. split; [exact Hin|].
    now apply (proj1 (product_holds_substitution_valuation i rho s original)).
  - exists (subst_product s p). split; [now apply in_map|].
    now apply (proj2 (product_holds_substitution_valuation i rho s p)).
Qed.

Lemma rank_atom_substitution_valuation i rho trace s a :
  rank_atom i rho trace (subst_atom s a) =
  rank_atom i (substitution_valuation rho s) trace a.
Proof.
  destruct a as [x y|x y|tag name args]; simpl; auto.
  now rewrite eval_terms_substitution_valuation.
Qed.

Lemma rank_product_substitution_valuation i rho trace s p :
  rank_product i rho trace (subst_product s p) =
  rank_product i (substitution_valuation rho s) trace p.
Proof.
  induction p as [|a p IH]; simpl; auto.
  rewrite rank_atom_substitution_valuation.
  destruct (rank_atom i (substitution_valuation rho s) trace a); auto.
Qed.

Lemma rank_formula_substitution_valuation i rho trace s f :
  rank_formula i rho trace (subst_formula s f) =
  rank_formula i (substitution_valuation rho s) trace f.
Proof.
  induction f as [|p f IH]; simpl; auto.
  rewrite rank_product_substitution_valuation.
  destruct (rank_product i (substitution_valuation rho s) trace p); auto.
Qed.

Definition matched_right_unfold_product
    (s : substitution) (context : product) (c : clause) : product :=
  (subst_product s c.(clause_body) ++ context)%list.

Definition matched_right_unfold_judgment
    (ds : definitions) (lhs : formula) (s : substitution)
    (context : product) (alternatives : formula) (c : clause) : judgment :=
  mk_judgment ds
    (mk_sequent lhs (matched_right_unfold_product s context c :: alternatives)).

Lemma matched_right_unfold_transfer
    ds i base tag name args context alternatives c s :
  models ds i ->
  In c (lookup_definition name ds) ->
  map (subst_term s) c.(clause_head) = args ->
  right_holds i base
    (matched_right_unfold_product s context c :: alternatives) ->
  right_holds i base ((Pred tag name args :: context) :: alternatives).
Proof.
  intros Hmodel Hin Hmatch [witness [p [[Hp | Hp] HpHolds]]].
  - subst p. exists witness.
    exists (Pred tag name args :: context). split; [now left|]. simpl.
    apply (proj1 (product_holds_app _ _ _ _)) in HpHolds
      as [Hbody Hcontext].
    split; [|exact Hcontext].
    destruct Hmodel as [Hintro _].
    pose proof (Hintro name c
      (substitution_valuation (merge_valuation base witness) s) Hin
      (proj1 (product_holds_substitution_valuation i
        (merge_valuation base witness) s c.(clause_body)) Hbody)) as Hpred.
    unfold predicate_holds in Hpred |- *.
    rewrite <- Hmatch.
    now rewrite eval_terms_substitution_valuation.
  - exists witness, p. split; [right; exact Hp|exact HpHolds].
Qed.

Definition matched_right_unfold_rule
    (ds : definitions) (lhs : formula) (tag : option nat)
    (name : string) (args : list term) (context : product)
    (alternatives : formula) (c : clause) (s : substitution)
    (Hin : In c (lookup_definition name ds))
    (Hmatch : map (subst_term s) c.(clause_head) = args)
    : Cyclic.rule_instance.
Proof.
  set (source := mk_judgment ds
    (mk_sequent lhs ((Pred tag name args :: context) :: alternatives))).
  set (target := matched_right_unfold_judgment ds lhs s context alternatives c).
  set (p := {| Cyclic.premise_judgment := target;
               Cyclic.premise_edge := identity_edge source |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "R.Unfold/match";
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := [p] |}.
  - intros Hvalid [i base]. unfold source, denote, sequent_holds; simpl.
    intros Hmodel Hlhs.
    pose proof (Hvalid p ltac:(now left) (i, base)) as Htarget.
    unfold p, target, matched_right_unfold_judgment, denote, sequent_holds
      in Htarget; simpl in Htarget.
    apply matched_right_unfold_transfer with (ds := ds)
      (c := c) (s := s); try assumption.
    now apply Htarget.
  - intros [i base] Hfalse.
    exists 0, p, (i, base). split; [reflexivity|]. split.
    + unfold p, target, matched_right_unfold_judgment.
      intro Htarget. apply Hfalse.
      unfold source, denote, sequent_holds in *; simpl in *.
      intros Hmodel Hlhs.
      eapply matched_right_unfold_transfer; eauto.
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

(** The list position of a right-hand product has no logical significance.
    This variant is convenient for executable search because it closes a goal
    using any right product found by [existsb], without first permuting the
    reified formula. *)
Definition identity_axiom_anywhere
    (ds : definitions) (big : product) (rhs : formula) (small : product)
    (Hin : In small rhs)
    (Hsubset : forall a, In a small -> In a big)
    (Hfree : product_freeb small = true) : Cyclic.axiom_instance.
Proof.
  refine
    {| Cyclic.axiom_name := "Id";
       Cyclic.axiom_conclusion := mk_judgment ds (mk_sequent [big] rhs) |}.
  intros [i rho]. unfold denote, sequent_holds; simpl.
  intros _ Hlhs. apply formula_holds_singleton_inv in Hlhs.
  exists rho, small. split; [exact Hin|].
  apply (proj2 (product_holds_merge_free i rho rho small Hfree)).
  eapply product_holds_subset; eauto.
Defined.

Definition identity_axiom_anywhere_from_check
    (ds : definitions) (big : product) (rhs : formula) (small : product)
    (Hin : In small rhs)
    (Hsubset : product_subsetb small big = true)
    (Hfree : product_freeb small = true) : Cyclic.axiom_instance :=
  identity_axiom_anywhere ds big rhs small Hin
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

(** Constructor terms in the semantic domain are disjoint.  The OCaml
    ex-falso test checks the common special cases [0 = s(_)] and
    [0 = cons(_,_)]; the free constructor model validates the slightly more
    general constant-versus-function clash below. *)
Definition constructor_clash_axiom_left
    (ds : definitions) (p : product) (rhs : formula)
    (n : nat) (name : string) (args : list term)
    (Hin : In (Eq (Const n) (Fun name args)) p) : Cyclic.axiom_instance.
Proof.
  refine
    {| Cyclic.axiom_name := "Ex Falso";
       Cyclic.axiom_conclusion := mk_judgment ds (mk_sequent [p] rhs) |}.
  intros [i rho]. unfold denote, sequent_holds; simpl.
  intros _ Hlhs. exfalso. apply formula_holds_singleton_inv in Hlhs.
  pose proof (product_holds_atom i rho p
    (Eq (Const n) (Fun name args)) Hlhs Hin) as Hclash.
  simpl in Hclash. discriminate.
Defined.

Definition constructor_clash_axiom_right
    (ds : definitions) (p : product) (rhs : formula)
    (n : nat) (name : string) (args : list term)
    (Hin : In (Eq (Fun name args) (Const n)) p) : Cyclic.axiom_instance.
Proof.
  refine
    {| Cyclic.axiom_name := "Ex Falso";
       Cyclic.axiom_conclusion := mk_judgment ds (mk_sequent [p] rhs) |}.
  intros [i rho]. unfold denote, sequent_holds; simpl.
  intros _ Hlhs. exfalso. apply formula_holds_singleton_inv in Hlhs.
  pose proof (product_holds_atom i rho p
    (Eq (Fun name args) (Const n)) Hlhs Hin) as Hclash.
  simpl in Hclash. discriminate.
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

(** An exact repeated judgment is the simplest backlink candidate.  The edge
    carries every antecedent trace tag unchanged.  More permissive backlink
    discovery may insert explicit weakening/substitution nodes first, just as
    the OCaml prover does, but the final backlink itself is always exact. *)
Lemma identity_edge_respects_refl j w :
  Cyclic.respects_edge j j w w (identity_edge j).
Proof.
  destruct j as [ds [lhs rhs]].
  exact (identity_edge_respects_same_lhs ds lhs rhs rhs w).
Qed.

Definition exact_backlink_rule (j : judgment) : Cyclic.rule_instance :=
  backlink_rule j j (identity_edge j)
    (fun _ => conj (fun H => H) (fun H => H))
    (fun w _ => identity_edge_respects_refl j w).

(** ** Equality simplification

    The executable OCaml prover repeatedly removes reflexive equalities.  The
    following rule proves that transformation once for an equality occurring
    at any position in a singleton antecedent product. *)

Lemma product_holds_remove_refl i rho before t after :
  product_holds i rho (before ++ Eq t t :: after)%list <->
  product_holds i rho (before ++ after)%list.
Proof.
  rewrite !product_holds_app. simpl. tauto.
Qed.

Lemma rank_product_remove_refl i rho tag before t after :
  rank_product i rho tag (before ++ Eq t t :: after)%list =
  rank_product i rho tag (before ++ after)%list.
Proof.
  induction before as [|a before IH]; simpl; [reflexivity|].
  destruct (rank_atom i rho tag a); [reflexivity|exact IH].
Qed.

Definition reflexive_equality_source
    (ds : definitions) (before : product) (t : term) (after : product)
    (rhs : formula) : judgment :=
  mk_judgment ds (mk_sequent [(before ++ Eq t t :: after)%list] rhs).

Definition reflexive_equality_target
    (ds : definitions) (before after : product) (rhs : formula) : judgment :=
  mk_judgment ds (mk_sequent [(before ++ after)%list] rhs).

Lemma reflexive_equality_semantics ds before t after rhs w :
  denote (reflexive_equality_source ds before t after rhs) w <->
  denote (reflexive_equality_target ds before after rhs) w.
Proof.
  destruct w as [i rho].
  unfold denote, reflexive_equality_source, reflexive_equality_target,
    sequent_holds, mk_judgment, mk_sequent; simpl.
  split.
  - intros H Hmodel Hlhs. apply H; [exact Hmodel|].
    apply formula_holds_singleton_inv in Hlhs.
    apply formula_holds_cons_intro.
    now apply (proj2 (product_holds_remove_refl i rho before t after)).
  - intros H Hmodel Hlhs. apply H; [exact Hmodel|].
    apply formula_holds_singleton_inv in Hlhs.
    apply formula_holds_cons_intro.
    now apply (proj1 (product_holds_remove_refl i rho before t after)).
Qed.

Lemma reflexive_equality_rank ds before t after rhs w tag :
  FirstOrderTheory.rank (reflexive_equality_target ds before after rhs) w tag =
  FirstOrderTheory.rank (reflexive_equality_source ds before t after rhs) w tag.
Proof.
  destruct w as [i rho].
  unfold FirstOrderTheory.rank, rank_of_tag, reflexive_equality_source,
    reflexive_equality_target, mk_judgment, mk_sequent. simpl.
  now rewrite rank_product_remove_refl.
Qed.

Lemma identity_edge_respects_rank_equivalence source target w
    (Hrank : forall tag,
      FirstOrderTheory.rank target w tag = FirstOrderTheory.rank source w tag) :
  Cyclic.respects_edge source target w w (identity_edge source).
Proof.
  split.
  - intros a b Hin. apply in_identity_pairs_eq in Hin. subst b.
    rewrite Hrank. apply Nat.le_refl.
  - intros a b Hin. inversion Hin.
Qed.

(** A reusable unary equivalence rule.  Its countermodel theorem transports a
    false world unchanged, while [Hrespect] explains how trace ranks behave. *)
Definition equivalence_rule
    (name : string) (source target : judgment) (edge : Cyclic.edge_info)
    (Hsemantic : forall w, denote source w <-> denote target w)
    (Hrespect : forall w, Cyclic.respects_edge source target w w edge)
    : Cyclic.rule_instance.
Proof.
  set (p := {| Cyclic.premise_judgment := target;
               Cyclic.premise_edge := edge |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := name;
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := [p] |}.
  - intros Hvalid w. apply (proj2 (Hsemantic w)).
    apply Hvalid with (p := p). now left.
  - intros w Hfalse. exists 0, p, w. split; [reflexivity|]. split.
    + intro Htarget. apply Hfalse. now apply (proj2 (Hsemantic w)).
    + apply Hrespect.
Defined.

(** Reuse a verified rule after replacing its conclusion by a semantically
    equivalent judgment with exactly the same trace ranks.  This is useful
    for set-like syntax: the OCaml prover can select an atom from anywhere in
    a product, while our executable lists must first put that atom in the
    position expected by a small rule kernel.

    The premises and their edge annotations are left untouched.  The rank
    equality is precisely what justifies viewing those edges as starting at
    the reordered conclusion. *)
Definition transport_rule_conclusion
    (name : string) (source : judgment) (r : Cyclic.rule_instance)
    (Hsemantic : forall w,
      denote source w <-> denote r.(Cyclic.rule_conclusion) w)
    (Hrank : forall w tag,
      FirstOrderTheory.rank r.(Cyclic.rule_conclusion) w tag =
      FirstOrderTheory.rank source w tag)
    : Cyclic.rule_instance.
Proof.
  refine
    {| Cyclic.rule_name := name;
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := r.(Cyclic.rule_premises) |}.
  - intros Hvalid w. apply (proj2 (Hsemantic w)).
    exact (r.(Cyclic.rule_theorem) Hvalid w).
  - intros w Hfalse.
    assert (Hfalse_r : ~ denote r.(Cyclic.rule_conclusion) w).
    { intro Hr. apply Hfalse. now apply (proj2 (Hsemantic w)). }
    destruct (r.(Cyclic.rule_counter_step) w Hfalse_r)
      as [k [p [w' [Hnth [Hpfalse Hrespect]]]]].
    exists k, p, w'. split; [exact Hnth|]. split; [exact Hpfalse|].
    destruct Hrespect as [Hvalid_edge Hprogress_edge]. split.
    + intros a b Hin. specialize (Hvalid_edge a b Hin).
      rewrite <- (Hrank w a). exact Hvalid_edge.
    + intros a b Hin. specialize (Hprogress_edge a b Hin).
      rewrite <- (Hrank w a). exact Hprogress_edge.
Defined.

(** Conjunction products and disjunction formulae are represented by lists,
    but their semantics is insensitive to list rotation.  These compact
    lemmas are used below to expose a selected succedent predicate at the
    head, where the basic unfolding rule expects it. *)
Lemma product_holds_rotate i rho before a after :
  product_holds i rho (before ++ a :: after)%list <->
  product_holds i rho (a :: before ++ after)%list.
Proof.
  rewrite (product_holds_app i rho before (a :: after)). simpl.
  rewrite (product_holds_app i rho before after). tauto.
Qed.

Lemma formula_holds_app i rho (left right : formula) :
  formula_holds i rho (left ++ right)%list <->
  formula_holds i rho left \/ formula_holds i rho right.
Proof.
  unfold formula_holds. split.
  - intros [p [Hin Hp]]. apply in_app_iff in Hin as [Hin|Hin].
    + left. now exists p.
    + right. now exists p.
  - intros [[p [Hin Hp]] | [p [Hin Hp]]].
    + exists p. split; [apply in_app_iff; now left|exact Hp].
    + exists p. split; [apply in_app_iff; now right|exact Hp].
Qed.

Lemma formula_holds_cons i rho p rest :
  formula_holds i rho (p :: rest) <->
  product_holds i rho p \/ formula_holds i rho rest.
Proof.
  unfold formula_holds. split.
  - intros [q [Hin Hq]]. destruct Hin as [Heq|Hin].
    + subst q. left. exact Hq.
    + right. exists q. split; assumption.
  - intros [Hp | [q [Hin Hq]]].
    + exists p. split; [now left|exact Hp].
    + exists q. split; [now right|exact Hq].
Qed.

(** Replacing one disjunct by a semantically equivalent product preserves the
    whole disjunction, even when that product occurs in the middle of the
    executable list representation. *)
Lemma formula_holds_replace_product i rho before old_product new_product after
    (Hproduct : product_holds i rho old_product <->
                product_holds i rho new_product) :
  formula_holds i rho (before ++ old_product :: after)%list <->
  formula_holds i rho (before ++ new_product :: after)%list.
Proof.
  rewrite !formula_holds_app, !formula_holds_cons, Hproduct. tauto.
Qed.

Lemma formula_holds_rotate_product i rho
    before_products before_atoms a after_atoms after_products :
  formula_holds i rho
    (before_products ++
      (before_atoms ++ a :: after_atoms)%list :: after_products)%list <->
  formula_holds i rho
    ((a :: before_atoms ++ after_atoms)%list ::
      before_products ++ after_products)%list.
Proof.
  rewrite formula_holds_app, !formula_holds_cons,
    formula_holds_app, product_holds_rotate.
  tauto.
Qed.

Lemma right_holds_rotate_product i base
    before_products before_atoms a after_atoms after_products :
  right_holds i base
    (before_products ++
      (before_atoms ++ a :: after_atoms)%list :: after_products)%list <->
  right_holds i base
    ((a :: before_atoms ++ after_atoms)%list ::
      before_products ++ after_products)%list.
Proof.
  unfold right_holds. split; intros [witness H]; exists witness.
  - now apply (proj1 (formula_holds_rotate_product i _ _ _ _ _ _)).
  - now apply (proj2 (formula_holds_rotate_product i _ _ _ _ _ _)).
Qed.

(** ** Right unfolding at an arbitrary formula/product position

    [matched_right_unfold_rule] is intentionally small: it unfolds the first
    atom of the first succedent product.  The original OCaml generator,
    however, visits every inductive predicate in every product.  The wrapper
    below rotates a selected occurrence to that canonical position, applies
    the small verified rule, and transports the result back to the original
    list presentation. *)

Definition right_unfold_at_source
    (ds : definitions) (lhs : formula)
    (before_products : formula) (before_atoms : product)
    (tag : option nat) (name : string) (args : list term)
    (after_atoms : product) (after_products : formula) : judgment :=
  mk_judgment ds
    (mk_sequent lhs
      (before_products ++
        (before_atoms ++ Pred tag name args :: after_atoms)%list ::
        after_products)%list).

Definition right_unfold_at_rotated
    (ds : definitions) (lhs : formula)
    (before_products : formula) (before_atoms : product)
    (tag : option nat) (name : string) (args : list term)
    (after_atoms : product) (after_products : formula) : judgment :=
  mk_judgment ds
    (mk_sequent lhs
      ((Pred tag name args :: before_atoms ++ after_atoms)%list ::
        before_products ++ after_products)%list).

Lemma right_unfold_at_semantics ds lhs before_products before_atoms
    tag name args after_atoms after_products w :
  denote (right_unfold_at_source ds lhs before_products before_atoms
    tag name args after_atoms after_products) w <->
  denote (right_unfold_at_rotated ds lhs before_products before_atoms
    tag name args after_atoms after_products) w.
Proof.
  destruct w as [i base]. unfold right_unfold_at_source,
    right_unfold_at_rotated, denote, sequent_holds, mk_judgment, mk_sequent;
    simpl.
  split; intros H Hmodel Hlhs.
  - apply (proj1 (right_holds_rotate_product i base
      before_products before_atoms (Pred tag name args) after_atoms
      after_products)). now apply H.
  - apply (proj2 (right_holds_rotate_product i base
      before_products before_atoms (Pred tag name args) after_atoms
      after_products)). now apply H.
Qed.

Lemma right_unfold_at_rank ds lhs before_products before_atoms
    tag name args after_atoms after_products w trace :
  FirstOrderTheory.rank
    (right_unfold_at_rotated ds lhs before_products before_atoms
      tag name args after_atoms after_products) w trace =
  FirstOrderTheory.rank
    (right_unfold_at_source ds lhs before_products before_atoms
      tag name args after_atoms after_products) w trace.
Proof. reflexivity. Qed.

Definition matched_right_unfold_at_rule
    (ds : definitions) (lhs : formula)
    (before_products : formula) (before_atoms : product)
    (tag : option nat) (name : string) (args : list term)
    (after_atoms : product) (after_products : formula)
    (c : clause) (s : substitution)
    (Hin : In c (lookup_definition name ds))
    (Hmatch : map (subst_term s) c.(clause_head) = args)
    : Cyclic.rule_instance :=
  let rotated_context := (before_atoms ++ after_atoms)%list in
  let rotated_alternatives := (before_products ++ after_products)%list in
  let basic := matched_right_unfold_rule ds lhs tag name args
    rotated_context rotated_alternatives c s Hin Hmatch in
  transport_rule_conclusion "R.Unfold/match"
    (right_unfold_at_source ds lhs before_products before_atoms
      tag name args after_atoms after_products)
    basic
    (right_unfold_at_semantics ds lhs before_products before_atoms
      tag name args after_atoms after_products)
    (right_unfold_at_rank ds lhs before_products before_atoms
      tag name args after_atoms after_products).

(** Equation-producing fallback for the same arbitrary position.  This is the
    verified form of [std_ruf_pred_in_prod] from the OCaml prover: clause
    variables are shifted to fresh existential variables and head agreement
    is recorded explicitly as equality atoms. *)
Definition standard_right_unfold_at_rule
    (ds : definitions) (offset : nat) (lhs : formula)
    (before_products : formula) (before_atoms : product)
    (tag : option nat) (name : string) (args : list term)
    (after_atoms : product) (after_products : formula)
    (c : clause)
    (Hin : In c (lookup_definition name ds))
    (Harity : List.length args = List.length c.(clause_head))
    : Cyclic.rule_instance :=
  let rotated_context := (before_atoms ++ after_atoms)%list in
  let rotated_alternatives := (before_products ++ after_products)%list in
  let basic := right_unfold_rule ds offset lhs tag name args
    rotated_context rotated_alternatives c Hin Harity in
  transport_rule_conclusion "R.Unfold"
    (right_unfold_at_source ds lhs before_products before_atoms
      tag name args after_atoms after_products)
    basic
    (right_unfold_at_semantics ds lhs before_products before_atoms
      tag name args after_atoms after_products)
    (right_unfold_at_rank ds lhs before_products before_atoms
      tag name args after_atoms after_products).

Definition reflexive_equality_rule
    (ds : definitions) (before : product) (t : term) (after : product)
    (rhs : formula) : Cyclic.rule_instance :=
  let source := reflexive_equality_source ds before t after rhs in
  let target := reflexive_equality_target ds before after rhs in
  equivalence_rule "Simpl =" source target (identity_edge source)
    (reflexive_equality_semantics ds before t after rhs)
    (fun w => identity_edge_respects_rank_equivalence source target w
      (reflexive_equality_rank ds before t after rhs w)).

(** The OCaml [simplify_eqs] pass removes reflexive equalities on both sides
    of the sequent.  The preceding rule handles the antecedent; this rule
    handles one occurrence in an arbitrary succedent product. *)

Definition right_reflexive_equality_source
    (ds : definitions) (lhs before_products : formula)
    (before_atoms : product) (t : term) (after_atoms : product)
    (after_products : formula) : judgment :=
  mk_judgment ds
    (mk_sequent lhs
      (before_products ++
        (before_atoms ++ Eq t t :: after_atoms)%list :: after_products)%list).

Definition right_reflexive_equality_target
    (ds : definitions) (lhs before_products : formula)
    (before_atoms after_atoms : product) (after_products : formula) : judgment :=
  mk_judgment ds
    (mk_sequent lhs
      (before_products ++
        (before_atoms ++ after_atoms)%list :: after_products)%list).

Lemma product_holds_remove_right_refl i rho before t after :
  product_holds i rho (before ++ Eq t t :: after)%list <->
  product_holds i rho (before ++ after)%list.
Proof.
  rewrite (product_holds_app i rho before (Eq t t :: after)). simpl.
  rewrite (product_holds_app i rho before after). tauto.
Qed.

Lemma right_reflexive_equality_right_holds i base before_products before_atoms
    t after_atoms after_products :
  right_holds i base
    (before_products ++
      (before_atoms ++ Eq t t :: after_atoms)%list :: after_products)%list <->
  right_holds i base
    (before_products ++
      (before_atoms ++ after_atoms)%list :: after_products)%list.
Proof.
  unfold right_holds. split; intros [witness H]; exists witness.
  - apply (proj1 (formula_holds_replace_product i _ before_products
      (before_atoms ++ Eq t t :: after_atoms)%list
      (before_atoms ++ after_atoms)%list after_products
      (product_holds_remove_right_refl i _ before_atoms t after_atoms))).
    exact H.
  - apply (proj2 (formula_holds_replace_product i _ before_products
      (before_atoms ++ Eq t t :: after_atoms)%list
      (before_atoms ++ after_atoms)%list after_products
      (product_holds_remove_right_refl i _ before_atoms t after_atoms))).
    exact H.
Qed.

Lemma right_reflexive_equality_semantics ds lhs before_products before_atoms
    t after_atoms after_products w :
  denote (right_reflexive_equality_source ds lhs before_products before_atoms
    t after_atoms after_products) w <->
  denote (right_reflexive_equality_target ds lhs before_products before_atoms
    after_atoms after_products) w.
Proof.
  destruct w as [i base]. unfold right_reflexive_equality_source,
    right_reflexive_equality_target, denote, sequent_holds, mk_judgment,
    mk_sequent; simpl.
  split; intros H Hmodel Hlhs.
  - apply (proj1 (right_reflexive_equality_right_holds i base
      before_products before_atoms t after_atoms after_products)).
    now apply H.
  - apply (proj2 (right_reflexive_equality_right_holds i base
      before_products before_atoms t after_atoms after_products)).
    now apply H.
Qed.

Definition right_reflexive_equality_rule
    (ds : definitions) (lhs before_products : formula)
    (before_atoms : product) (t : term) (after_atoms : product)
    (after_products : formula) : Cyclic.rule_instance :=
  let source := right_reflexive_equality_source ds lhs before_products
    before_atoms t after_atoms after_products in
  let target := right_reflexive_equality_target ds lhs before_products
    before_atoms after_atoms after_products in
  equivalence_rule "Simpl =/right" source target (identity_edge source)
    (right_reflexive_equality_semantics ds lhs before_products before_atoms
      t after_atoms after_products)
    (fun w => identity_edge_respects_rank_equivalence source target w
      (fun _ => eq_refl)).

(** ** Elimination of an existential equality on the right

    A succedent is existentially quantified by [right_holds].  Therefore a
    conjunct [?e = t] can be solved by choosing [?e] to denote [t], provided
    [t] is free (so its value is determined by the base valuation rather than
    by the witness currently being modified). *)

Definition single_existential_substitution (id : nat) (replacement : term)
    : substitution := [(existential_var id, replacement)].

Lemma subst_term_single_existential_self id replacement :
  subst_term (single_existential_substitution id replacement)
    (Var (existential_var id)) = replacement.
Proof.
  unfold single_existential_substitution, existential_var,
    lookup_substitution. simpl.
  unfold variable_eqb, var_kind_eqb. simpl. now rewrite Nat.eqb_refl.
Qed.

Lemma subst_term_single_existential_free id replacement t :
  term_freeb t = true ->
  subst_term (single_existential_substitution id replacement) t = t.
Proof.
  induction t using term_nested_ind; intro Hfree; simpl in *.
  - reflexivity.
  - destruct x as [kind current]. destruct kind; simpl in *;
      [reflexivity|discriminate].
  - f_equal. transitivity (map (fun t => t) args).
    + apply map_ext_in. intros t Hin.
      pose proof (proj1 (Forall_forall _ args) H t Hin) as IHt.
      apply IHt.
      apply (proj1 (forallb_forall term_freeb args) Hfree t Hin).
    + apply map_id.
Qed.

Definition existential_solution_valuation
    (base witness : valuation) (id : nat) (replacement : term) : valuation :=
  substitution_valuation (merge_valuation base witness)
    (single_existential_substitution id replacement).

(** Installing the solved valuation as the new witness changes no free
    variable.  Hence merging it with the original base valuation is a fixed
    point. *)
Lemma merge_existential_solution base witness id replacement :
  merge_valuation base
    (existential_solution_valuation base witness id replacement) =
  existential_solution_valuation base witness id replacement.
Proof.
  apply functional_extensionality. intros [kind current]. destruct kind.
  - unfold existential_solution_valuation, substitution_valuation,
      single_existential_substitution, merge_valuation, existential_var,
      lookup_substitution, variable_eqb, var_kind_eqb; simpl. reflexivity.
  - unfold merge_valuation. simpl. reflexivity.
Qed.

Lemma existential_solution_equation base witness id replacement
    (Hfree : term_freeb replacement = true) :
  existential_solution_valuation base witness id replacement
      (existential_var id) =
  eval_term (existential_solution_valuation base witness id replacement)
      replacement.
Proof.
  unfold existential_solution_valuation.
  change
    (eval_term (merge_valuation base witness)
       (subst_term (single_existential_substitution id replacement)
         (Var (existential_var id))) =
     eval_term
       (substitution_valuation (merge_valuation base witness)
         (single_existential_substitution id replacement)) replacement).
  rewrite <- eval_term_substitution_valuation.
  rewrite subst_term_single_existential_self.
  rewrite subst_term_single_existential_free by exact Hfree.
  reflexivity.
Qed.

Definition right_existential_substitution_source
    (ds : definitions) (lhs : formula) (id : nat) (replacement : term)
    (context : product) (alternatives : formula) : judgment :=
  mk_judgment ds
    (mk_sequent lhs
      ((Eq (Var (existential_var id)) replacement :: context) :: alternatives)).

Definition right_existential_substitution_target
    (ds : definitions) (lhs : formula) (id : nat) (replacement : term)
    (context : product) (alternatives : formula) : judgment :=
  mk_judgment ds
    (mk_sequent lhs
      (subst_product (single_existential_substitution id replacement) context
        :: alternatives)).

Lemma right_existential_substitution_transfer i base id replacement
    context alternatives :
  term_freeb replacement = true ->
  right_holds i base
    (subst_product (single_existential_substitution id replacement) context
      :: alternatives) ->
  right_holds i base
    ((Eq (Var (existential_var id)) replacement :: context) :: alternatives).
Proof.
  intros Hfree [witness [p [[Hp|Hp] Hholds]]].
  - subst p.
    set (solved := existential_solution_valuation base witness id replacement).
    exists solved.
    exists (Eq (Var (existential_var id)) replacement :: context).
    split; [now left|].
    unfold solved. rewrite merge_existential_solution. simpl. split.
    + unfold atom_holds.
      apply existential_solution_equation. exact Hfree.
    + now apply (proj1 (product_holds_substitution_valuation i
        (merge_valuation base witness)
        (single_existential_substitution id replacement) context)).
  - exists witness, p. split; [now right|exact Hholds].
Qed.

Definition right_existential_substitution_rule
    (ds : definitions) (lhs : formula) (id : nat) (replacement : term)
    (context : product) (alternatives : formula)
    (Hfree : term_freeb replacement = true) : Cyclic.rule_instance.
Proof.
  set (source := right_existential_substitution_source ds lhs id replacement
    context alternatives).
  set (target := right_existential_substitution_target ds lhs id replacement
    context alternatives).
  set (p := {| Cyclic.premise_judgment := target;
               Cyclic.premise_edge := identity_edge source |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "Eq existential/right";
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := [p] |}.
  - intros Hvalid [i base]. unfold source, right_existential_substitution_source,
      denote, sequent_holds; simpl.
    intros Hmodel Hlhs.
    pose proof (Hvalid p ltac:(now left) (i, base)) as Htarget.
    unfold p, target, right_existential_substitution_target, denote,
      sequent_holds in Htarget; simpl in Htarget.
    apply right_existential_substitution_transfer; [exact Hfree|].
    now apply Htarget.
  - intros [i base] Hfalse.
    exists 0, p, (i, base). split; [reflexivity|]. split.
    + unfold p, target, right_existential_substitution_target.
      intro Htarget. apply Hfalse.
      unfold source, right_existential_substitution_source, denote,
        sequent_holds in *; simpl in *.
      intros Hmodel Hlhs.
      apply right_existential_substitution_transfer; [exact Hfree|].
      now apply Htarget.
    + unfold p. apply identity_edge_respects_same_lhs.
Defined.

(** Rotate an arbitrary selected existential equation to the canonical
    head/first-product position consumed by the small rule above. *)
Definition right_existential_substitution_at_rule
    (ds : definitions) (lhs before_products : formula)
    (before_atoms : product) (id : nat) (replacement : term)
    (after_atoms : product) (after_products : formula)
    (Hfree : term_freeb replacement = true) : Cyclic.rule_instance :=
  let context := (before_atoms ++ after_atoms)%list in
  let alternatives := (before_products ++ after_products)%list in
  let basic := right_existential_substitution_rule ds lhs id replacement
    context alternatives Hfree in
  transport_rule_conclusion "Eq existential/right"
    (mk_judgment ds
      (mk_sequent lhs
        (before_products ++
          (before_atoms ++ Eq (Var (existential_var id)) replacement ::
            after_atoms)%list :: after_products)%list))
    basic
    (fun w =>
      match w as world_value return
        denote
          (mk_judgment ds
            (mk_sequent lhs
              (before_products ++
                (before_atoms ++ Eq (Var (existential_var id)) replacement ::
                  after_atoms)%list :: after_products)%list)) world_value <->
        denote basic.(Cyclic.rule_conclusion) world_value
      with
      | (i, base) =>
          (* Both sequents have the same antecedent; only the list position of
             the selected succedent atom changes. *)
          conj
            (fun H Hmodel Hlhs =>
              proj1 (right_holds_rotate_product i base before_products
                before_atoms (Eq (Var (existential_var id)) replacement)
                after_atoms after_products) (H Hmodel Hlhs))
            (fun H Hmodel Hlhs =>
              proj2 (right_holds_rotate_product i base before_products
                before_atoms (Eq (Var (existential_var id)) replacement)
                after_atoms after_products) (H Hmodel Hlhs))
      end)
    (fun _ _ => eq_refl).

(** ** Substitution justified by a left-hand equality *)

Lemma eval_term_single_subst_equal rho x replacement u :
  rho x = eval_term rho replacement ->
  eval_term rho (subst_term [(x, replacement)] u) = eval_term rho u.
Proof.
  intro Hvalue. induction u using term_nested_ind; simpl.
  - reflexivity.
  - destruct (variable_eqb x0 x) eqn:Heq.
    + apply variable_eqb_spec in Heq. subst x0. now symmetry.
    + reflexivity.
  - f_equal. rewrite map_map. apply map_ext_in.
    intros u Hu. apply (proj1 (Forall_forall _ args) H u Hu).
Qed.

Lemma eval_terms_single_subst_equal rho x replacement terms :
  rho x = eval_term rho replacement ->
  eval_terms rho (map (subst_term [(x, replacement)]) terms) =
  eval_terms rho terms.
Proof.
  intro Hvalue. unfold eval_terms. rewrite map_map.
  apply map_ext_in. intros u Hu.
  now apply eval_term_single_subst_equal.
Qed.

Lemma atom_holds_single_subst_equal i rho x replacement a :
  rho x = eval_term rho replacement ->
  atom_holds i rho (subst_atom [(x, replacement)] a) <->
  atom_holds i rho a.
Proof.
  intro Hvalue. destruct a as [u v|u v|tag name args]; simpl.
  - now rewrite !eval_term_single_subst_equal by exact Hvalue.
  - now rewrite !eval_term_single_subst_equal by exact Hvalue.
  - now rewrite eval_terms_single_subst_equal by exact Hvalue.
Qed.

Lemma product_holds_single_subst_equal i rho x replacement p :
  rho x = eval_term rho replacement ->
  product_holds i rho (subst_product [(x, replacement)] p) <->
  product_holds i rho p.
Proof.
  intro Hvalue. induction p as [|a p IH]; simpl; [tauto|].
  rewrite atom_holds_single_subst_equal by exact Hvalue.
  rewrite IH. tauto.
Qed.

Lemma formula_holds_single_subst_equal i rho x replacement f :
  rho x = eval_term rho replacement ->
  formula_holds i rho (subst_formula [(x, replacement)] f) <->
  formula_holds i rho f.
Proof.
  intro Hvalue. unfold formula_holds, subst_formula.
  split; intros [p [Hin Hp]].
  - apply in_map_iff in Hin. destruct Hin as [original [<- Hin]].
    exists original. split; [exact Hin|].
    now apply (proj1 (product_holds_single_subst_equal
      i rho x replacement original Hvalue)).
  - exists (subst_product [(x, replacement)] p). split.
    + now apply in_map.
    + now apply (proj2 (product_holds_single_subst_equal
        i rho x replacement p Hvalue)).
Qed.

Lemma rank_atom_single_subst_equal i rho trace x replacement a :
  rho x = eval_term rho replacement ->
  rank_atom i rho trace (subst_atom [(x, replacement)] a) =
  rank_atom i rho trace a.
Proof.
  intro Hvalue. destruct a as [u v|u v|tag name args]; simpl; auto.
  now rewrite eval_terms_single_subst_equal by exact Hvalue.
Qed.

Lemma rank_product_single_subst_equal i rho trace x replacement p :
  rho x = eval_term rho replacement ->
  rank_product i rho trace (subst_product [(x, replacement)] p) =
  rank_product i rho trace p.
Proof.
  intro Hvalue. induction p as [|a p IH]; simpl; auto.
  rewrite rank_atom_single_subst_equal by exact Hvalue.
  destruct (rank_atom i rho trace a); auto.
Qed.

Lemma rank_formula_single_subst_equal i rho trace x replacement f :
  rho x = eval_term rho replacement ->
  rank_formula i rho trace (subst_formula [(x, replacement)] f) =
  rank_formula i rho trace f.
Proof.
  intro Hvalue. induction f as [|p f IH]; simpl; auto.
  rewrite rank_product_single_subst_equal by exact Hvalue.
  destruct (rank_product i rho trace p); auto.
Qed.

Definition left_equality_source
    (ds : definitions) (before : product) (id : nat) (replacement : term)
    (after : product) (rhs : formula) : judgment :=
  mk_judgment ds
    (mk_sequent
      [(before ++ Eq (Var (free_var id)) replacement :: after)%list] rhs).

Definition left_equality_target
    (ds : definitions) (before : product) (id : nat) (replacement : term)
    (after : product) (rhs : formula) : judgment :=
  let theta := [(free_var id, replacement)] in
  mk_judgment ds
    (subst_sequent theta
      (mk_sequent
        [(before ++ Eq (Var (free_var id)) replacement :: after)%list] rhs)).

Lemma left_equality_rank ds before id replacement after rhs i rho trace
    (Hvalue : rho (free_var id) = eval_term rho replacement) :
  FirstOrderTheory.rank
    (left_equality_target ds before id replacement after rhs) (i, rho) trace =
  FirstOrderTheory.rank
    (left_equality_source ds before id replacement after rhs) (i, rho) trace.
Proof.
  unfold FirstOrderTheory.rank, rank_of_tag, left_equality_target,
    left_equality_source, mk_judgment, subst_sequent, mk_sequent. simpl.
  now rewrite rank_product_single_subst_equal by exact Hvalue.
Qed.

(** The restriction [term_freeb replacement = true] is semantic, not merely
    an implementation convenience.  It ensures that the equality remains
    true when the succedent switches from the base valuation to an existential
    witness valuation. *)
Definition left_equality_substitution_rule
    (ds : definitions) (before : product) (id : nat) (replacement : term)
    (after : product) (rhs : formula)
    (Hreplacement_free : term_freeb replacement = true)
    : Cyclic.rule_instance.
Proof.
  set (source := left_equality_source ds before id replacement after rhs).
  set (target := left_equality_target ds before id replacement after rhs).
  set (p := {| Cyclic.premise_judgment := target;
               Cyclic.premise_edge := identity_edge source |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "Eq subst";
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := [p] |}.
  - intros Hvalid [i rho].
    unfold source, left_equality_source, denote, sequent_holds; simpl.
    intros Hmodel Hlhs.
    apply formula_holds_singleton_inv in Hlhs.
    assert (Heqin : In (Eq (Var (free_var id)) replacement)
      (before ++ Eq (Var (free_var id)) replacement :: after)%list).
    { apply in_or_app. right. now left. }
    pose proof (product_holds_atom i rho _
      (Eq (Var (free_var id)) replacement) Hlhs Heqin) as Hvalue.
    simpl in Hvalue.
    pose proof (Hvalid p ltac:(now left) (i, rho)) as Htarget.
    unfold p, target, left_equality_target, denote, sequent_holds in Htarget;
      simpl in Htarget.
    specialize (Htarget Hmodel).
    assert (Htarget_lhs : formula_holds i rho
      (subst_formula [(free_var id, replacement)]
        [(before ++ Eq (Var (free_var id)) replacement :: after)%list])).
    {
      apply (proj2 (formula_holds_single_subst_equal i rho
        (free_var id) replacement _ Hvalue)).
      apply formula_holds_cons_intro. exact Hlhs.
    }
    destruct (Htarget Htarget_lhs) as [witness Hright].
    exists witness.
    assert (Hmerged :
      merge_valuation rho witness (free_var id) =
      eval_term (merge_valuation rho witness) replacement).
    {
      simpl. rewrite eval_term_merge_free by exact Hreplacement_free.
      exact Hvalue.
    }
    now apply (proj1 (formula_holds_single_subst_equal i
      (merge_valuation rho witness) (free_var id) replacement rhs Hmerged)).
  - intros [i rho] Hfalse.
    assert (Hsource : ~ denote
      (left_equality_source ds before id replacement after rhs) (i, rho)).
    { now unfold source in Hfalse. }
    destruct (false_world_parts ds
      (mk_sequent
        [(before ++ Eq (Var (free_var id)) replacement :: after)%list] rhs)
      i rho Hsource) as [Hmodel [Hlhs Hright]].
    apply formula_holds_singleton_inv in Hlhs.
    assert (Heqin : In (Eq (Var (free_var id)) replacement)
      (before ++ Eq (Var (free_var id)) replacement :: after)%list).
    { apply in_or_app. right. now left. }
    pose proof (product_holds_atom i rho _
      (Eq (Var (free_var id)) replacement) Hlhs Heqin) as Hvalue.
    simpl in Hvalue.
    exists 0, p, (i, rho). split; [reflexivity|]. split.
    + unfold p, target, left_equality_target.
      apply make_false_world; [exact Hmodel| |].
      * apply (proj2 (formula_holds_single_subst_equal i rho
          (free_var id) replacement _ Hvalue)).
        apply formula_holds_cons_intro. exact Hlhs.
      * intro Htarget_right. apply Hright.
        destruct Htarget_right as [witness Htarget_formula]. exists witness.
        assert (Hmerged :
          merge_valuation rho witness (free_var id) =
          eval_term (merge_valuation rho witness) replacement).
        {
          simpl. rewrite eval_term_merge_free by exact Hreplacement_free.
          exact Hvalue.
        }
        now apply (proj1 (formula_holds_single_subst_equal i
          (merge_valuation rho witness) (free_var id) replacement rhs Hmerged)).
    + unfold p, source, target.
      apply identity_edge_respects_rank_equivalence.
      intro trace. now apply left_equality_rank.
Defined.

(** ** Explicit weakening used before a backlink *)

Lemma in_identity_pairs_members a b tags :
  In (a, b) (Cyclic.identity_pairs tags) -> a = b /\ In a tags.
Proof.
  unfold Cyclic.identity_pairs. intro H. apply in_map_iff in H.
  destruct H as [tag [Heq Hin]]. inversion Heq; subst. auto.
Qed.

Lemma product_tag_has_rank i rho trace p :
  In trace (product_tags p) ->
  exists n, rank_product i rho trace p = Some n.
Proof.
  induction p as [|a p IH]; simpl; [contradiction|].
  destruct a as [x y|x y|tag name args]; simpl.
  - apply IH.
  - apply IH.
  - destruct tag as [current|]; simpl.
    + intros [Heq | Hin].
      * subst current. rewrite Nat.eqb_refl.
        destruct (i.(predicate_rank) name (eval_terms rho args)) as [height|].
        -- now exists (S height).
        -- now exists 0.
      * destruct (Nat.eqb trace current) eqn:Hsame.
        -- destruct (i.(predicate_rank) name (eval_terms rho args))
             as [height|]; [now exists (S height)|now exists 0].
        -- apply IH. exact Hin.
    + apply IH.
Qed.

Definition prefix_weakening_source
    (ds : definitions) (small extra : product) (rhs : formula) : judgment :=
  mk_judgment ds (mk_sequent [(small ++ extra)%list] rhs).

Definition prefix_weakening_target
    (ds : definitions) (small : product) (rhs : formula) : judgment :=
  mk_judgment ds (mk_sequent [small] rhs).

Lemma prefix_weakening_rank ds small extra rhs w trace
    (Htag : In trace
      (judgment_tags (prefix_weakening_target ds small rhs))) :
  FirstOrderTheory.rank (prefix_weakening_target ds small rhs) w trace =
  FirstOrderTheory.rank (prefix_weakening_source ds small extra rhs) w trace.
Proof.
  destruct w as [i rho].
  unfold judgment_tags, sequent_tags, prefix_weakening_target,
    prefix_weakening_source, mk_judgment, mk_sequent in Htag |- *; simpl in *.
  apply nodup_In in Htag.
  rewrite app_nil_r in Htag.
  destruct (product_tag_has_rank i rho trace small Htag) as [n Hrank].
  unfold FirstOrderTheory.rank, rank_of_tag; simpl.
  rewrite Hrank.
  now rewrite (rank_product_app_some i rho trace small extra n Hrank).
Qed.

Definition prefix_weakening_rule
    (ds : definitions) (small extra : product) (rhs : formula)
    : Cyclic.rule_instance.
Proof.
  set (source := prefix_weakening_source ds small extra rhs).
  set (target := prefix_weakening_target ds small rhs).
  set (edge := identity_edge target).
  set (p := {| Cyclic.premise_judgment := target;
               Cyclic.premise_edge := edge |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "Weaken";
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := [p] |}.
  - intros Hvalid [i rho]. unfold source, prefix_weakening_source,
      denote, sequent_holds; simpl.
    intros Hmodel Hlhs. apply formula_holds_singleton_inv in Hlhs.
    pose proof (proj1 (product_holds_app i rho small extra) Hlhs) as [Hsmall _].
    pose proof (Hvalid p ltac:(now left) (i, rho)) as Htarget.
    unfold p, target, prefix_weakening_target, denote, sequent_holds in Htarget;
      simpl in Htarget.
    apply Htarget; [exact Hmodel|].
    apply formula_holds_cons_intro. exact Hsmall.
  - intros [i rho] Hfalse.
    assert (Hsource : ~ denote (prefix_weakening_source ds small extra rhs)
      (i, rho)).
    { now unfold source in Hfalse. }
    destruct (false_world_parts ds
      (mk_sequent [(small ++ extra)%list] rhs) i rho Hsource)
      as [Hmodel [Hlhs Hright]].
    apply formula_holds_singleton_inv in Hlhs.
    pose proof (proj1 (product_holds_app i rho small extra) Hlhs) as [Hsmall _].
    exists 0, p, (i, rho). split; [reflexivity|]. split.
    + unfold p, target, prefix_weakening_target.
      apply make_false_world; [exact Hmodel| |exact Hright].
      apply formula_holds_cons_intro. exact Hsmall.
    + unfold p, edge, source, target. split.
      * intros a b Hin. destruct (in_identity_pairs_members a b _ Hin)
          as [-> Htag].
        change
          (FirstOrderTheory.rank (prefix_weakening_target ds small rhs)
             (i, rho) b <=
           FirstOrderTheory.rank (prefix_weakening_source ds small extra rhs)
             (i, rho) b).
        rewrite (prefix_weakening_rank ds small extra rhs (i, rho) b Htag).
        apply Nat.le_refl.
      * intros a b Hin. inversion Hin.
Defined.

(** ** Explicit free-variable substitution used before a backlink *)

(** The executable matcher may discover several bindings at once.  Such a
    substitution is safe across our sequent semantics when it changes only
    free variables and every replacement is itself free of existential
    variables.  The latter condition is essential: the succedent is evaluated
    under [merge_valuation base witness], and a replacement containing an
    existential variable could otherwise observe a different value after the
    witness is installed. *)
Fixpoint free_substitutionb (s : substitution) : bool :=
  match s with
  | [] => true
  | (x, replacement) :: rest =>
      match x.(variable_kind) with
      | Free => term_freeb replacement && free_substitutionb rest
      | Existential => false
      end
  end.

(** A successful [free_substitutionb] check says that every value returned by
    lookup is a free term.  Notice that this remains true in the presence of
    duplicate keys: [lookup_substitution] returns the first binding, and that
    binding is among those checked by [free_substitutionb]. *)
Lemma free_substitutionb_lookup_range s x replacement :
  free_substitutionb s = true ->
  lookup_substitution s x = Some replacement ->
  term_freeb replacement = true.
Proof.
  induction s as [|[bound value] rest IH]; simpl; intros Hfree Hlookup.
  - discriminate.
  - destruct bound as [kind id]. destruct kind; [|discriminate].
    apply Bool.andb_true_iff in Hfree as [Hvalue Hrest].
    destruct (variable_eqb x {| variable_kind := Free; variable_id := id |})
      eqn:Hsame.
    + inversion Hlookup; subst. exact Hvalue.
    + now apply IH.
Qed.

(** Existential variables cannot occur in the domain of a checked free
    substitution.  This lemma is the other half of the commuting argument
    below: witness variables must continue to be read directly from the
    witness valuation. *)
Lemma free_substitutionb_lookup_existential_none s id :
  free_substitutionb s = true ->
  lookup_substitution s (existential_var id) = None.
Proof.
  induction s as [|[bound value] rest IH]; simpl; intro Hfree; [reflexivity|].
  destruct bound as [kind current]. destruct kind; [|discriminate].
  apply Bool.andb_true_iff in Hfree as [_ Hrest].
  unfold variable_eqb, existential_var, var_kind_eqb; simpl.
  now apply IH.
Qed.

(** This is the semantic reason for [free_substitutionb].  Substitution may be
    evaluated before or after installing an existential witness, with exactly
    the same resulting valuation. *)
Lemma substitution_valuation_merge_free base witness s
    (Hfree : free_substitutionb s = true) :
  substitution_valuation (merge_valuation base witness) s =
  merge_valuation (substitution_valuation base s) witness.
Proof.
  apply functional_extensionality. intros [kind id]. destruct kind.
  - unfold substitution_valuation, merge_valuation. simpl.
    destruct (lookup_substitution s (free_var id)) as [replacement|]
      eqn:Hlookup; simpl.
    + unfold free_var in Hlookup. rewrite Hlookup. simpl.
      apply eval_term_merge_free.
      exact (free_substitutionb_lookup_range s (free_var id) replacement
        Hfree ltac:(exact Hlookup)).
    + unfold free_var in Hlookup. rewrite Hlookup. reflexivity.
  - unfold substitution_valuation, merge_valuation. simpl.
    pose proof (free_substitutionb_lookup_existential_none s id Hfree)
      as Hnone. unfold existential_var in Hnone. rewrite Hnone.
    reflexivity.
Qed.

Definition general_free_substitution_source
    (ds : definitions) (q : sequent) (s : substitution) : judgment :=
  mk_judgment ds (subst_sequent s q).

Definition general_free_substitution_target
    (ds : definitions) (q : sequent) : judgment := mk_judgment ds q.

Lemma general_free_substitution_rank ds q s i rho trace :
  FirstOrderTheory.rank (general_free_substitution_source ds q s)
    (i, rho) trace =
  FirstOrderTheory.rank (general_free_substitution_target ds q)
    (i, substitution_valuation rho s) trace.
Proof.
  unfold FirstOrderTheory.rank, rank_of_tag,
    general_free_substitution_source, general_free_substitution_target,
    mk_judgment, subst_sequent, mk_sequent. simpl.
  apply rank_formula_substitution_valuation.
Qed.

(** The multi-binding counterpart of the OCaml [subst_rule].  It has one
    premise—the unsubstituted ancestor—and records no progressing trace pair,
    because substitution changes term values but does not unfold an inductive
    predicate. *)
Definition general_free_substitution_rule
    (ds : definitions) (q : sequent) (s : substitution)
    (Hfree : free_substitutionb s = true) : Cyclic.rule_instance.
Proof.
  set (source := general_free_substitution_source ds q s).
  set (target := general_free_substitution_target ds q).
  set (edge := identity_edge source).
  set (p := {| Cyclic.premise_judgment := target;
               Cyclic.premise_edge := edge |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "Subst";
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := [p] |}.
  - intros Hvalid [i rho]. unfold source, general_free_substitution_source,
      denote, sequent_holds; simpl.
    intros Hmodel Hlhs.
    set (rho' := substitution_valuation rho s).
    pose proof (Hvalid p ltac:(now left) (i, rho')) as Htarget.
    unfold p, target, general_free_substitution_target, denote, sequent_holds
      in Htarget; simpl in Htarget.
    assert (Htarget_lhs : formula_holds i rho' q.(antecedent)).
    {
      unfold rho'.
      now apply (proj1
        (formula_holds_substitution_valuation i rho s q.(antecedent))).
    }
    destruct (Htarget Hmodel Htarget_lhs) as [witness Htarget_right].
    exists witness.
    apply (proj2 (formula_holds_substitution_valuation i
      (merge_valuation rho witness) s q.(succedent))).
    rewrite substitution_valuation_merge_free by exact Hfree.
    exact Htarget_right.
  - intros [i rho] Hfalse.
    assert (Hsource :
      ~ denote (general_free_substitution_source ds q s) (i, rho)).
    { now unfold source in Hfalse. }
    destruct (false_world_parts ds (subst_sequent s q) i rho Hsource)
      as [Hmodel [Hlhs Hright]].
    set (rho' := substitution_valuation rho s).
    exists 0, p, (i, rho'). split; [reflexivity|]. split.
    + unfold p, target, general_free_substitution_target.
      apply make_false_world; [exact Hmodel| |].
      * unfold rho'.
        now apply (proj1
          (formula_holds_substitution_valuation i rho s q.(antecedent))).
      * intro Htarget_right. apply Hright.
        destruct Htarget_right as [witness Htarget_formula]. exists witness.
        apply (proj2 (formula_holds_substitution_valuation i
          (merge_valuation rho witness) s q.(succedent))).
        rewrite substitution_valuation_merge_free by exact Hfree.
        exact Htarget_formula.
    + unfold p, edge, source, target. split.
      * intros a b Hin. apply in_identity_pairs_eq in Hin. subst b.
        change
          (FirstOrderTheory.rank (general_free_substitution_target ds q)
             (i, rho') a <=
           FirstOrderTheory.rank (general_free_substitution_source ds q s)
             (i, rho) a).
        unfold rho'. rewrite general_free_substitution_rank.
        apply Nat.le_refl.
      * intros a b Hin. inversion Hin.
Defined.

(** The original single-binding API remains as a small specialization.  It is
    used by existing examples and makes the simplest substitution proof easy
    to inspect in isolation. *)

Definition single_free_substitution (id : nat) (replacement : term)
    : substitution := [(free_var id, replacement)].

Lemma substitution_valuation_merge_single_free base witness id replacement
    (Hfree : term_freeb replacement = true) :
  substitution_valuation (merge_valuation base witness)
    (single_free_substitution id replacement) =
  merge_valuation
    (substitution_valuation base (single_free_substitution id replacement))
    witness.
Proof.
  apply functional_extensionality. intros [kind current].
  destruct kind.
  - unfold substitution_valuation at 1. simpl.
    rewrite eval_term_merge_free.
    + reflexivity.
    + unfold single_free_substitution, lookup_substitution, variable_eqb,
        var_kind_eqb, free_var; simpl.
      destruct (Nat.eqb current id); simpl; [exact Hfree|reflexivity].
  - unfold substitution_valuation, single_free_substitution,
      lookup_substitution, variable_eqb, var_kind_eqb, free_var,
      merge_valuation; simpl. reflexivity.
Qed.

Definition free_substitution_source
    (ds : definitions) (q : sequent) (id : nat) (replacement : term)
    : judgment :=
  mk_judgment ds (subst_sequent (single_free_substitution id replacement) q).

Definition free_substitution_target (ds : definitions) (q : sequent)
    : judgment := mk_judgment ds q.

Lemma free_substitution_rank ds q id replacement i rho trace :
  FirstOrderTheory.rank (free_substitution_source ds q id replacement)
    (i, rho) trace =
  FirstOrderTheory.rank (free_substitution_target ds q)
    (i, substitution_valuation rho (single_free_substitution id replacement))
    trace.
Proof.
  unfold FirstOrderTheory.rank, rank_of_tag, free_substitution_source,
    free_substitution_target, mk_judgment, subst_sequent, mk_sequent. simpl.
  apply rank_formula_substitution_valuation.
Qed.

Definition free_substitution_rule
    (ds : definitions) (q : sequent) (id : nat) (replacement : term)
    (Hfree : term_freeb replacement = true) : Cyclic.rule_instance.
Proof.
  set (source := free_substitution_source ds q id replacement).
  set (target := free_substitution_target ds q).
  set (edge := identity_edge source).
  set (p := {| Cyclic.premise_judgment := target;
               Cyclic.premise_edge := edge |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "Subst";
       Cyclic.rule_conclusion := source;
       Cyclic.rule_premises := [p] |}.
  - intros Hvalid [i rho]. unfold source, free_substitution_source,
      denote, sequent_holds; simpl.
    intros Hmodel Hlhs.
    set (rho' := substitution_valuation rho
      (single_free_substitution id replacement)).
    pose proof (Hvalid p ltac:(now left) (i, rho')) as Htarget.
    unfold p, target, free_substitution_target, denote, sequent_holds in Htarget;
      simpl in Htarget.
    assert (Htarget_lhs : formula_holds i rho' q.(antecedent)).
    {
      unfold rho'.
      now apply (proj1 (formula_holds_substitution_valuation i rho
        (single_free_substitution id replacement) q.(antecedent))).
    }
    destruct (Htarget Hmodel Htarget_lhs) as [witness Htarget_right].
    exists witness.
    apply (proj2 (formula_holds_substitution_valuation i
      (merge_valuation rho witness)
      (single_free_substitution id replacement) q.(succedent))).
    rewrite substitution_valuation_merge_single_free by exact Hfree.
    exact Htarget_right.
  - intros [i rho] Hfalse.
    assert (Hsource : ~ denote (free_substitution_source ds q id replacement)
      (i, rho)).
    { now unfold source in Hfalse. }
    destruct (false_world_parts ds
      (subst_sequent (single_free_substitution id replacement) q)
      i rho Hsource) as [Hmodel [Hlhs Hright]].
    set (rho' := substitution_valuation rho
      (single_free_substitution id replacement)).
    exists 0, p, (i, rho'). split; [reflexivity|]. split.
    + unfold p, target, free_substitution_target.
      apply make_false_world; [exact Hmodel| |].
      * unfold rho'.
        now apply (proj1 (formula_holds_substitution_valuation i rho
          (single_free_substitution id replacement) q.(antecedent))).
      * intro Htarget_right. apply Hright.
        destruct Htarget_right as [witness Htarget_formula]. exists witness.
        apply (proj2 (formula_holds_substitution_valuation i
          (merge_valuation rho witness)
          (single_free_substitution id replacement) q.(succedent))).
        rewrite substitution_valuation_merge_single_free by exact Hfree.
        exact Htarget_formula.
    + unfold p, edge, source, target. split.
      * intros a b Hin. apply in_identity_pairs_eq in Hin. subst b.
        change
          (FirstOrderTheory.rank (free_substitution_target ds q) (i, rho') a <=
           FirstOrderTheory.rank
             (free_substitution_source ds q id replacement) (i, rho) a).
        unfold rho'.
        rewrite free_substitution_rank. apply Nat.le_refl.
      * intros a b Hin. inversion Hin.
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

(** ** Left unfolding at an arbitrary product position

    The antecedent of an unfoldable first-order goal is a singleton formula,
    but its unique product may contain several tagged predicates.  As on the
    right, list position is not logical structure.  The following lemmas show
    that moving one selected tagged predicate to the head preserves both
    truth and trace rank, provided its tag does not already occur in the
    skipped prefix.  That side condition rules out an ambiguous input with
    duplicate trace tags. *)

Lemma rank_product_remove_different_tag i rho selected name args
    before after trace :
  trace <> selected ->
  rank_product i rho trace
    (before ++ Pred (Some selected) name args :: after)%list =
  rank_product i rho trace (before ++ after)%list.
Proof.
  intro Hdifferent. induction before as [|a before IH]; simpl.
  - destruct (Nat.eqb trace selected) eqn:Heq.
    + apply Nat.eqb_eq in Heq. contradiction.
    + reflexivity.
  - destruct (rank_atom i rho trace a); [reflexivity|exact IH].
Qed.

Lemma rank_product_move_selected_tag i rho selected name args before after :
  ~ In selected (product_tags before) ->
  rank_product i rho selected
    (before ++ Pred (Some selected) name args :: after)%list =
  rank_product i rho selected
    (Pred (Some selected) name args :: before ++ after)%list.
Proof.
  induction before as [|a before IH]; simpl; intro Habsent.
  - reflexivity.
  - destruct a as [x y|x y|tag predicate arguments]; simpl in *.
    + apply IH. tauto.
    + apply IH. tauto.
    + destruct tag as [current|]; simpl in *.
      * assert (Hneq : selected <> current).
        { intro Heq. apply Habsent. left. now symmetry. }
        assert (Heq : Nat.eqb selected current = false).
        { apply Nat.eqb_neq. exact Hneq. }
        rewrite Heq. apply IH. intro Hin. apply Habsent. now right.
      * apply IH. exact Habsent.
Qed.

Lemma rank_product_rotate_tagged i rho selected name args before after trace :
  ~ In selected (product_tags before) ->
  rank_product i rho trace
    (before ++ Pred (Some selected) name args :: after)%list =
  rank_product i rho trace
    (Pred (Some selected) name args :: before ++ after)%list.
Proof.
  intro Habsent. destruct (Nat.eq_dec trace selected) as [->|Hdifferent].
  - now apply rank_product_move_selected_tag.
  - rewrite (rank_product_remove_different_tag i rho selected name args
      before after trace Hdifferent).
    simpl. destruct (Nat.eqb trace selected) eqn:Heq.
    + apply Nat.eqb_eq in Heq. contradiction.
    + reflexivity.
Qed.

Definition left_unfold_at_source
    (ds : definitions) (before : product) (tag : nat)
    (name : string) (args : list term) (after : product) (rhs : formula)
    : judgment :=
  mk_judgment ds
    (mk_sequent [(before ++ Pred (Some tag) name args :: after)%list] rhs).

Definition left_unfold_at_rotated
    (ds : definitions) (before : product) (tag : nat)
    (name : string) (args : list term) (after : product) (rhs : formula)
    : judgment :=
  mk_judgment ds
    (mk_sequent [(Pred (Some tag) name args :: before ++ after)%list] rhs).

Lemma left_unfold_at_semantics ds before tag name args after rhs w :
  denote (left_unfold_at_source ds before tag name args after rhs) w <->
  denote (left_unfold_at_rotated ds before tag name args after rhs) w.
Proof.
  destruct w as [i rho]. unfold left_unfold_at_source,
    left_unfold_at_rotated, denote, sequent_holds, mk_judgment, mk_sequent;
    simpl.
  split; intros H Hmodel Hlhs.
  - apply H; [exact Hmodel|].
    apply formula_holds_singleton_inv in Hlhs.
    apply formula_holds_cons_intro.
    now apply (proj2 (product_holds_rotate i rho before
      (Pred (Some tag) name args) after)).
  - apply H; [exact Hmodel|].
    apply formula_holds_singleton_inv in Hlhs.
    apply formula_holds_cons_intro.
    now apply (proj1 (product_holds_rotate i rho before
      (Pred (Some tag) name args) after)).
Qed.

Lemma left_unfold_at_rank ds before tag name args after rhs w trace :
  ~ In tag (product_tags before) ->
  FirstOrderTheory.rank
    (left_unfold_at_rotated ds before tag name args after rhs) w trace =
  FirstOrderTheory.rank
    (left_unfold_at_source ds before tag name args after rhs) w trace.
Proof.
  intro Habsent. destruct w as [i rho]. unfold FirstOrderTheory.rank,
    rank_of_tag, left_unfold_at_rotated, left_unfold_at_source, mk_judgment,
    mk_sequent; simpl.
  symmetry.
  rewrite (rank_product_rotate_tagged i rho tag name args before after trace
    Habsent). reflexivity.
Qed.

Definition left_unfold_at_rule
    (ds : definitions) (offset : nat) (before : product) (tag fresh : nat)
    (name : string) (args : list term) (after : product) (rhs : formula)
    (Hbefore : ~ In tag (product_tags before))
    (Htag : tag <> fresh)
    (Hbelow : product_belowb offset
      (Pred (Some tag) name args :: before ++ after) = true)
    (Hrhsfree : formula_freeb rhs = true)
    (Hrhsbelow : formula_belowb offset rhs = true)
    : Cyclic.rule_instance :=
  let basic := left_unfold_rule ds offset tag fresh name args
    (before ++ after)%list rhs Htag Hbelow Hrhsfree Hrhsbelow in
  transport_rule_conclusion "L.Unfold"
    (left_unfold_at_source ds before tag name args after rhs)
    basic
    (left_unfold_at_semantics ds before tag name args after rhs)
    (fun w trace =>
      left_unfold_at_rank ds before tag name args after rhs w trace Hbefore).
