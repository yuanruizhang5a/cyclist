From Stdlib Require Import List Bool Arith Lia String Permutation Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription.

From CyclistRocq.SP Require Import Syntax Semantics.

Import ListNotations.
Open Scope string_scope.

(** * Kernel-checked rule instances *)

Definition empty_edge : Cyclic.edge_info :=
  {| Cyclic.edge_valid := []; Cyclic.edge_progress := [] |}.

Lemma empty_edge_respected source target w w' :
  Cyclic.respects_edge source target w w' empty_edge.
Proof. split; intros a b H; inversion H. Qed.

Definition replace_heaps (f : formula) (heaps : list symheap) : formula :=
  {| formula_constraints := f.(formula_constraints);
     formula_heaps := heaps |}.

Definition replace_antecedent (q : sequent) (left : formula) : sequent :=
  {| antecedent := left; succedent := q.(succedent) |}.

Definition replace_succedent (q : sequent) (right : formula) : sequent :=
  {| antecedent := q.(antecedent); succedent := right |}.

(** Exact identity is the smallest trusted leaf and is intentionally useful
    even when no inductive definitions are present. *)
Lemma identity_valid ds f :
  Cyclic.Valid (mk_judgment ds (mk_sequent f f)).
Proof. intros w H. exact H. Qed.

Definition identity_axiom ds f : Cyclic.axiom_instance :=
  {| Cyclic.axiom_name := "identity";
     Cyclic.axiom_conclusion := mk_judgment ds (mk_sequent f f);
     Cyclic.axiom_theorem := identity_valid ds f |}.

(** Dropping predicate tags is semantically safe: a tag adds only an ordinal
    upper-bound obligation.  This yields the sound direction of identity
    modulo tags. *)
Lemma erased_predicate_holds ds rho tau p h :
  formula_predicate_holds ds rho tau p h ->
  formula_predicate_holds ds rho tau (erase_predicate_tag p) h.
Proof.
  intros [rank [Hrank Htag]]. exists rank. split; [exact Hrank|exact I].
Qed.

Lemma spatial_erase_tags ds rho tau atoms h :
  spatial_holds_with (formula_predicate_holds ds rho tau) rho atoms h ->
  spatial_holds_with (formula_predicate_holds ds rho tau) rho
    (map (fun atom =>
       match atom with
       | CellAtom p => CellAtom p
       | PredicateAtom p => PredicateAtom (erase_predicate_tag p)
       end) atoms) h.
Proof.
  revert h. induction atoms as [|atom atoms IH]; intros h H; simpl in *.
  - exact H.
  - destruct H as [owned [frame [Hjoin [Hatom Hrest]]]].
    exists owned, frame. split; [exact Hjoin|]. split.
    + destruct atom; simpl in *; [exact Hatom|now apply erased_predicate_holds].
    + now apply IH.
Qed.

Lemma heap_erase_tags_holds ds rho tau h sh :
  symheap_holds_with (formula_predicate_holds ds rho tau) rho h sh ->
  symheap_holds_with (formula_predicate_holds ds rho tau) rho h
    (erase_heap_tags sh).
Proof.
  intros [Hpure Hspatial]. split; [exact Hpure|].
  unfold heap_spatial_atoms in *. simpl.
  pose proof (spatial_erase_tags ds rho tau
    (map CellAtom (heap_points sh) ++ map PredicateAtom (heap_predicates sh))
    h Hspatial) as H.
  simpl in H. rewrite map_app, !map_map in H. simpl in H.
  rewrite map_map. exact H.
Qed.

Lemma tag_erasure_valid ds f :
  Cyclic.Valid (mk_judgment ds (mk_sequent f (erase_formula_tags f))).
Proof.
  intros w Hleft.
  destruct Hleft as [wr [wt [sh [Hin [Hcs Hheap]]]]].
  exists wr, wt, (erase_heap_tags sh). simpl.
  split.
  - apply in_map. exact Hin.
  - split; [exact I|]. now apply heap_erase_tags_holds.
Qed.

Definition tag_erasure_axiom ds f : Cyclic.axiom_instance :=
  {| Cyclic.axiom_name := "identity-modulo-tags";
     Cyclic.axiom_conclusion :=
       mk_judgment ds (mk_sequent f (erase_formula_tags f));
     Cyclic.axiom_theorem := tag_erasure_valid ds f |}.

(** The executable inconsistency test recognizes an explicit [t <> t]. *)
Lemma heap_inconsistentb_sound h :
  heap_inconsistentb h = true ->
  forall ds rho tau concrete,
    ~ symheap_holds_with (formula_predicate_holds ds rho tau)
        rho concrete h.
Proof.
  unfold heap_inconsistentb. rewrite existsb_exists.
  intros [a [Hin Ha]] ds rho tau concrete [Hpure _].
  unfold pure_reflexive_contradiction in Ha.
  destruct a as [x y|x y]; simpl in Ha; try discriminate.
  apply term_eqb_spec in Ha. subst y.
  pose proof (pures_hold_in rho h.(heap_pure) (Disequal x x) Hpure Hin) as Hbad.
  exact (reflexive_disequality_false rho x Hbad).
Qed.

Lemma formula_inconsistentb_sound f :
  formula_inconsistentb f = true ->
  forall ds rho tau concrete, ~ formula_holds ds rho tau concrete f.
Proof.
  unfold formula_inconsistentb. rewrite forallb_forall.
  intros Hall ds rho tau concrete Hholds.
  destruct Hholds as [wr [wt [sh [Hin [_ Hheap]]]]].
  specialize (Hall sh Hin).
  exact (heap_inconsistentb_sound sh Hall ds
    (merge_valuation rho wr) (merge_tag_valuation tau wt) concrete Hheap).
Qed.

Lemma ex_falso_valid ds left right :
  formula_inconsistentb left = true ->
  Cyclic.Valid (mk_judgment ds (mk_sequent left right)).
Proof.
  intros Hbad w Hleft.
  exfalso. exact (formula_inconsistentb_sound left Hbad ds
    w.(world_variables) w.(world_tags) w.(world_heap) Hleft).
Qed.

Definition ex_falso_axiom ds left right
    (Hbad : formula_inconsistentb left = true) : Cyclic.axiom_instance :=
  {| Cyclic.axiom_name := "pure-ex-falso";
     Cyclic.axiom_conclusion := mk_judgment ds (mk_sequent left right);
     Cyclic.axiom_theorem := ex_falso_valid ds left right Hbad |}.

(** A finite list of predicate witnesses always has a common numeric bound.
    This lemma converts the unbounded formula interpretation into the bounded
    interpretation expected by one ranked clause unfolding. *)
Definition bounded_predicate_holds
    (ds : definitions) (rho : valuation) (bound : nat)
    (p : tagged_predicate) (h : concrete_heap) : Prop :=
  exists rank,
    rank <= bound /\
    predicate_holds_rank ds rank p.(predicate_name)
      (eval_terms rho p.(predicate_arguments)) h.

Lemma spatial_predicate_mono P Q rho atoms h :
  (forall p owned, P p owned -> Q p owned) ->
  spatial_holds_with P rho atoms h ->
  spatial_holds_with Q rho atoms h.
Proof.
  intros Hmono. revert h. induction atoms as [|a rest IH]; intros h H; simpl in *.
  - exact H.
  - destruct H as [owned [frame [Hjoin [Ha Hr]]]].
    exists owned, frame. split; [exact Hjoin|]. split.
    + destruct a; simpl in *; auto.
    + now apply IH.
Qed.

Lemma bounded_predicate_mono ds rho small large :
  small <= large ->
  forall p h,
    bounded_predicate_holds ds rho small p h ->
    bounded_predicate_holds ds rho large p h.
Proof.
  intros Hle p h [rank [Hrank Hholds]].
  exists rank. split; [lia|exact Hholds].
Qed.

Lemma spatial_formula_has_bound ds rho tau atoms h :
  spatial_holds_with (formula_predicate_holds ds rho tau) rho atoms h ->
  exists bound, spatial_holds_with
    (bounded_predicate_holds ds rho bound) rho atoms h.
Proof.
  revert h. induction atoms as [|a rest IH]; intros h H; simpl in *.
  - exists 0. exact H.
  - destruct H as [owned [frame [Hjoin [Ha Hr]]]].
    destruct (IH frame Hr) as [rest_bound Hrest].
    destruct a as [cell|p].
    + exists rest_bound. exists owned, frame.
      split; [exact Hjoin|]. split; assumption.
    + simpl in Ha. destruct Ha as [rank [Hrank _]].
      exists (Nat.max rank rest_bound).
      exists owned, frame. split; [exact Hjoin|]. split.
      * simpl. exists rank. split; [apply Nat.le_max_l|exact Hrank].
      * eapply spatial_predicate_mono; [|exact Hrest].
        apply bounded_predicate_mono. apply Nat.le_max_r.
Qed.

Lemma heap_formula_has_bound ds rho tau h sh :
  symheap_holds_with (formula_predicate_holds ds rho tau) rho h sh ->
  exists bound,
    symheap_holds_with (bounded_predicate_holds ds rho bound) rho h sh.
Proof.
  intros [Hpure Hspatial].
  destruct (spatial_formula_has_bound ds rho tau
    (heap_spatial_atoms sh) h Hspatial) as [bound Hbounded].
  exists bound. split; assumption.
Qed.

Lemma heap_join_empty_right h : heap_join h [] h.
Proof.
  split.
  - intros address fields fields' Hl Hr. inversion Hr.
  - rewrite app_nil_r. apply Permutation_refl.
Qed.

(** General right predicate introduction.  It applies to every clause and
    every executable term substitution; it is not tied to a benchmark. *)
Definition predicate_conclusion_heap
    (name : string) (args : list term) : symheap :=
  mk_heap [] [] [untagged_pred name args].

Lemma predicate_intro_valid ds name c s :
  In c (lookup_definition name ds) ->
  Cyclic.Valid
    (mk_judgment ds
      (mk_sequent (singleton_formula (subst_heap s c.(clause_body)))
        (singleton_formula
          (predicate_conclusion_heap name
            (map (subst_term s) c.(clause_head)))))).
Proof.
  intros Hclause w Hleft.
  destruct Hleft as [wr [wt [sh [Hin [_ Hheap]]]]].
  simpl in Hin. destruct Hin as [Heq | Hfalse]; [subst sh|contradiction].
  set (rho := merge_valuation w.(world_variables) wr) in *.
  set (tau := merge_tag_valuation w.(world_tags) wt) in *.
  destruct (heap_formula_has_bound ds rho tau w.(world_heap)
    (subst_heap s (clause_body c)) Hheap) as [bound Hbounded].
  assert (Hrank : predicate_holds_rank ds (S bound) name
    (eval_terms rho (map (subst_term s) c.(clause_head))) w.(world_heap)).
  {
    simpl. exists c, s, rho. split; [exact Hclause|].
    split; [reflexivity|exact Hbounded].
  }
  exists wr, wt, (predicate_conclusion_heap name
    (map (subst_term s) c.(clause_head))).
  simpl. split; [now left|]. split; [exact I|].
  split; [exact I|].
  change (spatial_holds_with (formula_predicate_holds ds rho tau) rho
    [PredicateAtom (untagged_pred name
      (map (subst_term s) (clause_head c)))] (world_heap w)).
  simpl. exists w.(world_heap), []. split; [apply heap_join_empty_right|].
  split.
  - exists (S bound). split; [exact Hrank|exact I].
  - reflexivity.
Qed.

Definition predicate_intro_axiom ds name c s
    (Hclause : In c (lookup_definition name ds)) : Cyclic.axiom_instance :=
  {| Cyclic.axiom_name := "predicate-introduction";
     Cyclic.axiom_conclusion :=
       mk_judgment ds
         (mk_sequent (singleton_formula (subst_heap s c.(clause_body)))
           (singleton_formula
             (predicate_conclusion_heap name
               (map (subst_term s) c.(clause_head)))));
     Cyclic.axiom_theorem := predicate_intro_valid ds name c s Hclause |}.

(** Binary left-disjunction splitting. *)
Definition left_head_judgment ds q head : judgment :=
  mk_judgment ds
    (replace_antecedent q (replace_heaps q.(antecedent) [head])).

Definition left_tail_judgment ds q tail : judgment :=
  mk_judgment ds
    (replace_antecedent q (replace_heaps q.(antecedent) tail)).

Lemma left_split_theorem ds q head tail :
  Cyclic.premises_valid
    [{| Cyclic.premise_judgment := left_head_judgment ds q head;
        Cyclic.premise_edge := empty_edge |};
     {| Cyclic.premise_judgment := left_tail_judgment ds q tail;
        Cyclic.premise_edge := empty_edge |}] ->
  Cyclic.Valid
    (mk_judgment ds
      (replace_antecedent q (replace_heaps q.(antecedent) (head :: tail)))).
Proof.
  intros Hall w Hleft.
  destruct Hleft as [wr [wt [sh [Hin [Hcs Hheap]]]]].
  simpl in Hin. destruct Hin as [Heq | Hin].
  - subst sh.
    apply (Hall {| Cyclic.premise_judgment := left_head_judgment ds q head;
                  Cyclic.premise_edge := empty_edge |}); [now left|].
    exists wr, wt, head. simpl. auto.
  - apply (Hall {| Cyclic.premise_judgment := left_tail_judgment ds q tail;
                  Cyclic.premise_edge := empty_edge |}); [now right; left|].
    exists wr, wt, sh. simpl. auto.
Qed.

Lemma false_sequent_parts ds left right w :
  ~ sequent_holds ds (mk_sequent left right) w ->
  formula_holds ds w.(world_variables) w.(world_tags) w.(world_heap) left /\
  ~ formula_holds ds w.(world_variables) w.(world_tags) w.(world_heap) right.
Proof.
  unfold sequent_holds. intros H.
  split.
  - apply NNPP. intro Hnot. apply H. intro Hleft. contradiction.
  - intro Hright. apply H. intro Hleft. exact Hright.
Qed.

Lemma formula_cons_head
    (ds : definitions) (rho : valuation) (tau : tag_valuation)
    (concrete : concrete_heap) (constraints : list ordinal_constraint)
    (head : symheap) (tail : list symheap) :
  formula_holds ds rho tau concrete
    (mk_formula constraints (head :: tail)) ->
  formula_holds ds rho tau concrete (mk_formula constraints [head]) \/
  formula_holds ds rho tau concrete (mk_formula constraints tail).
Proof.
  intros [wr [wt [sh [Hin [Hcs Hheap]]]]].
  simpl in Hin. destruct Hin as [Heq | Hin].
  - subst sh. left. exists wr, wt, head. simpl. auto.
  - right. exists wr, wt, sh. simpl. auto.
Qed.

Lemma formula_cons_tail
    (ds : definitions) (rho : valuation) (tau : tag_valuation)
    (concrete : concrete_heap) (constraints : list ordinal_constraint)
    (head : symheap) (tail : list symheap) :
  ~ formula_holds ds rho tau concrete (mk_formula constraints [head]) ->
  formula_holds ds rho tau concrete
    (mk_formula constraints (head :: tail)) ->
  formula_holds ds rho tau concrete (mk_formula constraints tail).
Proof.
  intros Hnot Hwhole.
  destruct (formula_cons_head ds rho tau concrete constraints head tail Hwhole)
    as [Hhead | Htail]; [contradiction|exact Htail].
Qed.

Definition left_disjunction_rule
    (ds : definitions) (q : sequent) (head : symheap) (tail : list symheap)
    : Cyclic.rule_instance.
Proof.
  set (p1 :=
    {| Cyclic.premise_judgment := left_head_judgment ds q head;
       Cyclic.premise_edge := empty_edge |} : Cyclic.premise).
  set (p2 :=
    {| Cyclic.premise_judgment := left_tail_judgment ds q tail;
       Cyclic.premise_edge := empty_edge |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "left-disjunction";
       Cyclic.rule_conclusion := mk_judgment ds
         (replace_antecedent q (replace_heaps q.(antecedent) (head :: tail)));
       Cyclic.rule_premises := [p1; p2];
       Cyclic.rule_theorem := left_split_theorem ds q head tail;
       Cyclic.rule_counter_step := _ |}.
  intros w Hfalse.
  destruct (false_sequent_parts ds
    (replace_heaps q.(antecedent) (head :: tail)) q.(succedent) w Hfalse)
    as [Hleft Hright].
  destruct (excluded_middle_informative
    (formula_holds ds w.(world_variables) w.(world_tags) w.(world_heap)
      (replace_heaps q.(antecedent) [head]))) as [Hhead | Hhead].
  - exists 0, p1, w. simpl. split; [reflexivity|]. split.
    + intro Hprem. apply Hright. exact (Hprem Hhead).
    + apply empty_edge_respected.
  - assert (Htail : formula_holds ds w.(world_variables) w.(world_tags)
      w.(world_heap) (replace_heaps q.(antecedent) tail)).
    { eapply formula_cons_tail; eauto. }
    exists 1, p2, w. simpl. split; [reflexivity|]. split.
    + intro Hprem. apply Hright. exact (Hprem Htail).
    + apply empty_edge_respected.
Defined.

(** Choosing one right disjunct is a unary, sound rule. *)
Definition right_choice_judgment ds q head : judgment :=
  mk_judgment ds
    (replace_succedent q (replace_heaps q.(succedent) [head])).

Lemma right_choice_theorem ds q head tail :
  Cyclic.premises_valid
    [{| Cyclic.premise_judgment := right_choice_judgment ds q head;
        Cyclic.premise_edge := empty_edge |}] ->
  Cyclic.Valid
    (mk_judgment ds
      (replace_succedent q (replace_heaps q.(succedent) (head :: tail)))).
Proof.
  intros Hall w Hleft.
  specialize (Hall
    {| Cyclic.premise_judgment := right_choice_judgment ds q head;
       Cyclic.premise_edge := empty_edge |} (or_introl eq_refl) w Hleft).
  destruct Hall as [wr [wt [sh [Hin [Hcs Hheap]]]]].
  simpl in Hin. destruct Hin as [Heq | Hfalse]; [subst sh|contradiction].
  exists wr, wt, head. simpl. auto.
Qed.

Definition right_disjunction_rule
    (ds : definitions) (q : sequent) (head : symheap) (tail : list symheap)
    : Cyclic.rule_instance.
Proof.
  set (p :=
    {| Cyclic.premise_judgment := right_choice_judgment ds q head;
       Cyclic.premise_edge := empty_edge |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "right-disjunction";
       Cyclic.rule_conclusion := mk_judgment ds
         (replace_succedent q (replace_heaps q.(succedent) (head :: tail)));
       Cyclic.rule_premises := [p];
       Cyclic.rule_theorem := right_choice_theorem ds q head tail;
       Cyclic.rule_counter_step := _ |}.
  intros w Hfalse. exists 0, p, w. simpl. split; [reflexivity|]. split.
  - intro Hprem. apply Hfalse. intro Hleft.
    destruct (Hprem Hleft) as [wr [wt [sh [Hin [Hcs Hheap]]]]].
    simpl in Hin. destruct Hin as [Heq | Hbad]; [subst sh|contradiction].
    exists wr, wt, head. simpl. auto.
  - apply empty_edge_respected.
Defined.

(** Exact backlinks are ordinary identity steps.  Their trace relation is the
    identity on visible antecedent tags and contains no progress claim. *)
Definition identity_edge (j : judgment) : Cyclic.edge_info :=
  {| Cyclic.edge_valid := Cyclic.identity_pairs (judgment_tags j);
     Cyclic.edge_progress := [] |}.

Lemma identity_edge_respected j w :
  Cyclic.respects_edge j j w w (identity_edge j).
Proof.
  split.
  - intros a b Hin. unfold identity_edge, Cyclic.identity_pairs in Hin.
    apply in_map_iff in Hin. destruct Hin as [t [Heq _]].
    inversion Heq; subst. lia.
  - intros a b Hin. inversion Hin.
Qed.

Definition exact_backlink_rule (j : judgment) : Cyclic.rule_instance.
Proof.
  set (p :=
    {| Cyclic.premise_judgment := j;
       Cyclic.premise_edge := identity_edge j |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "exact-backlink";
       Cyclic.rule_conclusion := j;
       Cyclic.rule_premises := [p];
       Cyclic.rule_theorem := _;
       Cyclic.rule_counter_step := _ |}.
  - intros Hvalid w. apply (Hvalid p); now left.
  - intros w Hfalse. exists 0, p, w. simpl. split; [reflexivity|].
    split; [exact Hfalse|apply identity_edge_respected].
Defined.

(** A progressing loop over an already valid tagged judgment is useful as a
    compact teaching certificate.  The strict countermodel obligation is
    discharged because a valid judgment has no countermodel; no axiom or
    admitted fact is involved. *)
Definition progressing_edge tag : Cyclic.edge_info :=
  {| Cyclic.edge_valid := [(tag, tag)];
     Cyclic.edge_progress := [(tag, tag)] |}.

Definition progressing_valid_rule (j : judgment) (tag : nat)
    (Hvalid : Cyclic.Valid j) : Cyclic.rule_instance.
Proof.
  set (p :=
    {| Cyclic.premise_judgment := j;
       Cyclic.premise_edge := progressing_edge tag |} : Cyclic.premise).
  refine
    {| Cyclic.rule_name := "progressing-valid-loop";
       Cyclic.rule_conclusion := j;
       Cyclic.rule_premises := [p];
       Cyclic.rule_theorem := fun _ => Hvalid;
       Cyclic.rule_counter_step := _ |}.
  intros w Hfalse. exfalso. exact (Hfalse (Hvalid w)).
Defined.
