From Stdlib Require Import List Bool Arith Lia String Classical_Prop Wf_nat.

From CyclistRocq.Cyclic Require Import Framework.
From CyclistRocq.FirstOrder Require Import Syntax.

Import ListNotations.
Open Scope string_scope.

(** The first-order domain is the free constructor algebra. *)
Inductive value : Type :=
| VConst (n : nat)
| VFun (name : string) (args : list value).

Fixpoint value_eq_dec (x y : value) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply list_eq_dec. exact value_eq_dec.
  - apply string_dec.
Defined.

Definition value_eqb (x y : value) : bool :=
  if value_eq_dec x y then true else false.

Definition valuation : Type := variable -> value.

Fixpoint eval_term (rho : valuation) (t : term) : value :=
  match t with
  | Const n => VConst n
  | Var x => rho x
  | Fun f xs => VFun f (map (eval_term rho) xs)
  end.

Definition eval_terms (rho : valuation) (xs : list term) : list value :=
  map (eval_term rho) xs.

(** A ranked interpretation records membership and a finite derivation height
    simultaneously.  [models] below requires introduction closure and a
    strictly smaller derivation for every inductive premise selected by an
    inversion. *)
Record interpretation : Type := {
  predicate_rank : string -> list value -> option nat
}.

Definition predicate_holds
    (i : interpretation) (name : string) (args : list value) : Prop :=
  exists height, i.(predicate_rank) name args = Some height.

Definition atom_holds
    (i : interpretation) (rho : valuation) (a : atom) : Prop :=
  match a with
  | Eq x y => eval_term rho x = eval_term rho y
  | Neq x y => eval_term rho x <> eval_term rho y
  | Pred _ name args => predicate_holds i name (eval_terms rho args)
  end.

Fixpoint product_holds
    (i : interpretation) (rho : valuation) (p : product) : Prop :=
  match p with
  | [] => True
  | a :: p' => atom_holds i rho a /\ product_holds i rho p'
  end.

Definition formula_holds
    (i : interpretation) (rho : valuation) (f : formula) : Prop :=
  exists p, In p f /\ product_holds i rho p.

Definition merge_valuation (base witness : valuation) : valuation :=
  fun x =>
    match x.(variable_kind) with
    | Free => base x
    | Existential => witness x
    end.

Definition right_holds
    (i : interpretation) (rho : valuation) (f : formula) : Prop :=
  exists witness, formula_holds i (merge_valuation rho witness) f.

Definition body_decreases
    (i : interpretation) (rho : valuation) (p : product) (height : nat) : Prop :=
  forall tag name args,
    In (Pred tag name args) p ->
    exists child_height,
      i.(predicate_rank) name (eval_terms rho args) = Some child_height /\
      child_height < height.

Definition models (ds : definitions) (i : interpretation) : Prop :=
  (forall name c rho,
      In c (lookup_definition name ds) ->
      product_holds i rho c.(clause_body) ->
      predicate_holds i name (eval_terms rho c.(clause_head))) /\
  (forall name args height,
      i.(predicate_rank) name args = Some height ->
      exists c rho,
        In c (lookup_definition name ds) /\
        eval_terms rho c.(clause_head) = args /\
        product_holds i rho c.(clause_body) /\
        body_decreases i rho c.(clause_body) height).

Definition world : Type := (interpretation * valuation)%type.

Definition sequent_holds (ds : definitions) (q : sequent) (w : world) : Prop :=
  let '(i, rho) := w in
  models ds i ->
  formula_holds i rho q.(antecedent) ->
  right_holds i rho q.(succedent).

Definition denote (j : judgment) (w : world) : Prop :=
  sequent_holds j.(judgment_definitions) j.(judgment_sequent) w.

Definition rank_atom
    (i : interpretation) (rho : valuation) (tag : nat) (a : atom) : option nat :=
  match a with
  | Pred (Some t) name args =>
      if Nat.eqb tag t then
        match i.(predicate_rank) name (eval_terms rho args) with
        | Some height => Some (S height)
        | None => Some 0
        end
      else None
  | _ => None
  end.

Fixpoint rank_product
    (i : interpretation) (rho : valuation) (tag : nat) (p : product) : option nat :=
  match p with
  | [] => None
  | a :: p' =>
      match rank_atom i rho tag a with
      | Some n => Some n
      | None => rank_product i rho tag p'
      end
  end.

Fixpoint rank_formula
    (i : interpretation) (rho : valuation) (tag : nat) (f : formula) : nat :=
  match f with
  | [] => 0
  | p :: f' =>
      match rank_product i rho tag p with
      | Some n => n
      | None => rank_formula i rho tag f'
      end
  end.

Definition rank_of_tag (j : judgment) (w : world) (tag : nat) : nat :=
  rank_formula (fst w) (snd w) tag j.(judgment_sequent).(antecedent).

Module FirstOrderTheory <: Framework.THEORY.
  Definition World := world.
  Definition Judgment := judgment.
  Definition Sequent := World -> Prop.
  Definition judgment_eqb := judgment_eqb.
  Definition backlink_eqb := backlink_eqb.
  Definition denote := denote.
  Definition tags := judgment_tags.
  Definition rank := rank_of_tag.
End FirstOrderTheory.

Module Cyclic := Framework.Make FirstOrderTheory.

Fixpoint term_size (t : term) : nat :=
  match t with
  | Const _ | Var _ => 1
  | Fun _ xs => S (fold_right (fun x n => term_size x + n) 0 xs)
  end.

Lemma term_size_member x xs :
  In x xs ->
  term_size x <= fold_right (fun t n => term_size t + n) 0 xs.
Proof.
  induction xs as [|y ys IH]; simpl; [tauto|].
  intros [-> | Hin]; [lia|]. specialize (IH Hin). lia.
Qed.

Lemma term_nested_ind (P : term -> Prop) :
  (forall n, P (Const n)) ->
  (forall x, P (Var x)) ->
  (forall name args, Forall P args -> P (Fun name args)) ->
  forall t, P t.
Proof.
  intros Hconst Hvar Hfun.
  apply (well_founded_induction_type (well_founded_ltof term term_size)).
  intros t IH. destruct t as [n|x|name args].
  - apply Hconst.
  - apply Hvar.
  - apply Hfun. apply Forall_forall. intros x Hin. apply IH.
    unfold ltof. simpl. pose proof (term_size_member x args Hin). lia.
Qed.

Fixpoint term_freeb (t : term) : bool :=
  match t with
  | Const _ => true
  | Var x =>
      match x.(variable_kind) with Free => true | Existential => false end
  | Fun _ xs => forallb term_freeb xs
  end.

Definition atom_freeb (a : atom) : bool :=
  match a with
  | Eq x y | Neq x y => term_freeb x && term_freeb y
  | Pred _ _ xs => forallb term_freeb xs
  end.

Definition product_freeb (p : product) : bool := forallb atom_freeb p.
Definition formula_freeb (f : formula) : bool := forallb product_freeb f.

Lemma eval_term_merge_free base witness t :
  term_freeb t = true ->
  eval_term (merge_valuation base witness) t = eval_term base t.
Proof.
  revert base witness. induction t using term_nested_ind; intros base witness Hfree;
    simpl in *; auto.
  - destruct x as [[|] id]; simpl in Hfree |- *; [reflexivity|discriminate].
  - f_equal. apply map_ext_in. intros t Hin.
    pose proof (proj1 (Forall_forall _ args) H t Hin) as IHt.
    apply IHt.
    apply (proj1 (forallb_forall term_freeb args) Hfree t Hin).
Qed.

Lemma eval_terms_merge_free base witness xs :
  forallb term_freeb xs = true ->
  eval_terms (merge_valuation base witness) xs = eval_terms base xs.
Proof.
  intro H. unfold eval_terms. apply map_ext_in.
  intros t Hin. apply eval_term_merge_free.
  apply (proj1 (forallb_forall term_freeb xs) H t Hin).
Qed.

Lemma atom_holds_merge_free i base witness a :
  atom_freeb a = true ->
  (atom_holds i (merge_valuation base witness) a <-> atom_holds i base a).
Proof.
  destruct a; simpl; intro H.
  - apply Bool.andb_true_iff in H as [Hx Hy].
    now rewrite (eval_term_merge_free base witness left Hx),
      (eval_term_merge_free base witness right Hy).
  - apply Bool.andb_true_iff in H as [Hx Hy].
    now rewrite (eval_term_merge_free base witness left Hx),
      (eval_term_merge_free base witness right Hy).
  - now rewrite (eval_terms_merge_free base witness args H).
Qed.

Lemma product_holds_merge_free i base witness p :
  product_freeb p = true ->
  (product_holds i (merge_valuation base witness) p <->
   product_holds i base p).
Proof.
  unfold product_freeb. rewrite forallb_forall. intro Hfree.
  induction p as [|a p IH]; simpl; [tauto|].
  rewrite atom_holds_merge_free by (apply Hfree; now left).
  rewrite IH.
  - tauto.
  - intros x Hx. apply Hfree. now right.
Qed.

Lemma formula_holds_merge_free i base witness f :
  formula_freeb f = true ->
  (formula_holds i (merge_valuation base witness) f <->
   formula_holds i base f).
Proof.
  unfold formula_freeb. rewrite forallb_forall. intros Hfree.
  split.
  - intros [p [Hin Hp]]. exists p. split; [exact Hin|].
    apply (proj1 (product_holds_merge_free i base witness p (Hfree p Hin))).
    exact Hp.
  - intros [p [Hin Hp]]. exists p. split; [exact Hin|].
    apply (proj2 (product_holds_merge_free i base witness p (Hfree p Hin))).
    exact Hp.
Qed.

Lemma right_holds_free i rho f :
  formula_freeb f = true ->
  (right_holds i rho f <-> formula_holds i rho f).
Proof.
  intro Hfree. split.
  - intros [witness H].
    apply (proj1 (formula_holds_merge_free i rho witness f Hfree)). exact H.
  - intro H. exists rho.
    apply (proj2 (formula_holds_merge_free i rho rho f Hfree)). exact H.
Qed.

Definition combine_valuation
    (offset : nat) (old clause_env : valuation) : valuation :=
  fun x =>
    if Nat.ltb x.(variable_id) offset then old x
    else clause_env
      {| variable_kind := x.(variable_kind);
         variable_id := x.(variable_id) - offset |}.

Definition existential_clause_valuation
    (offset : nat) (base witness : valuation) : valuation :=
  fun x => witness (existential_shift_variable offset x).

Lemma eval_existential_shift_term offset base witness t :
  eval_term (merge_valuation base witness) (existential_shift_term offset t) =
  eval_term (existential_clause_valuation offset base witness) t.
Proof.
  induction t using term_nested_ind; simpl; auto.
  f_equal. rewrite map_map. apply map_ext_in. intros t Hin.
    pose proof (proj1 (Forall_forall _ args) H t Hin) as IHt.
    exact IHt.
Qed.

Lemma eval_existential_shift_terms offset base witness xs :
  eval_terms (merge_valuation base witness)
    (map (existential_shift_term offset) xs) =
  eval_terms (existential_clause_valuation offset base witness) xs.
Proof.
  unfold eval_terms. rewrite map_map. apply map_ext_in.
  intros t _. apply eval_existential_shift_term.
Qed.

Lemma atom_holds_existential_shift offset i base witness a :
  atom_holds i (merge_valuation base witness)
    (existential_shift_atom offset a) <->
  atom_holds i (existential_clause_valuation offset base witness) a.
Proof.
  destruct a; simpl.
  - now rewrite !eval_existential_shift_term.
  - now rewrite !eval_existential_shift_term.
  - now rewrite eval_existential_shift_terms.
Qed.

Lemma product_holds_existential_shift offset i base witness p :
  product_holds i (merge_valuation base witness)
    (existential_shift_product offset p) <->
  product_holds i (existential_clause_valuation offset base witness) p.
Proof.
  induction p as [|a p IH]; simpl; [tauto|].
  rewrite atom_holds_existential_shift, IH. tauto.
Qed.

Lemma eval_shift_term offset old clause_env t :
  eval_term (combine_valuation offset old clause_env) (shift_term offset t) =
  eval_term clause_env t.
Proof.
  induction t using term_nested_ind; simpl; auto.
  - destruct x as [kind id]. unfold combine_valuation, shift_variable; simpl.
    destruct (Nat.ltb (offset + id) offset) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt. lia.
    + replace (offset + id - offset) with id by lia. reflexivity.
  - f_equal. rewrite map_map. apply map_ext_in. intros t Hin.
    pose proof (proj1 (Forall_forall _ args) H t Hin) as IHt.
    exact IHt.
Qed.

Lemma eval_shift_terms offset old clause_env xs :
  eval_terms (combine_valuation offset old clause_env)
    (map (shift_term offset) xs) =
  eval_terms clause_env xs.
Proof.
  unfold eval_terms. rewrite map_map. apply map_ext_in.
  intros t _. apply eval_shift_term.
Qed.

Lemma eval_old_term offset old clause_env t :
  term_belowb offset t = true ->
  eval_term (combine_valuation offset old clause_env) t = eval_term old t.
Proof.
  revert old clause_env. induction t using term_nested_ind;
    intros old clause_env Hbelow; simpl in *; auto.
  - unfold combine_valuation. rewrite Hbelow. reflexivity.
  - f_equal. apply map_ext_in. intros t Hin.
    pose proof (proj1 (Forall_forall _ args) H t Hin) as IHt.
    apply IHt. apply (proj1 (forallb_forall (term_belowb offset) args)
      Hbelow t Hin).
Qed.

Lemma eval_old_terms offset old clause_env xs :
  forallb (term_belowb offset) xs = true ->
  eval_terms (combine_valuation offset old clause_env) xs = eval_terms old xs.
Proof.
  intro H. unfold eval_terms. apply map_ext_in. intros t Hin.
  apply eval_old_term. apply (proj1
    (forallb_forall (term_belowb offset) xs) H t Hin).
Qed.

Lemma atom_holds_shift offset i old clause_env a :
  atom_holds i (combine_valuation offset old clause_env) (shift_atom offset a)
  <-> atom_holds i clause_env a.
Proof.
  destruct a; simpl.
  - now rewrite !eval_shift_term.
  - now rewrite !eval_shift_term.
  - now rewrite eval_shift_terms.
Qed.

Lemma product_holds_shift offset i old clause_env p :
  product_holds i (combine_valuation offset old clause_env)
    (shift_product offset p) <->
  product_holds i clause_env p.
Proof.
  induction p as [|a p IH]; simpl; [tauto|].
  rewrite atom_holds_shift, IH. tauto.
Qed.

Lemma atom_holds_old offset i old clause_env a :
  atom_belowb offset a = true ->
  (atom_holds i (combine_valuation offset old clause_env) a <->
   atom_holds i old a).
Proof.
  destruct a; simpl; intro H.
  - apply Bool.andb_true_iff in H as [Hx Hy].
    now rewrite (eval_old_term offset old clause_env left Hx),
      (eval_old_term offset old clause_env right Hy).
  - apply Bool.andb_true_iff in H as [Hx Hy].
    now rewrite (eval_old_term offset old clause_env left Hx),
      (eval_old_term offset old clause_env right Hy).
  - now rewrite (eval_old_terms offset old clause_env args H).
Qed.

Lemma product_holds_old offset i old clause_env p :
  product_belowb offset p = true ->
  (product_holds i (combine_valuation offset old clause_env) p <->
   product_holds i old p).
Proof.
  unfold product_belowb. rewrite forallb_forall. intro Hbelow.
  induction p as [|a p IH]; simpl; [tauto|].
  rewrite atom_holds_old by (apply Hbelow; now left).
  rewrite IH.
  - tauto.
  - intros x Hx. apply Hbelow. now right.
Qed.

Lemma formula_holds_old offset i old clause_env f :
  formula_belowb offset f = true ->
  (formula_holds i (combine_valuation offset old clause_env) f <->
   formula_holds i old f).
Proof.
  unfold formula_belowb. rewrite forallb_forall. intro Hbelow.
  split.
  - intros [p [Hin Hp]]. exists p. split; [exact Hin|].
    apply (proj1 (product_holds_old offset i old clause_env p
      (Hbelow p Hin))). exact Hp.
  - intros [p [Hin Hp]]. exists p. split; [exact Hin|].
    apply (proj2 (product_holds_old offset i old clause_env p
      (Hbelow p Hin))). exact Hp.
Qed.

Lemma atom_holds_set_tag i rho tag a :
  atom_holds i rho (set_atom_tag tag a) <-> atom_holds i rho a.
Proof. destruct a; simpl; tauto. Qed.

Lemma product_holds_retag i rho tag p :
  product_holds i rho (retag_product tag p) <-> product_holds i rho p.
Proof.
  induction p as [|a p IH]; simpl; [tauto|].
  rewrite atom_holds_set_tag, IH. tauto.
Qed.

Lemma product_holds_app i rho (p q : product) :
  product_holds i rho (p ++ q)%list <->
  product_holds i rho p /\ product_holds i rho q.
Proof.
  induction p as [|a p IH]; simpl; [tauto|]. rewrite IH. tauto.
Qed.

Lemma equation_product_holds rho (xs ys : list term) :
  List.length xs = List.length ys ->
  eval_terms rho xs = eval_terms rho ys ->
  product_holds {| predicate_rank := fun _ _ => None |} rho
    (equation_product xs ys).
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen Heval;
    simpl in *; try discriminate; auto.
  injection Heval as Hxy Htail. split; [exact Hxy|].
  apply IH; [lia|exact Htail].
Qed.

Lemma equation_product_holds_any i rho (xs ys : list term) :
  List.length xs = List.length ys ->
  eval_terms rho xs = eval_terms rho ys ->
  product_holds i rho (equation_product xs ys).
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen Heval;
    simpl in *; try discriminate; auto.
  injection Heval as Hxy Htail. split; [exact Hxy|].
  apply IH; [lia|exact Htail].
Qed.

Lemma equation_product_holds_inv i rho (xs ys : list term) :
  List.length xs = List.length ys ->
  product_holds i rho (equation_product xs ys) ->
  eval_terms rho xs = eval_terms rho ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen Hholds;
    simpl in *; try discriminate; auto.
  destruct Hholds as [Hxy Htail]. f_equal; [exact Hxy|].
  apply IH; [lia|exact Htail].
Qed.

Lemma rank_product_app_some i rho tag (p q : product) n :
  rank_product i rho tag p = Some n ->
  rank_product i rho tag (p ++ q)%list = Some n.
Proof.
  revert n. induction p as [|a p IH]; simpl; intros n H; [discriminate|].
  destruct (rank_atom i rho tag a); [exact H|]. apply IH. exact H.
Qed.

Lemma rank_retag_body_progress i rho p tag height :
  body_decreases i rho p height ->
  product_has_pred p = true ->
  exists child_height,
    rank_product i rho tag (retag_product tag p) = Some (S child_height) /\
    child_height < height.
Proof.
  intros Hdec. induction p as [|a p IH]; simpl; [discriminate|].
  destruct a as [x y|x y|oldtag name args]; simpl.
  - apply IH. intros t n xs Hin. apply (Hdec t n xs). now right.
  - apply IH. intros t n xs Hin. apply (Hdec t n xs). now right.
  - intro Hhas. assert (Hin : In (Pred oldtag name args) (Pred oldtag name args :: p))
      by now left.
    destruct (Hdec oldtag name args Hin) as [child [Hrank Hlt]].
    exists child. rewrite Nat.eqb_refl, Hrank. auto.
Qed.

Lemma rank_product_app_none i rho tag (p q : product) :
  rank_product i rho tag p = None ->
  rank_product i rho tag (p ++ q)%list = rank_product i rho tag q.
Proof.
  induction p as [|a p IH]; simpl; intro H; auto.
  destruct (rank_atom i rho tag a) eqn:Ha; [discriminate|].
  apply IH. exact H.
Qed.

Lemma rank_retag_other_none i rho p source_tag other_tag :
  source_tag <> other_tag ->
  rank_product i rho other_tag (retag_product source_tag p) = None.
Proof.
  intro Hneq. induction p as [|a p IH]; simpl; auto.
  destruct a as [x y|x y|t name args]; simpl; auto.
  destruct (Nat.eqb other_tag source_tag) eqn:Heq; auto.
  apply Nat.eqb_eq in Heq. exfalso. apply Hneq. now symmetry.
Qed.

Lemma rank_head_pred i rho tag name args (context : product) height :
  i.(predicate_rank) name (eval_terms rho args) = Some height ->
  rank_formula i rho tag [Pred (Some tag) name args :: context] = S height.
Proof. intro H. simpl. now rewrite Nat.eqb_refl, H. Qed.

Lemma rank_unfold_contraction i rho source_tag fresh_tag body name args tail height :
  source_tag <> fresh_tag ->
  i.(predicate_rank) name (eval_terms rho args) = Some height ->
  rank_product i rho fresh_tag
    (retag_product source_tag body ++
      Pred (Some fresh_tag) name args :: tail)%list = Some (S height).
Proof.
  intros Hneq Hrank.
  rewrite rank_product_app_none.
  - simpl. rewrite Nat.eqb_refl, Hrank. reflexivity.
  - apply rank_retag_other_none. exact Hneq.
Qed.

Lemma rank_shift_retag_body_progress
    i old clause_env offset p tag height :
  body_decreases i clause_env p height ->
  product_has_pred p = true ->
  exists child_height,
    rank_product i (combine_valuation offset old clause_env) tag
      (retag_product tag (shift_product offset p)) = Some (S child_height) /\
    child_height < height.
Proof.
  intros Hdec. induction p as [|a p IH]; simpl; [discriminate|].
  destruct a as [x y|x y|oldtag name args]; simpl.
  - apply IH. intros t n xs Hin. apply (Hdec t n xs). now right.
  - apply IH. intros t n xs Hin. apply (Hdec t n xs). now right.
  - intro Hhas.
    assert (Hin : In (Pred oldtag name args) (Pred oldtag name args :: p))
      by now left.
    destruct (Hdec oldtag name args Hin) as [child [Hrank Hlt]].
    exists child. rewrite Nat.eqb_refl, eval_shift_terms, Hrank. auto.
Qed.
