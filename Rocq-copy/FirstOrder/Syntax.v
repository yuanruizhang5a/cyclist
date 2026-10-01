From Stdlib Require Import List Bool Arith String.

Import ListNotations.
Open Scope string_scope.

(** Variables are split into the two classes used by Cyclist's first-order
    frontend.  The executable prover currently keeps the distinction even
    though the benchmark fragment only contains free variables. *)
Inductive var_kind : Type := Free | Existential.

Record variable : Type := {
  variable_kind : var_kind;
  variable_id : nat
}.

Definition free_var (x : nat) : variable :=
  {| variable_kind := Free; variable_id := x |}.

Definition existential_var (x : nat) : variable :=
  {| variable_kind := Existential; variable_id := x |}.

Definition var_kind_eqb (x y : var_kind) : bool :=
  match x, y with
  | Free, Free | Existential, Existential => true
  | _, _ => false
  end.

Definition variable_eqb (x y : variable) : bool :=
  var_kind_eqb x.(variable_kind) y.(variable_kind) &&
  Nat.eqb x.(variable_id) y.(variable_id).

Inductive term : Type :=
| Const (n : nat)
| Var (x : variable)
| Fun (name : string) (args : list term).

Definition variable_eq_dec : forall x y : variable, {x = y} + {x <> y}.
Proof. decide equality; [apply Nat.eq_dec | decide equality]. Defined.

Fixpoint term_eq_dec (x y : term) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply variable_eq_dec.
  - apply list_eq_dec. exact term_eq_dec.
  - apply string_dec.
Defined.

Definition term_eqb (x y : term) : bool :=
  if term_eq_dec x y then true else false.

Fixpoint terms_eqb (xs ys : list term) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => term_eqb x y && terms_eqb xs' ys'
  | _, _ => false
  end.

Definition zero : term := Const 0.
Definition succ (t : term) : term := Fun "s" [t].
Definition cons (head tail : term) : term := Fun "cons" [head; tail].

Inductive atom : Type :=
| Eq (left right : term)
| Neq (left right : term)
| Pred (tag : option nat) (name : string) (args : list term).

Definition option_nat_eqb (x y : option nat) : bool :=
  match x, y with
  | None, None => true
  | Some n, Some m => Nat.eqb n m
  | _, _ => false
  end.

Definition atom_eqb (x y : atom) : bool :=
  match x, y with
  | Eq a b, Eq c d | Neq a b, Neq c d =>
      term_eqb a c && term_eqb b d
  | Pred t p xs, Pred u q ys =>
      option_nat_eqb t u && String.eqb p q && terms_eqb xs ys
  | _, _ => false
  end.

Definition atom_eqb_upto_tags (x y : atom) : bool :=
  match x, y with
  | Eq a b, Eq c d | Neq a b, Neq c d =>
      term_eqb a c && term_eqb b d
  | Pred _ p xs, Pred _ q ys => String.eqb p q && terms_eqb xs ys
  | _, _ => false
  end.

Definition product : Type := list atom.
Definition formula : Type := list product.

Record sequent : Type := {
  antecedent : formula;
  succedent : formula
}.

Record clause : Type := {
  clause_body : product;
  clause_head : list term
}.

(** Association lists deliberately preserve the ordering of definitions and
    clauses, just as the OCaml implementation does. *)
Definition definitions : Type := list (string * list clause).

Record judgment : Type := {
  judgment_definitions : definitions;
  judgment_sequent : sequent
}.

Fixpoint atoms_eqb (xs ys : list atom) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => atom_eqb x y && atoms_eqb xs' ys'
  | _, _ => false
  end.

Fixpoint atoms_eqb_upto_tags (xs ys : list atom) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      atom_eqb_upto_tags x y && atoms_eqb_upto_tags xs' ys'
  | _, _ => false
  end.

Fixpoint formula_eqb (xs ys : formula) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => atoms_eqb x y && formula_eqb xs' ys'
  | _, _ => false
  end.

Fixpoint formula_eqb_upto_tags (xs ys : formula) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      atoms_eqb_upto_tags x y && formula_eqb_upto_tags xs' ys'
  | _, _ => false
  end.

Definition sequent_eqb (x y : sequent) : bool :=
  formula_eqb x.(antecedent) y.(antecedent) &&
  formula_eqb x.(succedent) y.(succedent).

Definition sequent_eqb_upto_tags (x y : sequent) : bool :=
  formula_eqb_upto_tags x.(antecedent) y.(antecedent) &&
  formula_eqb_upto_tags x.(succedent) y.(succedent).

Definition clause_eqb (x y : clause) : bool :=
  atoms_eqb x.(clause_body) y.(clause_body) &&
  terms_eqb x.(clause_head) y.(clause_head).

Fixpoint clauses_eqb (xs ys : list clause) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => clause_eqb x y && clauses_eqb xs' ys'
  | _, _ => false
  end.

Fixpoint definitions_eqb (xs ys : definitions) : bool :=
  match xs, ys with
  | [], [] => true
  | (p, cs) :: xs', (q, ds) :: ys' =>
      String.eqb p q && clauses_eqb cs ds && definitions_eqb xs' ys'
  | _, _ => false
  end.

Definition judgment_eqb (x y : judgment) : bool :=
  definitions_eqb x.(judgment_definitions) y.(judgment_definitions) &&
  sequent_eqb x.(judgment_sequent) y.(judgment_sequent).

Definition backlink_eqb (x y : judgment) : bool :=
  definitions_eqb x.(judgment_definitions) y.(judgment_definitions) &&
  sequent_eqb_upto_tags x.(judgment_sequent) y.(judgment_sequent).

Definition substitution : Type := list (variable * term).

Fixpoint lookup_substitution (s : substitution) (x : variable) : option term :=
  match s with
  | [] => None
  | (y, t) :: s' =>
      if variable_eqb x y then Some t else lookup_substitution s' x
  end.

Fixpoint subst_term (s : substitution) (t : term) : term :=
  match t with
  | Const n => Const n
  | Var x =>
      match lookup_substitution s x with
      | Some u => u
      | None => Var x
      end
  | Fun f xs => Fun f (map (subst_term s) xs)
  end.

Definition subst_atom (s : substitution) (a : atom) : atom :=
  match a with
  | Eq x y => Eq (subst_term s x) (subst_term s y)
  | Neq x y => Neq (subst_term s x) (subst_term s y)
  | Pred t p xs => Pred t p (map (subst_term s) xs)
  end.

Definition subst_product (s : substitution) (p : product) : product :=
  map (subst_atom s) p.

Definition subst_formula (s : substitution) (f : formula) : formula :=
  map (subst_product s) f.

Definition subst_sequent (s : substitution) (q : sequent) : sequent :=
  {| antecedent := subst_formula s q.(antecedent);
     succedent := subst_formula s q.(succedent) |}.

Definition shift_variable (offset : nat) (x : variable) : variable :=
  {| variable_kind := x.(variable_kind);
     variable_id := offset + x.(variable_id) |}.

Fixpoint shift_term (offset : nat) (t : term) : term :=
  match t with
  | Const n => Const n
  | Var x => Var (shift_variable offset x)
  | Fun f xs => Fun f (map (shift_term offset) xs)
  end.

Definition shift_atom (offset : nat) (a : atom) : atom :=
  match a with
  | Eq x y => Eq (shift_term offset x) (shift_term offset y)
  | Neq x y => Neq (shift_term offset x) (shift_term offset y)
  | Pred t p xs => Pred t p (map (shift_term offset) xs)
  end.

Definition shift_product (offset : nat) (p : product) : product :=
  map (shift_atom offset) p.

Definition shift_clause (offset : nat) (c : clause) : clause :=
  {| clause_body := shift_product offset c.(clause_body);
     clause_head := map (shift_term offset) c.(clause_head) |}.

(** Fresh variables introduced by a right unfolding are witnesses rather than
    parameters.  They therefore become existential variables irrespective of
    how the definition file names them. *)
Definition existential_shift_variable (offset : nat) (x : variable) : variable :=
  {| variable_kind := Existential;
     variable_id := offset + x.(variable_id) |}.

Fixpoint existential_shift_term (offset : nat) (t : term) : term :=
  match t with
  | Const n => Const n
  | Var x => Var (existential_shift_variable offset x)
  | Fun f xs => Fun f (map (existential_shift_term offset) xs)
  end.

Definition existential_shift_atom (offset : nat) (a : atom) : atom :=
  match a with
  | Eq x y => Eq (existential_shift_term offset x)
                    (existential_shift_term offset y)
  | Neq x y => Neq (existential_shift_term offset x)
                      (existential_shift_term offset y)
  | Pred t p xs => Pred t p (map (existential_shift_term offset) xs)
  end.

Definition existential_shift_product (offset : nat) (p : product) : product :=
  map (existential_shift_atom offset) p.

Fixpoint term_belowb (bound : nat) (t : term) : bool :=
  match t with
  | Const _ => true
  | Var x => Nat.ltb x.(variable_id) bound
  | Fun _ xs => forallb (term_belowb bound) xs
  end.

Definition atom_belowb (bound : nat) (a : atom) : bool :=
  match a with
  | Eq x y | Neq x y => term_belowb bound x && term_belowb bound y
  | Pred _ _ xs => forallb (term_belowb bound) xs
  end.

Definition product_belowb (bound : nat) (p : product) : bool :=
  forallb (atom_belowb bound) p.

Definition formula_belowb (bound : nat) (f : formula) : bool :=
  forallb (product_belowb bound) f.

Definition sequent_belowb (bound : nat) (q : sequent) : bool :=
  formula_belowb bound q.(antecedent) && formula_belowb bound q.(succedent).

Fixpoint term_max_var (t : term) : nat :=
  match t with
  | Const _ => 0
  | Var x => S x.(variable_id)
  | Fun _ xs => fold_right Nat.max 0 (map term_max_var xs)
  end.

Definition atom_max_var (a : atom) : nat :=
  match a with
  | Eq x y | Neq x y => Nat.max (term_max_var x) (term_max_var y)
  | Pred _ _ xs => fold_right Nat.max 0 (map term_max_var xs)
  end.

Definition product_max_var (p : product) : nat :=
  fold_right Nat.max 0 (map atom_max_var p).

Definition formula_max_var (f : formula) : nat :=
  fold_right Nat.max 0 (map product_max_var f).

Definition sequent_max_var (q : sequent) : nat :=
  Nat.max (formula_max_var q.(antecedent)) (formula_max_var q.(succedent)).

Definition fresh_variable_offset (q : sequent) : nat :=
  sequent_max_var q.

Definition atom_tag (a : atom) : option nat :=
  match a with
  | Pred t _ _ => t
  | _ => None
  end.

Definition set_atom_tag (t : option nat) (a : atom) : atom :=
  match a with
  | Pred _ p xs => Pred t p xs
  | _ => a
  end.

Definition retag_product (t : nat) (p : product) : product :=
  map (set_atom_tag (Some t)) p.

Fixpoint product_has_pred (p : product) : bool :=
  match p with
  | [] => false
  | Pred _ _ _ :: _ => true
  | _ :: p' => product_has_pred p'
  end.

Fixpoint equation_product (xs ys : list term) : product :=
  match xs, ys with
  | x :: xs', y :: ys' => Eq x y :: equation_product xs' ys'
  | _, _ => []
  end.

Fixpoint product_tags (p : product) : list nat :=
  match p with
  | [] => []
  | a :: p' =>
      match atom_tag a with
      | Some t => t :: product_tags p'
      | None => product_tags p'
      end
  end.

Fixpoint formula_tags (f : formula) : list nat :=
  match f with
  | [] => []
  | p :: f' => product_tags p ++ formula_tags f'
  end.

Definition sequent_tags (q : sequent) : list nat :=
  nodup Nat.eq_dec (formula_tags q.(antecedent)).

Definition judgment_tags (j : judgment) : list nat :=
  sequent_tags j.(judgment_sequent).

Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (max_list xs')
  end.

Definition fresh_tag (q : sequent) : nat := S (max_list (sequent_tags q)).

Fixpoint tag_product_from (next : nat) (p : product) : product * nat :=
  match p with
  | [] => ([], next)
  | a :: p' =>
      match a with
      | Pred _ name args =>
          let '(p'', next') := tag_product_from (S next) p' in
          (Pred (Some next) name args :: p'', next')
      | _ =>
          let '(p'', next') := tag_product_from next p' in
          (a :: p'', next')
      end
  end.

Fixpoint tag_formula_from (next : nat) (f : formula) : formula * nat :=
  match f with
  | [] => ([], next)
  | p :: f' =>
      let '(p', next') := tag_product_from next p in
      let '(f'', next'') := tag_formula_from next' f' in
      (p' :: f'', next'')
  end.

Definition prepare_sequent (q : sequent) : sequent :=
  let '(lhs, _) := tag_formula_from 0 q.(antecedent) in
  {| antecedent := lhs; succedent := q.(succedent) |}.

Fixpoint lookup_definition (name : string) (ds : definitions)
  : list clause :=
  match ds with
  | [] => []
  | (p, cs) :: ds' =>
      if String.eqb name p then cs else lookup_definition name ds'
  end.

Definition mk_sequent (lhs rhs : formula) : sequent :=
  {| antecedent := lhs; succedent := rhs |}.

Definition mk_judgment (ds : definitions) (q : sequent) : judgment :=
  {| judgment_definitions := ds; judgment_sequent := q |}.

Definition pred (name : string) (args : list term) : atom :=
  Pred None name args.

Definition tagged_pred (tag : nat) (name : string) (args : list term) : atom :=
  Pred (Some tag) name args.

Definition truth : product := [].
Definition falsehood : formula := [].

Lemma term_eqb_spec x y : term_eqb x y = true <-> x = y.
Proof.
  unfold term_eqb. destruct (term_eq_dec x y); split; intro H; auto.
  discriminate.
Qed.

Lemma variable_eqb_spec x y : variable_eqb x y = true <-> x = y.
Proof.
  unfold variable_eqb, var_kind_eqb.
  destruct x as [kx nx], y as [ky ny].
  destruct kx, ky; simpl.
  - rewrite Nat.eqb_eq. split; intro H; [now subst|now inversion H].
  - split; intro H; [discriminate|inversion H].
  - split; intro H; [discriminate|inversion H].
  - rewrite Nat.eqb_eq. split; intro H; [now subst|now inversion H].
Qed.

Lemma terms_eqb_spec xs ys : terms_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl;
    try (split; intro H; [discriminate|inversion H]).
  - tauto.
  - rewrite Bool.andb_true_iff, term_eqb_spec, IH.
    split.
    + intros [-> ->]. reflexivity.
    + intro H. inversion H. auto.
Qed.

Lemma atom_eqb_spec x y : atom_eqb x y = true <-> x = y.
Proof.
  destruct x, y; simpl; try (split; intro H; [discriminate|inversion H]).
  - repeat rewrite Bool.andb_true_iff. repeat rewrite term_eqb_spec.
    split.
    + intros [-> ->]. reflexivity.
    + intro H. inversion H. auto.
  - repeat rewrite Bool.andb_true_iff. repeat rewrite term_eqb_spec.
    split.
    + intros [-> ->]. reflexivity.
    + intro H. inversion H. auto.
  - destruct tag, tag0; simpl; try (split; intro H; [discriminate|inversion H]).
    + repeat rewrite Bool.andb_true_iff.
      rewrite Nat.eqb_eq, String.eqb_eq, terms_eqb_spec.
      split.
      * intros [[-> ->] ->]. reflexivity.
      * intro H. inversion H; subst. auto.
    + rewrite Bool.andb_true_iff, String.eqb_eq, terms_eqb_spec.
      split.
      * intros [-> ->]. reflexivity.
      * intro H. inversion H; subst. auto.
Qed.

Definition atom_eq_dec (x y : atom) : {x = y} + {x <> y}.
Proof.
  destruct (atom_eqb x y) eqn:H.
  - left. now apply atom_eqb_spec.
  - right. intro Heq. subst y. assert (atom_eqb x x = true).
    { apply atom_eqb_spec. reflexivity. }
    congruence.
Defined.

Definition product_eq_dec (x y : product) : {x = y} + {x <> y} :=
  list_eq_dec atom_eq_dec x y.

Definition atom_mem (a : atom) (p : product) : bool :=
  existsb (atom_eqb a) p.

Definition product_subsetb (small big : product) : bool :=
  forallb (fun a => atom_mem a big) small.

Lemma atom_mem_spec a p : atom_mem a p = true <-> In a p.
Proof.
  unfold atom_mem. rewrite existsb_exists.
  split.
  - intros [x [Hin H]]. apply atom_eqb_spec in H. now subst x.
  - intro Hin. exists a. split; [exact Hin|]. apply atom_eqb_spec. reflexivity.
Qed.

Lemma product_subsetb_spec small big :
  product_subsetb small big = true <->
  forall a, In a small -> In a big.
Proof.
  unfold product_subsetb. rewrite forallb_forall.
  setoid_rewrite atom_mem_spec. tauto.
Qed.

Definition formula_eq_dec (x y : formula) : {x = y} + {x <> y} :=
  list_eq_dec product_eq_dec x y.

Definition sequent_eq_dec (x y : sequent) : {x = y} + {x <> y}.
Proof.
  decide equality; apply formula_eq_dec.
Defined.

Definition clause_eq_dec (x y : clause) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply list_eq_dec. exact term_eq_dec.
  - apply product_eq_dec.
Defined.

Definition definition_entry_eq_dec
    (x y : string * list clause) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply list_eq_dec. exact clause_eq_dec.
  - apply string_dec.
Defined.

Definition definitions_eq_dec (x y : definitions) : {x = y} + {x <> y} :=
  list_eq_dec definition_entry_eq_dec x y.

Definition judgment_eq_dec (x y : judgment) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply sequent_eq_dec.
  - apply definitions_eq_dec.
Defined.

(** The cyclic graph checker uses the Boolean equalities above.  Search and
    certificate reflection need the converse direction as well: a successful
    executable comparison must justify replacing one reified label by the
    other inside a semantic proof.  The following lemmas establish that link
    once, bottom-up, rather than repeating Boolean case analyses in every
    graph theorem. *)

Lemma atoms_eqb_spec xs ys : atoms_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl;
    try (split; intro H; [discriminate|inversion H]).
  - tauto.
  - rewrite Bool.andb_true_iff, atom_eqb_spec, IH.
    split.
    + intros [-> ->]. reflexivity.
    + intro H. inversion H. auto.
Qed.

Lemma formula_eqb_spec xs ys : formula_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl;
    try (split; intro H; [discriminate|inversion H]).
  - tauto.
  - rewrite Bool.andb_true_iff, atoms_eqb_spec, IH.
    split.
    + intros [-> ->]. reflexivity.
    + intro H. inversion H. auto.
Qed.

Lemma clause_eqb_spec x y : clause_eqb x y = true <-> x = y.
Proof.
  destruct x as [xb xh], y as [yb yh]. unfold clause_eqb; simpl.
  rewrite Bool.andb_true_iff, atoms_eqb_spec, terms_eqb_spec.
  split.
  - intros [-> ->]. reflexivity.
  - intro H. inversion H. auto.
Qed.

Lemma clauses_eqb_spec xs ys : clauses_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl;
    try (split; intro H; [discriminate|inversion H]).
  - tauto.
  - rewrite Bool.andb_true_iff, clause_eqb_spec, IH.
    split.
    + intros [-> ->]. reflexivity.
    + intro H. inversion H. auto.
Qed.

Lemma definitions_eqb_spec xs ys : definitions_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys. induction xs as [|[name cs] xs IH];
    intros [|[name' cs'] ys]; simpl;
    try (split; intro H; [discriminate|inversion H]).
  - tauto.
  - repeat rewrite Bool.andb_true_iff.
    rewrite String.eqb_eq, clauses_eqb_spec, IH.
    split.
    + intros [[-> ->] ->]. reflexivity.
    + intro H. inversion H. auto.
Qed.

Lemma sequent_eqb_spec x y : sequent_eqb x y = true <-> x = y.
Proof.
  destruct x as [xl xr], y as [yl yr]. unfold sequent_eqb; simpl.
  rewrite Bool.andb_true_iff, !formula_eqb_spec.
  split.
  - intros [-> ->]. reflexivity.
  - intro H. inversion H. auto.
Qed.

Lemma judgment_eqb_spec x y : judgment_eqb x y = true <-> x = y.
Proof.
  destruct x as [xd xq], y as [yd yq]. unfold judgment_eqb; simpl.
  rewrite Bool.andb_true_iff, definitions_eqb_spec, sequent_eqb_spec.
  split.
  - intros [-> ->]. reflexivity.
  - intro H. inversion H. auto.
Qed.
