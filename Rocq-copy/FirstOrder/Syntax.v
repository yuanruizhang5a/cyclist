From Stdlib Require Import List Bool Arith String.

Import ListNotations.
Open Scope string_scope.

(** Variables are split into the two classes used by Cyclist's first-order
    frontend.  The executable prover currently keeps the distinction even
    though the benchmark fragment only contains free variables. *)
Inductive var_kind : Type := Free | Existential.

(** A variable is represented by its class and a numeric identifier.  Thus
    free variable 0 and existential variable 0 are different variables. *)
Record variable : Type := {
  variable_kind : var_kind;
  variable_id : nat
}.

(** Build the free (parameter) variable with identifier [x]. *)
Definition free_var (x : nat) : variable :=
  {| variable_kind := Free; variable_id := x |}.

(** Build the existential (witness) variable with identifier [x]. *)
Definition existential_var (x : nat) : variable :=
  {| variable_kind := Existential; variable_id := x |}.

(** Executable equality for the two variable classes. *)
Definition var_kind_eqb (x y : var_kind) : bool :=
  match x, y with
  | Free, Free | Existential, Existential => true
  | _, _ => false
  end.

(** Executable equality for variables: both the class and identifier must
    agree. *)
Definition variable_eqb (x y : variable) : bool :=
  var_kind_eqb x.(variable_kind) y.(variable_kind) &&
  Nat.eqb x.(variable_id) y.(variable_id).

(** First-order terms are numeric constants, variables, or applications of a
    named function symbol to a (possibly empty) list of argument terms. *)
Inductive term : Type :=
| Const (n : nat)
| Var (x : variable)
| Fun (name : string) (args : list term).

(** Proof-relevant, decidable equality for variables.  A result is either a
    proof that the inputs are equal or a proof that they are unequal. *)
Definition variable_eq_dec : forall x y : variable, {x = y} + {x <> y}.
Proof. decide equality; [apply Nat.eq_dec | decide equality]. Defined.

(** Structural decidable equality for terms, recursively comparing function
    names and argument lists. *)
Fixpoint term_eq_dec (x y : term) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply variable_eq_dec.
  - apply list_eq_dec. exact term_eq_dec.
  - apply string_dec.
Defined.

(** Boolean wrapper around [term_eq_dec], convenient for executable checks. *)
Definition term_eqb (x y : term) : bool :=
  if term_eq_dec x y then true else false.

(** Compare two term lists element by element; differing lengths are unequal. *)
Fixpoint terms_eqb (xs ys : list term) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => term_eqb x y && terms_eqb xs' ys'
  | _, _ => false
  end.

(** The distinguished zero term used by the arithmetic/list rules. *)
Definition zero : term := Const 0.
(** Construct the unary successor term [s(t)]. *)
Definition succ (t : term) : term := Fun "s" [t].
(** Construct the binary list-cell term [cons(head, tail)]. *)
Definition cons (head tail : term) : term := Fun "cons" [head; tail].

(** Atomic formulas are equality, disequality, or a predicate application.
    Predicate tags are trace metadata: [None] means untagged, while [Some n]
    identifies an occurrence for cyclic-proof progress tracking. *)
Inductive atom : Type :=
| Eq (left right : term)
| Neq (left right : term)
| Pred (tag : option nat) (name : string) (args : list term).

(** Executable equality for optional natural-number tags. *)
Definition option_nat_eqb (x y : option nat) : bool :=
  match x, y with
  | None, None => true
  | Some n, Some m => Nat.eqb n m
  | _, _ => false
  end.

(** Structural equality of atoms, including a predicate's trace tag. *)
Definition atom_eqb (x y : atom) : bool :=
  match x, y with
  | Eq a b, Eq c d | Neq a b, Neq c d =>
      term_eqb a c && term_eqb b d
  | Pred t p xs, Pred u q ys =>
      option_nat_eqb t u && String.eqb p q && terms_eqb xs ys
  | _, _ => false
  end.

(** Structural equality of atoms except that predicate tags are ignored.
    This is the logical comparison used when trace annotations should not
    affect whether two predicate atoms mean the same thing. *)
Definition atom_eqb_upto_tags (x y : atom) : bool :=
  match x, y with
  | Eq a b, Eq c d | Neq a b, Neq c d =>
      term_eqb a c && term_eqb b d
  | Pred _ p xs, Pred _ q ys => String.eqb p q && terms_eqb xs ys
  | _, _ => false
  end.

(** A product is a conjunction of atoms.  The empty list therefore denotes
    truth. *)
Definition product : Type := list atom.
(** A formula is a disjunction of products (disjunctive normal form).  The
    empty list therefore denotes falsehood. *)
Definition formula : Type := list product.

(** A sequent [antecedent |- succedent] stores a DNF formula on each side. *)
Record sequent : Type := {
  antecedent : formula;
  succedent : formula
}.

(** A clause describes one way to derive a predicate: [clause_body] is the
    conjunction of premises and [clause_head] is the predicate's argument
    pattern.  The predicate name is supplied by the enclosing definition. *)
Record clause : Type := {
  clause_body : product;
  clause_head : list term
}.

(** Association lists deliberately preserve the ordering of definitions and
    clauses, just as the OCaml implementation does. *)
Definition definitions : Type := list (string * list clause).

(** A judgment packages the inductive predicate definitions together with
    the sequent to be proved. *)
Record judgment : Type := {
  judgment_definitions : definitions;
  judgment_sequent : sequent
}.

(** Compare two products (lists of atoms), including tags and list order. *)
Fixpoint atoms_eqb (xs ys : list atom) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => atom_eqb x y && atoms_eqb xs' ys'
  | _, _ => false
  end.

(** Compare products in order while ignoring predicate tags. *)
Fixpoint atoms_eqb_upto_tags (xs ys : list atom) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      atom_eqb_upto_tags x y && atoms_eqb_upto_tags xs' ys'
  | _, _ => false
  end.

(** Compare two DNF formulas product by product, including predicate tags. *)
Fixpoint formula_eqb (xs ys : formula) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => atoms_eqb x y && formula_eqb xs' ys'
  | _, _ => false
  end.

(** Compare DNF formulas in order while ignoring all predicate tags. *)
Fixpoint formula_eqb_upto_tags (xs ys : formula) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      atoms_eqb_upto_tags x y && formula_eqb_upto_tags xs' ys'
  | _, _ => false
  end.

(** Exact Boolean equality for both sides of a sequent. *)
Definition sequent_eqb (x y : sequent) : bool :=
  formula_eqb x.(antecedent) y.(antecedent) &&
  formula_eqb x.(succedent) y.(succedent).

(** Equality of sequents modulo predicate trace tags on both sides. *)
Definition sequent_eqb_upto_tags (x y : sequent) : bool :=
  formula_eqb_upto_tags x.(antecedent) y.(antecedent) &&
  formula_eqb_upto_tags x.(succedent) y.(succedent).

(** Exact equality of two clauses, including body order and predicate tags. *)
Definition clause_eqb (x y : clause) : bool :=
  atoms_eqb x.(clause_body) y.(clause_body) &&
  terms_eqb x.(clause_head) y.(clause_head).

(** Elementwise equality of clause lists. *)
Fixpoint clauses_eqb (xs ys : list clause) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => clause_eqb x y && clauses_eqb xs' ys'
  | _, _ => false
  end.

(** Equality of ordered definition tables.  Both predicate-entry order and
    clause order are significant to this executable comparison. *)
Fixpoint definitions_eqb (xs ys : definitions) : bool :=
  match xs, ys with
  | [], [] => true
  | (p, cs) :: xs', (q, ds) :: ys' =>
      String.eqb p q && clauses_eqb cs ds && definitions_eqb xs' ys'
  | _, _ => false
  end.

(** Exact equality of judgments: definitions, sequent, and tags must agree. *)
Definition judgment_eqb (x y : judgment) : bool :=
  definitions_eqb x.(judgment_definitions) y.(judgment_definitions) &&
  sequent_eqb x.(judgment_sequent) y.(judgment_sequent).

(** Equality used when closing a cyclic backlink.  Definitions must be exact,
    but trace tags in the sequents may differ. *)
Definition backlink_eqb (x y : judgment) : bool :=
  definitions_eqb x.(judgment_definitions) y.(judgment_definitions) &&
  sequent_eqb_upto_tags x.(judgment_sequent) y.(judgment_sequent).

(** A substitution is an association list mapping variables to replacement
    terms.  If a variable occurs more than once, the first mapping wins. *)
Definition substitution : Type := list (variable * term).

(** Find the first replacement assigned to [x], or [None] if [x] is unmapped. *)
Fixpoint lookup_substitution (s : substitution) (x : variable) : option term :=
  match s with
  | [] => None
  | (y, t) :: s' =>
      if variable_eqb x y then Some t else lookup_substitution s' x
  end.

(** Apply a substitution recursively to one term.  Replacement terms are
    inserted as-is rather than substituted a second time (simultaneous
    substitution). *)
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

(** Apply [s] to every term occurring in an atom; predicate tags and names are
    preserved. *)
Definition subst_atom (s : substitution) (a : atom) : atom :=
  match a with
  | Eq x y => Eq (subst_term s x) (subst_term s y)
  | Neq x y => Neq (subst_term s x) (subst_term s y)
  | Pred t p xs => Pred t p (map (subst_term s) xs)
  end.

(** Apply a substitution to every atom of a conjunction. *)
Definition subst_product (s : substitution) (p : product) : product :=
  map (subst_atom s) p.

(** Apply a substitution to every conjunction of a DNF formula. *)
Definition subst_formula (s : substitution) (f : formula) : formula :=
  map (subst_product s) f.

(** Apply the same substitution to both sides of a sequent. *)
Definition subst_sequent (s : substitution) (q : sequent) : sequent :=
  {| antecedent := subst_formula s q.(antecedent);
     succedent := subst_formula s q.(succedent) |}.

(** Add [offset] to a variable identifier without changing whether the
    variable is free or existential. *)
Definition shift_variable (offset : nat) (x : variable) : variable :=
  {| variable_kind := x.(variable_kind);
     variable_id := offset + x.(variable_id) |}.

(** Rename every variable in a term by adding the same identifier offset. *)
Fixpoint shift_term (offset : nat) (t : term) : term :=
  match t with
  | Const n => Const n
  | Var x => Var (shift_variable offset x)
  | Fun f xs => Fun f (map (shift_term offset) xs)
  end.

(** Shift all variables in an atom while preserving its predicate metadata. *)
Definition shift_atom (offset : nat) (a : atom) : atom :=
  match a with
  | Eq x y => Eq (shift_term offset x) (shift_term offset y)
  | Neq x y => Neq (shift_term offset x) (shift_term offset y)
  | Pred t p xs => Pred t p (map (shift_term offset) xs)
  end.

(** Shift every atom of a product. *)
Definition shift_product (offset : nat) (p : product) : product :=
  map (shift_atom offset) p.

(** Shift the variables in both the body and head of a clause. *)
Definition shift_clause (offset : nat) (c : clause) : clause :=
  {| clause_body := shift_product offset c.(clause_body);
     clause_head := map (shift_term offset) c.(clause_head) |}.

(** Fresh variables introduced by a right unfolding are witnesses rather than
    parameters.  They therefore become existential variables irrespective of
    how the definition file names them. *)
Definition existential_shift_variable (offset : nat) (x : variable) : variable :=
  {| variable_kind := Existential;
     variable_id := offset + x.(variable_id) |}.

(** Shift a term's variable identifiers and turn every variable into an
    existential witness. *)
Fixpoint existential_shift_term (offset : nat) (t : term) : term :=
  match t with
  | Const n => Const n
  | Var x => Var (existential_shift_variable offset x)
  | Fun f xs => Fun f (map (existential_shift_term offset) xs)
  end.

(** Apply existential shifting to every term in an atom. *)
Definition existential_shift_atom (offset : nat) (a : atom) : atom :=
  match a with
  | Eq x y => Eq (existential_shift_term offset x)
                    (existential_shift_term offset y)
  | Neq x y => Neq (existential_shift_term offset x)
                      (existential_shift_term offset y)
  | Pred t p xs => Pred t p (map (existential_shift_term offset) xs)
  end.

(** Apply existential shifting to an entire conjunction. *)
Definition existential_shift_product (offset : nat) (p : product) : product :=
  map (existential_shift_atom offset) p.

(** Check that every variable identifier in [t] is strictly below [bound].
    Constants always pass; all function arguments must pass. *)
Fixpoint term_belowb (bound : nat) (t : term) : bool :=
  match t with
  | Const _ => true
  | Var x => Nat.ltb x.(variable_id) bound
  | Fun _ xs => forallb (term_belowb bound) xs
  end.

(** Check the variable bound for every term occurring in an atom. *)
Definition atom_belowb (bound : nat) (a : atom) : bool :=
  match a with
  | Eq x y | Neq x y => term_belowb bound x && term_belowb bound y
  | Pred _ _ xs => forallb (term_belowb bound) xs
  end.

(** Check the variable bound for every atom in a product. *)
Definition product_belowb (bound : nat) (p : product) : bool :=
  forallb (atom_belowb bound) p.

(** Check the variable bound for every product in a formula. *)
Definition formula_belowb (bound : nat) (f : formula) : bool :=
  forallb (product_belowb bound) f.

(** Check the variable bound on both sides of a sequent. *)
Definition sequent_belowb (bound : nat) (q : sequent) : bool :=
  formula_belowb bound q.(antecedent) && formula_belowb bound q.(succedent).

(** Return one more than the largest variable identifier in [t], or zero when
    [t] has no variables.  Hence every identifier in [t] is below the result. *)
Fixpoint term_max_var (t : term) : nat :=
  match t with
  | Const _ => 0
  | Var x => S x.(variable_id)
  | Fun _ xs => fold_right Nat.max 0 (map term_max_var xs)
  end.

(** Compute the exclusive upper bound on variable identifiers in an atom. *)
Definition atom_max_var (a : atom) : nat :=
  match a with
  | Eq x y | Neq x y => Nat.max (term_max_var x) (term_max_var y)
  | Pred _ _ xs => fold_right Nat.max 0 (map term_max_var xs)
  end.

(** Compute the exclusive upper bound on variable identifiers in a product. *)
Definition product_max_var (p : product) : nat :=
  fold_right Nat.max 0 (map atom_max_var p).

(** Compute the exclusive upper bound on variable identifiers in a formula. *)
Definition formula_max_var (f : formula) : nat :=
  fold_right Nat.max 0 (map product_max_var f).

(** Compute one bound that covers variables on both sides of a sequent. *)
Definition sequent_max_var (q : sequent) : nat :=
  Nat.max (formula_max_var q.(antecedent)) (formula_max_var q.(succedent)).

(** Choose the first identifier at or above all identifiers already in [q].
    Shifting clause-local variables by this value prevents name capture. *)
Definition fresh_variable_offset (q : sequent) : nat :=
  sequent_max_var q.

(** Read a predicate atom's optional trace tag; equations have no tag. *)
Definition atom_tag (a : atom) : option nat :=
  match a with
  | Pred t _ _ => t
  | _ => None
  end.

(** Replace the tag of a predicate atom, leaving equations unchanged. *)
Definition set_atom_tag (t : option nat) (a : atom) : atom :=
  match a with
  | Pred _ p xs => Pred t p xs
  | _ => a
  end.

(** Give every predicate atom in a product the same tag [t]. *)
Definition retag_product (t : nat) (p : product) : product :=
  map (set_atom_tag (Some t)) p.

(** Test whether a conjunction contains at least one predicate atom. *)
Fixpoint product_has_pred (p : product) : bool :=
  match p with
  | [] => false
  | Pred _ _ _ :: _ => true
  | _ :: p' => product_has_pred p'
  end.

(** Zip equally positioned terms into equality atoms.  Processing stops when
    either list ends, so callers that require a full zip check lengths first. *)
Fixpoint equation_product (xs ys : list term) : product :=
  match xs, ys with
  | x :: xs', y :: ys' => Eq x y :: equation_product xs' ys'
  | _, _ => []
  end.

(** Collect predicate tags from a product, in occurrence order; untagged
    predicates and equations contribute nothing. *)
Fixpoint product_tags (p : product) : list nat :=
  match p with
  | [] => []
  | a :: p' =>
      match atom_tag a with
      | Some t => t :: product_tags p'
      | None => product_tags p'
      end
  end.

(** Collect all predicate tags from the products of a formula, preserving
    their left-to-right order. *)
Fixpoint formula_tags (f : formula) : list nat :=
  match f with
  | [] => []
  | p :: f' => product_tags p ++ formula_tags f'
  end.

(** List the distinct tags occurring in the antecedent.  Only antecedent tags
    participate in cyclic trace checking. *)
Definition sequent_tags (q : sequent) : list nat :=
  nodup Nat.eq_dec (formula_tags q.(antecedent)).

(** Obtain the trace tags of the sequent contained in a judgment. *)
Definition judgment_tags (j : judgment) : list nat :=
  sequent_tags j.(judgment_sequent).

(** Compute the maximum element of a natural-number list, using zero for the
    empty list. *)
Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (max_list xs')
  end.

(** Produce a tag strictly larger than every tag currently in the antecedent. *)
Definition fresh_tag (q : sequent) : nat := S (max_list (sequent_tags q)).

(** Starting at [next], tag each predicate occurrence in one product with a
    distinct consecutive number.  The returned number is the next unused tag;
    equality and disequality atoms do not consume numbers. *)
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

(** Thread [tag_product_from] through every product of a formula, returning
    the tagged formula and the next unused tag. *)
Fixpoint tag_formula_from (next : nat) (f : formula) : formula * nat :=
  match f with
  | [] => ([], next)
  | p :: f' =>
      let '(p', next') := tag_product_from next p in
      let '(f'', next'') := tag_formula_from next' f' in
      (p' :: f'', next'')
  end.

(** Initialize cyclic tracing by assigning unique tags to antecedent predicate
    occurrences from zero.  The succedent is deliberately left unchanged. *)
Definition prepare_sequent (q : sequent) : sequent :=
  let '(lhs, _) := tag_formula_from 0 q.(antecedent) in
  {| antecedent := lhs; succedent := q.(succedent) |}.

(** Look up the first clause list associated with predicate [name].  Missing
    predicates have no clauses. *)
Fixpoint lookup_definition (name : string) (ds : definitions)
  : list clause :=
  match ds with
  | [] => []
  | (p, cs) :: ds' =>
      if String.eqb name p then cs else lookup_definition name ds'
  end.

(** Convenience constructor for a sequent. *)
Definition mk_sequent (lhs rhs : formula) : sequent :=
  {| antecedent := lhs; succedent := rhs |}.

(** Convenience constructor that pairs a definition table with a sequent. *)
Definition mk_judgment (ds : definitions) (q : sequent) : judgment :=
  {| judgment_definitions := ds; judgment_sequent := q |}.

(** Construct an untagged predicate atom. *)
Definition pred (name : string) (args : list term) : atom :=
  Pred None name args.

(** Construct a predicate atom carrying the specified trace tag. *)
Definition tagged_pred (tag : nat) (name : string) (args : list term) : atom :=
  Pred (Some tag) name args.

(** The empty conjunction, which is true because it has no required atoms. *)
Definition truth : product := [].
(** The empty disjunction, which is false because it has no true branch. *)
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

(** [atom_eqb] reports true exactly for structurally equal atoms. *)
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

(** Decidable equality for atoms, obtained from the verified Boolean test. *)
Definition atom_eq_dec (x y : atom) : {x = y} + {x <> y}.
Proof.
  destruct (atom_eqb x y) eqn:H.
  - left. now apply atom_eqb_spec.
  - right. intro Heq. subst y. assert (atom_eqb x x = true).
    { apply atom_eqb_spec. reflexivity. }
    congruence.
Defined.

(** Decidable structural equality for products. *)
Definition product_eq_dec (x y : product) : {x = y} + {x <> y} :=
  list_eq_dec atom_eq_dec x y.

(** Test exact membership of atom [a] in product [p]. *)
Definition atom_mem (a : atom) (p : product) : bool :=
  existsb (atom_eqb a) p.

(** Set-style containment: every atom in [small] must occur in [big].  Order
    and multiplicity are ignored, but predicate tags are compared exactly. *)
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

(** Membership modulo trace annotations.  Equality and disequality atoms are
    still compared exactly; only [Pred]'s optional tag is ignored by
    [atom_eqb_upto_tags].  The argument order is chosen so a successful lookup
    records the concrete atom found in [p] together with its comparison to
    the requested [needle]. *)
Definition atom_mem_upto_tags (needle : atom) (p : product) : bool :=
  existsb (fun candidate => atom_eqb_upto_tags candidate needle) p.

Lemma atom_mem_upto_tags_spec needle p :
  atom_mem_upto_tags needle p = true <->
  exists candidate, In candidate p /\
    atom_eqb_upto_tags candidate needle = true.
Proof.
  unfold atom_mem_upto_tags. rewrite existsb_exists. tauto.
Qed.

(** Set-style containment used by the original identity axiom.  Every atom
    requested by the right product must have a semantically identical atom
    in the left product, but predicate trace tags need not agree. *)
Definition product_subsetb_upto_tags (small big : product) : bool :=
  forallb (fun a => atom_mem_upto_tags a big) small.

Lemma product_subsetb_upto_tags_spec small big :
  product_subsetb_upto_tags small big = true <->
  forall a, In a small ->
    exists candidate, In candidate big /\
      atom_eqb_upto_tags candidate a = true.
Proof.
  unfold product_subsetb_upto_tags. rewrite forallb_forall.
  setoid_rewrite atom_mem_upto_tags_spec. tauto.
Qed.

(** Decidable structural equality for formulas. *)
Definition formula_eq_dec (x y : formula) : {x = y} + {x <> y} :=
  list_eq_dec product_eq_dec x y.

(** Decidable structural equality for sequents. *)
Definition sequent_eq_dec (x y : sequent) : {x = y} + {x <> y}.
Proof.
  decide equality; apply formula_eq_dec.
Defined.

(** Decidable structural equality for clauses. *)
Definition clause_eq_dec (x y : clause) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply list_eq_dec. exact term_eq_dec.
  - apply product_eq_dec.
Defined.

(** Decidable equality for one predicate-name/clause-list table entry. *)
Definition definition_entry_eq_dec
    (x y : string * list clause) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply list_eq_dec. exact clause_eq_dec.
  - apply string_dec.
Defined.

(** Decidable structural equality for complete ordered definition tables. *)
Definition definitions_eq_dec (x y : definitions) : {x = y} + {x <> y} :=
  list_eq_dec definition_entry_eq_dec x y.

(** Decidable structural equality for judgments. *)
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
