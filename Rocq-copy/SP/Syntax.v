From Stdlib Require Import List Bool Arith String.

Import ListNotations.
Open Scope string_scope.

(** * Executable syntax for symbolic-heap separation logic

    This file deliberately keeps the representation elementary.  Names in an
    input file are reified as natural numbers by the examples module; the two
    constructors below retain the important distinction between parameters
    and formula-local existential witnesses. *)
Inductive var_kind : Type := Free | Existential.

Record variable : Type := {
  variable_kind : var_kind;
  variable_id : nat
}.

Definition free_var n :=
  {| variable_kind := Free; variable_id := n |}.
Definition existential_var n :=
  {| variable_kind := Existential; variable_id := n |}.

(** Separation-logic terms contain variables and the distinguished null
    location only. *)
Inductive term : Type :=
| Nil
| Var (x : variable).

(** Tags have the same three classes as the OCaml prover.  Anonymous tags do
    not participate in traces or ordinal constraints. *)
Inductive trace_tag : Type :=
| Anonymous
| FreeTag (name : nat)
| ExistentialTag (name : nat).

Inductive order_kind : Type := Strict | NonStrict.

Record ordinal_constraint : Type := {
  constraint_left : trace_tag;
  constraint_order : order_kind;
  constraint_right : trace_tag
}.

Inductive pure_atom : Type :=
| Equal (left right : term)
| Disequal (left right : term).

Record points_to : Type := {
  points_address : term;
  points_fields : list term
}.

Record tagged_predicate : Type := {
  predicate_tag : trace_tag;
  predicate_name : string;
  predicate_arguments : list term
}.

(** A symbolic heap is a pure conjunction and a separating conjunction of
    points-to cells and inductive predicates.  Separate lists make the common
    side conditions executable without obscuring the semantics. *)
Record symheap : Type := {
  heap_pure : list pure_atom;
  heap_points : list points_to;
  heap_predicates : list tagged_predicate
}.

(** A formula is a disjunction of symbolic heaps guarded by ordinal
    constraints.  The empty heap list denotes false; [[]] with no spatial
    atoms is [emp]. *)
Record formula : Type := {
  formula_constraints : list ordinal_constraint;
  formula_heaps : list symheap
}.

Record sequent : Type := {
  antecedent : formula;
  succedent : formula
}.

(** A clause body may use variables not in its head.  They are local to an
    unfolding and are freshened by rule generation. *)
Record clause : Type := {
  clause_body : symheap;
  clause_head : list term
}.

Definition definitions : Type := list (string * list clause).

Record judgment : Type := {
  judgment_definitions : definitions;
  judgment_sequent : sequent
}.

(** Decidable structural equalities.  Keeping these definitions proof
    relevant lets the executable checker reflect a successful comparison back
    to an equality accepted by the kernel. *)
Definition var_kind_eq_dec : forall x y : var_kind, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition variable_eq_dec : forall x y : variable, {x = y} + {x <> y}.
Proof. decide equality; [apply Nat.eq_dec | apply var_kind_eq_dec]. Defined.

Definition term_eq_dec : forall x y : term, {x = y} + {x <> y}.
Proof. decide equality; apply variable_eq_dec. Defined.

Definition trace_tag_eq_dec : forall x y : trace_tag, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition order_kind_eq_dec : forall x y : order_kind, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition ordinal_constraint_eq_dec :
  forall x y : ordinal_constraint, {x = y} + {x <> y}.
Proof.
  decide equality; try apply trace_tag_eq_dec; try apply order_kind_eq_dec.
Defined.

Definition pure_atom_eq_dec : forall x y : pure_atom, {x = y} + {x <> y}.
Proof. decide equality; apply term_eq_dec. Defined.

Definition points_to_eq_dec : forall x y : points_to, {x = y} + {x <> y}.
Proof.
  decide equality; try apply term_eq_dec; apply list_eq_dec; apply term_eq_dec.
Defined.

Definition tagged_predicate_eq_dec :
  forall x y : tagged_predicate, {x = y} + {x <> y}.
Proof.
  decide equality; try apply trace_tag_eq_dec; try apply string_dec;
    apply list_eq_dec; apply term_eq_dec.
Defined.

Definition symheap_eq_dec : forall x y : symheap, {x = y} + {x <> y}.
Proof.
  decide equality;
    try (apply list_eq_dec; apply tagged_predicate_eq_dec);
    try (apply list_eq_dec; apply points_to_eq_dec);
    apply list_eq_dec; apply pure_atom_eq_dec.
Defined.

Definition formula_eq_dec : forall x y : formula, {x = y} + {x <> y}.
Proof.
  decide equality;
    try (apply list_eq_dec; apply symheap_eq_dec);
    apply list_eq_dec; apply ordinal_constraint_eq_dec.
Defined.

Definition sequent_eq_dec : forall x y : sequent, {x = y} + {x <> y}.
Proof. decide equality; apply formula_eq_dec. Defined.

Definition clause_eq_dec : forall x y : clause, {x = y} + {x <> y}.
Proof.
  decide equality; try apply symheap_eq_dec; apply list_eq_dec; apply term_eq_dec.
Defined.

Definition definition_entry_eq_dec :
  forall x y : string * list clause, {x = y} + {x <> y}.
Proof.
  decide equality; try apply string_dec; apply list_eq_dec; apply clause_eq_dec.
Defined.

Definition definitions_eq_dec : forall x y : definitions, {x = y} + {x <> y} :=
  list_eq_dec definition_entry_eq_dec.

Definition judgment_eq_dec : forall x y : judgment, {x = y} + {x <> y}.
Proof. decide equality; [apply sequent_eq_dec | apply definitions_eq_dec]. Defined.

Definition term_eqb x y := if term_eq_dec x y then true else false.
Definition tag_eqb x y := if trace_tag_eq_dec x y then true else false.
Definition pure_atom_eqb x y := if pure_atom_eq_dec x y then true else false.
Definition points_to_eqb x y := if points_to_eq_dec x y then true else false.
Definition tagged_predicate_eqb x y :=
  if tagged_predicate_eq_dec x y then true else false.
Definition symheap_eqb x y := if symheap_eq_dec x y then true else false.
Definition formula_eqb x y := if formula_eq_dec x y then true else false.
Definition sequent_eqb x y := if sequent_eq_dec x y then true else false.
Definition definitions_eqb x y := if definitions_eq_dec x y then true else false.
Definition judgment_eqb x y := if judgment_eq_dec x y then true else false.

Lemma term_eqb_spec x y : term_eqb x y = true <-> x = y.
Proof. unfold term_eqb; destruct (term_eq_dec x y); intuition discriminate. Qed.

Lemma tag_eqb_spec x y : tag_eqb x y = true <-> x = y.
Proof. unfold tag_eqb; destruct (trace_tag_eq_dec x y); intuition discriminate. Qed.

Lemma judgment_eqb_spec x y : judgment_eqb x y = true <-> x = y.
Proof. unfold judgment_eqb; destruct (judgment_eq_dec x y); intuition discriminate. Qed.

(** Trace annotations have no effect on predicate membership.  Backlink
    comparison erases predicate tags and ordinal constraints, while retaining
    every logical symbol, term, disjunct, and definition.  A backlink rule
    still has to prove its own semantic transformation; this comparison alone
    never grants soundness. *)
Definition erase_predicate_tag (p : tagged_predicate) : tagged_predicate :=
  {| predicate_tag := Anonymous;
     predicate_name := p.(predicate_name);
     predicate_arguments := p.(predicate_arguments) |}.

Definition erase_heap_tags (h : symheap) : symheap :=
  {| heap_pure := h.(heap_pure);
     heap_points := h.(heap_points);
     heap_predicates := map erase_predicate_tag h.(heap_predicates) |}.

Definition erase_formula_tags (f : formula) : formula :=
  {| formula_constraints := [];
     formula_heaps := map erase_heap_tags f.(formula_heaps) |}.

Definition erase_sequent_tags (q : sequent) : sequent :=
  {| antecedent := erase_formula_tags q.(antecedent);
     succedent := erase_formula_tags q.(succedent) |}.

Definition backlink_eqb (x y : judgment) : bool :=
  definitions_eqb x.(judgment_definitions) y.(judgment_definitions) &&
  sequent_eqb (erase_sequent_tags x.(judgment_sequent))
              (erase_sequent_tags y.(judgment_sequent)).

(** Simultaneous term substitution and a small unifier. *)
Definition substitution : Type := list (variable * term).

Fixpoint lookup_substitution (s : substitution) (x : variable) : option term :=
  match s with
  | [] => None
  | (y, t) :: rest =>
      if variable_eq_dec x y then Some t else lookup_substitution rest x
  end.

Definition subst_term (s : substitution) (t : term) : term :=
  match t with
  | Nil => Nil
  | Var x => match lookup_substitution s x with Some u => u | None => t end
  end.

Definition subst_pure (s : substitution) (a : pure_atom) : pure_atom :=
  match a with
  | Equal x y => Equal (subst_term s x) (subst_term s y)
  | Disequal x y => Disequal (subst_term s x) (subst_term s y)
  end.

Definition subst_points (s : substitution) (p : points_to) : points_to :=
  {| points_address := subst_term s p.(points_address);
     points_fields := map (subst_term s) p.(points_fields) |}.

Definition subst_predicate
    (s : substitution) (p : tagged_predicate) : tagged_predicate :=
  {| predicate_tag := p.(predicate_tag);
     predicate_name := p.(predicate_name);
     predicate_arguments := map (subst_term s) p.(predicate_arguments) |}.

Definition subst_heap (s : substitution) (h : symheap) : symheap :=
  {| heap_pure := map (subst_pure s) h.(heap_pure);
     heap_points := map (subst_points s) h.(heap_points);
     heap_predicates := map (subst_predicate s) h.(heap_predicates) |}.

Definition subst_formula (s : substitution) (f : formula) : formula :=
  {| formula_constraints := f.(formula_constraints);
     formula_heaps := map (subst_heap s) f.(formula_heaps) |}.

Definition subst_sequent (s : substitution) (q : sequent) : sequent :=
  {| antecedent := subst_formula s q.(antecedent);
     succedent := subst_formula s q.(succedent) |}.

Definition subst_clause (s : substitution) (c : clause) : clause :=
  {| clause_body := subst_heap s c.(clause_body);
     clause_head := map (subst_term s) c.(clause_head) |}.

(** Tag substitutions are kept separate from term substitutions.  Anonymous
    occurrences are never keys; a missing named tag is left unchanged. *)
Definition tag_substitution : Type := list (trace_tag * trace_tag).

Fixpoint lookup_tag_substitution
    (s : tag_substitution) (tag : trace_tag) : option trace_tag :=
  match s with
  | [] => None
  | (source, target) :: rest =>
      if trace_tag_eq_dec tag source then Some target
      else lookup_tag_substitution rest tag
  end.

Definition subst_tag (s : tag_substitution) (tag : trace_tag) : trace_tag :=
  match tag with
  | Anonymous => Anonymous
  | _ => match lookup_tag_substitution s tag with
         | Some target => target
         | None => tag
         end
  end.

Definition subst_constraint_tags
    (s : tag_substitution) (c : ordinal_constraint) : ordinal_constraint :=
  {| constraint_left := subst_tag s c.(constraint_left);
     constraint_order := c.(constraint_order);
     constraint_right := subst_tag s c.(constraint_right) |}.

Definition subst_predicate_tags
    (s : tag_substitution) (p : tagged_predicate) : tagged_predicate :=
  {| predicate_tag := subst_tag s p.(predicate_tag);
     predicate_name := p.(predicate_name);
     predicate_arguments := p.(predicate_arguments) |}.

Definition subst_heap_tags (s : tag_substitution) (h : symheap) : symheap :=
  {| heap_pure := h.(heap_pure);
     heap_points := h.(heap_points);
     heap_predicates := map (subst_predicate_tags s) h.(heap_predicates) |}.

Definition subst_formula_tags (s : tag_substitution) (f : formula) : formula :=
  {| formula_constraints := map (subst_constraint_tags s)
       f.(formula_constraints);
     formula_heaps := map (subst_heap_tags s) f.(formula_heaps) |}.

Definition unify_tag (pattern target : trace_tag)
    (s : tag_substitution) : option tag_substitution :=
  match pattern with
  | Anonymous =>
      match target with Anonymous => Some s | _ => None end
  | _ =>
      match lookup_tag_substitution s pattern with
      | Some assigned => if trace_tag_eq_dec assigned target then Some s else None
      | None => Some ((pattern, target) :: s)
      end
  end.

Definition bind_variable
    (x : variable) (t : term) (s : substitution) : option substitution :=
  match lookup_substitution s x with
  | Some u => if term_eq_dec u t then Some s else None
  | None => Some ((x, t) :: s)
  end.

Definition unify_term (pattern target : term) (s : substitution)
    : option substitution :=
  match pattern with
  | Nil => match target with Nil => Some s | _ => None end
  | Var x => bind_variable x target s
  end.

Fixpoint unify_terms
    (patterns targets : list term) (s : substitution) : option substitution :=
  match patterns, targets with
  | [], [] => Some s
  | p :: ps, t :: ts =>
      match unify_term p t s with
      | Some s' => unify_terms ps ts s'
      | None => None
      end
  | _, _ => None
  end.

(** Freshening shifts only existential identifiers.  Free parameters retain
    their identity, as required when a clause head is matched to a goal. *)
Definition freshen_variable (offset : nat) (x : variable) : variable :=
  match x.(variable_kind) with
  | Free => x
  | Existential => existential_var (offset + x.(variable_id))
  end.

Definition freshen_term offset t :=
  match t with Nil => Nil | Var x => Var (freshen_variable offset x) end.

Definition freshen_tag offset t :=
  match t with
  | ExistentialTag n => ExistentialTag (offset + n)
  | _ => t
  end.

Definition freshen_predicate offset (p : tagged_predicate) :=
  {| predicate_tag := freshen_tag offset p.(predicate_tag);
     predicate_name := p.(predicate_name);
     predicate_arguments := map (freshen_term offset) p.(predicate_arguments) |}.

Definition freshen_heap offset (h : symheap) : symheap :=
  {| heap_pure := map (fun a =>
       match a with
       | Equal x y => Equal (freshen_term offset x) (freshen_term offset y)
       | Disequal x y => Disequal (freshen_term offset x) (freshen_term offset y)
       end) h.(heap_pure);
     heap_points := map (fun p =>
       {| points_address := freshen_term offset p.(points_address);
          points_fields := map (freshen_term offset) p.(points_fields) |})
       h.(heap_points);
     heap_predicates := map (freshen_predicate offset) h.(heap_predicates) |}.

(** Normalization is intentionally conservative: it removes no information
    and performs no quotienting beyond simultaneous substitution requested by
    a verified rule.  This identity normal form is idempotent and avoids the
    unsound representative choices that can arise from an unproved union-find
    port. *)
Definition normalize_heap (h : symheap) : symheap := h.
Definition normalize_formula (f : formula) : formula := f.
Definition normalize_sequent (q : sequent) : sequent := q.
Definition normalize_judgment (j : judgment) : judgment := j.

Lemma normalize_heap_idempotent h :
  normalize_heap (normalize_heap h) = normalize_heap h.
Proof. reflexivity. Qed.

(** Executable side conditions. *)
Definition pure_reflexive_contradiction (a : pure_atom) : bool :=
  match a with
  | Disequal x y => term_eqb x y
  | _ => false
  end.

Definition heap_inconsistentb (h : symheap) : bool :=
  existsb pure_reflexive_contradiction h.(heap_pure).

Definition formula_inconsistentb (f : formula) : bool :=
  forallb heap_inconsistentb f.(formula_heaps).

Definition tag_namedb (t : trace_tag) : bool :=
  match t with Anonymous => false | _ => true end.

Definition constraint_wfb (c : ordinal_constraint) : bool :=
  tag_namedb c.(constraint_left) && tag_namedb c.(constraint_right).

Definition formula_wfb (f : formula) : bool :=
  forallb constraint_wfb f.(formula_constraints).

Definition points_widthb (width : nat) (p : points_to) : bool :=
  Nat.eqb (List.length p.(points_fields)) width.

(** Only free antecedent tags are exposed to the cyclic framework.  Generated
    rules instantiate existential tags before they can become trace nodes. *)
Definition predicate_free_tag (p : tagged_predicate) : option nat :=
  match p.(predicate_tag) with FreeTag n => Some n | _ => None end.

Fixpoint predicate_tags (ps : list tagged_predicate) : list nat :=
  match ps with
  | [] => []
  | p :: rest =>
      match predicate_free_tag p with
      | Some n => n :: predicate_tags rest
      | None => predicate_tags rest
      end
  end.

Definition heap_tags (h : symheap) : list nat :=
  predicate_tags h.(heap_predicates).

Definition formula_tags (f : formula) : list nat :=
  nodup Nat.eq_dec (List.concat (map heap_tags f.(formula_heaps))).

Definition judgment_tags (j : judgment) : list nat :=
  formula_tags j.(judgment_sequent).(antecedent).

Fixpoint lookup_definition (name : string) (ds : definitions) : list clause :=
  match ds with
  | [] => []
  | (candidate, clauses) :: rest =>
      if String.eqb name candidate then clauses else lookup_definition name rest
  end.

(** Small constructors used by reified definitions and tests. *)
Definition mk_heap pure points predicates : symheap :=
  {| heap_pure := pure; heap_points := points; heap_predicates := predicates |}.
Definition emp : symheap := mk_heap [] [] [].
Definition pto address fields : points_to :=
  {| points_address := address; points_fields := fields |}.
Definition pred tag name arguments : tagged_predicate :=
  {| predicate_tag := tag; predicate_name := name;
     predicate_arguments := arguments |}.
Definition untagged_pred name arguments := pred Anonymous name arguments.
Definition tagged_pred tag name arguments := pred (FreeTag tag) name arguments.
Definition mk_formula constraints heaps : formula :=
  {| formula_constraints := constraints; formula_heaps := heaps |}.
Definition singleton_formula h := mk_formula [] [h].
Definition false_formula := mk_formula [] [].
Definition mk_sequent left right : sequent :=
  {| antecedent := left; succedent := right |}.
Definition mk_judgment ds q : judgment :=
  {| judgment_definitions := ds; judgment_sequent := q |}.
Definition mk_clause body head : clause :=
  {| clause_body := body; clause_head := head |}.
Definition lt_constraint left right : ordinal_constraint :=
  {| constraint_left := left; constraint_order := Strict;
     constraint_right := right |}.
Definition le_constraint left right : ordinal_constraint :=
  {| constraint_left := left; constraint_order := NonStrict;
     constraint_right := right |}.

Example substitution_unit :
  subst_term [(free_var 0, Nil)] (Var (free_var 0)) = Nil.
Proof. reflexivity. Qed.

Example unification_unit :
  unify_terms [Var (free_var 0); Nil] [Nil; Nil] [] =
    Some [(free_var 0, Nil)].
Proof. reflexivity. Qed.

Example tag_substitution_unit :
  subst_tag [(ExistentialTag 0, FreeTag 7)] (ExistentialTag 0) = FreeTag 7.
Proof. reflexivity. Qed.

Example malformed_constraint_rejected :
  constraint_wfb (lt_constraint Anonymous (FreeTag 0)) = false.
Proof. reflexivity. Qed.
