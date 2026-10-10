From Stdlib Require Import List Bool Arith String.

From CyclistRocq.SP Require Import Syntax Semantics Rules.

Import ListNotations.
Open Scope string_scope.

(** * Executable, proof-producing rule generation

    Every successful branch below returns a theorem-backed rule or axiom.
    Operations whose semantic obligations are not yet discharged return
    [None]; no unchecked candidate is ever inserted into a graph. *)

Definition exact_identity_candidate (j : judgment)
    : option Cyclic.axiom_instance.
Proof.
  destruct j as [ds [left right]].
  destruct (formula_eq_dec left right) as [Heq | Hneq].
  - subst right. exact (Some (identity_axiom ds left)).
  - exact None.
Defined.

Definition tag_erasure_candidate (j : judgment)
    : option Cyclic.axiom_instance :=
  let ds := j.(judgment_definitions) in
  let q := j.(judgment_sequent) in
  let candidate := tag_erasure_axiom ds q.(antecedent) in
  if judgment_eqb candidate.(Cyclic.axiom_conclusion) j
  then Some candidate else None.

Definition inconsistency_candidate (j : judgment)
    : option Cyclic.axiom_instance.
Proof.
  destruct (formula_inconsistentb j.(judgment_sequent).(antecedent))
    eqn:Hbad.
  - exact (Some (ex_falso_axiom j.(judgment_definitions)
      j.(judgment_sequent).(antecedent) j.(judgment_sequent).(succedent)
      Hbad)).
  - exact None.
Defined.

Definition unify_two_terms a b x y s : option substitution :=
  match unify_term a x s with
  | Some s' => unify_term b y s'
  | None => None
  end.

Definition unify_pure_atom
    (pattern target : pure_atom) (s : substitution) : option substitution :=
  match pattern, target with
  | Equal a b, Equal x y | Disequal a b, Disequal x y =>
      unify_two_terms a b x y s
  | _, _ => None
  end.

Fixpoint unify_pures patterns targets s : option substitution :=
  match patterns, targets with
  | [], [] => Some s
  | p :: ps, t :: ts =>
      match unify_pure_atom p t s with
      | Some s' => unify_pures ps ts s'
      | None => None
      end
  | _, _ => None
  end.

Definition unify_points_to
    (pattern target : points_to) (s : substitution) : option substitution :=
  match unify_term pattern.(points_address) target.(points_address) s with
  | Some s' => unify_terms pattern.(points_fields) target.(points_fields) s'
  | None => None
  end.

Fixpoint unify_points_list patterns targets s : option substitution :=
  match patterns, targets with
  | [], [] => Some s
  | p :: ps, t :: ts =>
      match unify_points_to p t s with
      | Some s' => unify_points_list ps ts s'
      | None => None
      end
  | _, _ => None
  end.

Definition unify_predicate
    (pattern target : tagged_predicate) (s : substitution)
    : option substitution :=
  if String.eqb pattern.(predicate_name) target.(predicate_name) then
    unify_terms pattern.(predicate_arguments) target.(predicate_arguments) s
  else None.

Fixpoint unify_predicate_list patterns targets s : option substitution :=
  match patterns, targets with
  | [], [] => Some s
  | p :: ps, t :: ts =>
      match unify_predicate p t s with
      | Some s' => unify_predicate_list ps ts s'
      | None => None
      end
  | _, _ => None
  end.

Definition unify_heap
    (pattern target : symheap) (s : substitution) : option substitution :=
  match unify_pures pattern.(heap_pure) target.(heap_pure) s with
  | Some s1 =>
      match unify_points_list pattern.(heap_points) target.(heap_points) s1 with
      | Some s2 =>
          unify_predicate_list pattern.(heap_predicates)
            target.(heap_predicates) s2
      | None => None
      end
  | None => None
  end.

Definition predicate_intro_for_clause
    (ds : definitions) (goal : judgment) (name : string)
    (target_args : list term) (target_body : symheap) (c : clause)
    : option Cyclic.axiom_instance :=
  match in_dec clause_eq_dec c (lookup_definition name ds) with
  | left Hin =>
      match unify_terms c.(clause_head) target_args [] with
      | Some s =>
          match unify_heap c.(clause_body) target_body s with
          | Some complete =>
              let candidate := predicate_intro_axiom ds name c complete Hin in
              if judgment_eqb candidate.(Cyclic.axiom_conclusion) goal
              then Some candidate else None
          | None => None
          end
      | None => None
      end
  | right _ => None
  end.

Fixpoint first_predicate_intro
    (ds : definitions) (goal : judgment) (name : string)
    (target_args : list term) (target_body : symheap) (clauses : list clause)
    : option Cyclic.axiom_instance :=
  match clauses with
  | [] => None
  | c :: rest =>
      match predicate_intro_for_clause ds goal name target_args target_body c with
      | Some candidate => Some candidate
      | None => first_predicate_intro ds goal name target_args target_body rest
      end
  end.

Definition predicate_intro_candidate (j : judgment)
    : option Cyclic.axiom_instance :=
  match j.(judgment_sequent).(antecedent).(formula_heaps),
        j.(judgment_sequent).(succedent).(formula_heaps) with
  | [left_heap], [right_heap] =>
      match right_heap.(heap_pure), right_heap.(heap_points),
            right_heap.(heap_predicates) with
      | [], [], [p] =>
          first_predicate_intro j.(judgment_definitions) j
            p.(predicate_name) p.(predicate_arguments) left_heap
            (lookup_definition p.(predicate_name) j.(judgment_definitions))
      | _, _, _ => None
      end
  | _, _ => None
  end.

Definition first_some {A : Type} (x y : option A) : option A :=
  match x with Some value => Some value | None => y end.

Definition generate_axiom (j : judgment) : option Cyclic.axiom_instance :=
  first_some (exact_identity_candidate j)
    (first_some (inconsistency_candidate j)
      (first_some (tag_erasure_candidate j)
        (predicate_intro_candidate j))).

Definition left_disjunction_candidate (j : judgment)
    : option Cyclic.rule_instance :=
  match j.(judgment_sequent).(antecedent).(formula_heaps) with
  | head :: (_ :: _ as tail) =>
      Some (left_disjunction_rule j.(judgment_definitions)
        j.(judgment_sequent) head tail)
  | _ => None
  end.

Definition right_disjunction_candidate (j : judgment)
    : option Cyclic.rule_instance :=
  match j.(judgment_sequent).(succedent).(formula_heaps) with
  | head :: (_ :: _ as tail) =>
      Some (right_disjunction_rule j.(judgment_definitions)
        j.(judgment_sequent) head tail)
  | _ => None
  end.

Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with Some value => [value] | None => [] end.

(** The order mirrors the front of the OCaml priority list.  Simplification
    and normalization are attempted as axioms before branching. *)
Definition generate_rules (j : judgment) : list Cyclic.rule_instance :=
  option_to_list (left_disjunction_candidate j) ++
  option_to_list (right_disjunction_candidate j).

(** Named conservative stubs document unsupported transformations at their
    executable boundary. *)
Definition generate_equality_substitution (_ : judgment)
    : option Cyclic.rule_instance := None.
Definition generate_constraint_simplification (_ : judgment)
    : option Cyclic.rule_instance := None.
Definition generate_bound_introduction (_ : judgment)
    : option Cyclic.rule_instance := None.
Definition generate_points_to_instantiation (_ : judgment)
    : option Cyclic.rule_instance := None.
Definition generate_left_unfolding (_ : judgment)
    : option Cyclic.rule_instance := None.
Definition generate_right_unfolding (_ : judgment)
    : option Cyclic.rule_instance := None.
Definition generate_partial_backlink (_ _ : judgment)
    : option Cyclic.rule_instance := None.

Example equality_generator_rejects_unproved_case j :
  generate_equality_substitution j = None.
Proof. reflexivity. Qed.

Example left_disjunction_requires_two_branches ds q h :
  left_disjunction_candidate
    (mk_judgment ds (replace_antecedent q
      (replace_heaps q.(antecedent) [h]))) = None.
Proof. reflexivity. Qed.
