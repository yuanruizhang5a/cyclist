From Stdlib Require Import List Bool Arith Lia String.

From CyclistRocq.FirstOrder Require Import
  Syntax Semantics Rules Automation.

Import ListNotations.
Open Scope string_scope.

(** * Executable generation of theorem-backed rule instances

    Search must never manufacture a rule by merely attaching a name to new
    syntax.  Every result of this module is one of the semantic rule records
    proved in [Rules.v].  Boolean tests are destructed dependently, so their
    successful branch supplies the proposition needed by the constructor.

    The generators here deliberately expose only the rule shapes already
    supported by the verified kernel.  Returning an empty list is safe and
    means only that this implementation has no applicable verified rule. *)

Definition option_to_list {A : Type} (candidate : option A) : list A :=
  match candidate with Some x => [x] | None => [] end.

(** ** Closing axioms *)

Definition try_identity_product
    (ds : definitions) (big : product) (rhs : formula) (small : product)
    (Hin : In small rhs) : option Cyclic.axiom_instance.
Proof.
  (* Predicate tags describe cyclic traces, not predicate truth.  The
     original identity test therefore uses containment modulo tags; Eq and
     Neq atoms remain exact through [atom_eqb_upto_tags]. *)
  destruct (product_subsetb_upto_tags small big) eqn:Hsubset; [|exact None].
  exact (Some (identity_axiom_anywhere_upto_tags ds big rhs small
    Hin Hsubset)).
Defined.

(** Scan right products in source order, matching the deterministic priority
    of the OCaml set iterator after normalization. *)
Fixpoint find_identity_product
    (ds : definitions) (big : product) (whole remaining : formula)
    (Hsuffix : forall p, In p remaining -> In p whole)
    : option Cyclic.axiom_instance :=
  match remaining as rest return
      (forall p, In p rest -> In p whole) -> option Cyclic.axiom_instance with
  | [] => fun _ => None
  | small :: rest => fun Hin =>
      match try_identity_product ds big whole small (Hin small (or_introl eq_refl)) with
      | Some a => Some a
      | None =>
          find_identity_product ds big whole rest
            (fun p Hp => Hin p (or_intror Hp))
      end
  end Hsuffix.

Definition identity_candidate
    (ds : definitions) (big : product) (rhs : formula)
    : option Cyclic.axiom_instance :=
  find_identity_product ds big rhs rhs (fun _ H => H).

(** Recognize one contradictory atom.  Disequality reflexivity and disjoint
    constructor heads are precisely the ex-falso cases currently justified by
    [Rules.v]. *)
Definition contradiction_from_atom
    (ds : definitions) (p : product) (rhs : formula) (a : atom)
    (Hin : In a p) : option Cyclic.axiom_instance.
Proof.
  destruct a as [lhs rhs_term | lhs rhs_term | tag name args].
  - destruct lhs as [n|x|f xs]; destruct rhs_term as [m|y|g ys].
    + exact None.
    + exact None.
    + exact (Some (constructor_clash_axiom_left ds p rhs n g ys Hin)).
    + exact None.
    + exact None.
    + exact None.
    + exact (Some (constructor_clash_axiom_right ds p rhs m f xs Hin)).
    + exact None.
    + exact None.
  - destruct (term_eq_dec lhs rhs_term) as [Heq | Hneq].
    + subst rhs_term. exact (Some (disequality_axiom ds p rhs lhs Hin)).
    + exact None.
  - exact None.
Defined.

Fixpoint find_contradiction
    (ds : definitions) (whole remaining : product) (rhs : formula)
    (Hsuffix : forall a, In a remaining -> In a whole)
    : option Cyclic.axiom_instance :=
  match remaining as rest return
      (forall a, In a rest -> In a whole) -> option Cyclic.axiom_instance with
  | [] => fun _ => None
  | a :: rest => fun Hin =>
      match contradiction_from_atom ds whole rhs a
        (Hin a (or_introl eq_refl)) with
      | Some ax => Some ax
      | None =>
          find_contradiction ds whole rest rhs
            (fun b Hb => Hin b (or_intror Hb))
      end
  end Hsuffix.

Definition contradiction_candidate
    (ds : definitions) (p : product) (rhs : formula)
    : option Cyclic.axiom_instance :=
  find_contradiction ds p p rhs (fun _ H => H).

(** Ex-falso is tried before identity, exactly as in [rules.ml].  Both axioms
    currently require a singleton antecedent; [L.Or] is responsible for
    splitting a disjunctive antecedent first. *)
Definition generate_axiom (goal : judgment) : option Cyclic.axiom_instance :=
  match goal.(judgment_sequent).(antecedent) with
  | [big] =>
      match contradiction_candidate goal.(judgment_definitions) big
        goal.(judgment_sequent).(succedent) with
      | Some ax => Some ax
      | None => identity_candidate goal.(judgment_definitions) big
          goal.(judgment_sequent).(succedent)
      end
  | _ => None
  end.

(** ** Repeated simplification candidates *)

Fixpoint find_reflexive_equality
    (ds : definitions) (before remaining : product) (rhs : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | a :: after =>
      match a with
      | Eq lhs rhs_term =>
          match term_eq_dec lhs rhs_term with
          | left Heq =>
              match Heq in _ = equal return option Cyclic.rule_instance with
              | eq_refl => Some (reflexive_equality_rule ds before lhs after rhs)
              end
          | right _ =>
              find_reflexive_equality ds (before ++ [a])%list after rhs
          end
      | _ => find_reflexive_equality ds (before ++ [a])%list after rhs
      end
  end.

Definition left_equality_at_head
    (ds : definitions) (before : product) (lhs rhs_term : term)
    (after : product) (right_formula : formula)
    : option Cyclic.rule_instance.
Proof.
  destruct lhs as [n|x|name args]; [exact None| |exact None].
  destruct x as [kind id]. destruct kind; [|exact None].
  destruct (term_eqb (Var (free_var id)) rhs_term) eqn:Hequal;
    [exact None|].
  destruct (term_freeb rhs_term) eqn:Hfree; [|exact None].
  exact (Some (left_equality_substitution_rule ds before id rhs_term after
    right_formula Hfree)).
Defined.

Fixpoint find_left_equality_substitution
    (ds : definitions) (before remaining : product) (rhs : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | a :: after =>
      match a with
      | Eq lhs rhs_term =>
          match left_equality_at_head ds before lhs rhs_term after rhs with
          | Some rule => Some rule
          | None => find_left_equality_substitution ds
              (before ++ [a])%list after rhs
          end
      | _ => find_left_equality_substitution ds
          (before ++ [a])%list after rhs
      end
  end.

(** Find one reflexive equality in one succedent product.  The two prefix
    accumulators retain the exact original list shape required by
    [right_reflexive_equality_rule]. *)
Fixpoint find_right_reflexive_in_product
    (ds : definitions) (lhs before_products : formula)
    (before_atoms remaining : product) (after_products : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | a :: after_atoms =>
      match a with
      | Eq lhs_term rhs_term =>
          match term_eq_dec lhs_term rhs_term with
          | left Heq =>
              match Heq in _ = equal return option Cyclic.rule_instance with
              | eq_refl => Some (right_reflexive_equality_rule ds lhs
                  before_products before_atoms lhs_term after_atoms
                  after_products)
              end
          | right _ => find_right_reflexive_in_product ds lhs before_products
              (before_atoms ++ [a])%list after_atoms after_products
          end
      | _ => find_right_reflexive_in_product ds lhs before_products
          (before_atoms ++ [a])%list after_atoms after_products
      end
  end.

Fixpoint find_right_reflexive_in_formula
    (ds : definitions) (lhs before_products remaining : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | p :: after_products =>
      match find_right_reflexive_in_product ds lhs before_products [] p
        after_products with
      | Some rule => Some rule
      | None => find_right_reflexive_in_formula ds lhs
          (before_products ++ [p])%list after_products
      end
  end.

Definition right_reflexive_equality_candidate (goal : judgment)
    : option Cyclic.rule_instance :=
  let q := goal.(judgment_sequent) in
  find_right_reflexive_in_formula goal.(judgment_definitions)
    q.(antecedent) [] q.(succedent).

(** Recognize the solved-witness orientation [?e = t].  We deliberately
    require [t] to be free: that is the executable side condition used by the
    semantic proof to ensure that assigning [?e] cannot change the value of
    [t] when the succedent witness valuation is installed. *)
Definition right_existential_at_head
    (ds : definitions) (lhs before_products : formula)
    (before_atoms : product) (left_term right_term : term)
    (after_atoms : product) (after_products : formula)
    : option Cyclic.rule_instance.
Proof.
  destruct left_term as [n|x|name args]; [exact None| |exact None].
  destruct x as [kind id]. destruct kind; [exact None|].
  destruct (term_freeb right_term) eqn:Hfree; [|exact None].
  exact (Some (right_existential_substitution_at_rule ds lhs before_products
    before_atoms id right_term after_atoms after_products Hfree)).
Defined.

(** Recognize the orientation [t = ?e].  This step only swaps the equality;
    repeated simplification immediately exposes [?e = t] to the preceding
    witness-substitution generator. *)
Definition orient_right_existential_at_head
    (ds : definitions) (lhs before_products : formula)
    (before_atoms : product) (left_term right_term : term)
    (after_atoms : product) (after_products : formula)
    : option Cyclic.rule_instance.
Proof.
  destruct right_term as [n|x|name args]; [exact None| |exact None].
  destruct x as [kind id]. destruct kind; [exact None|].
  destruct (term_freeb left_term) eqn:Hfree; [|exact None].
  exact (Some (right_equality_orientation_rule ds lhs before_products
    before_atoms left_term id after_atoms after_products)).
Defined.

Fixpoint find_right_existential_in_product
    (ds : definitions) (lhs before_products : formula)
    (before_atoms remaining : product) (after_products : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | a :: after_atoms =>
      match a with
      | Eq left_term right_term =>
          match right_existential_at_head ds lhs before_products before_atoms
            left_term right_term after_atoms after_products with
          | Some rule => Some rule
          | None =>
              match orient_right_existential_at_head ds lhs before_products
                before_atoms left_term right_term after_atoms after_products with
              | Some rule => Some rule
              | None => find_right_existential_in_product ds lhs before_products
                  (before_atoms ++ [a])%list after_atoms after_products
              end
          end
      | _ => find_right_existential_in_product ds lhs before_products
          (before_atoms ++ [a])%list after_atoms after_products
      end
  end.

Fixpoint find_right_existential_in_formula
    (ds : definitions) (lhs before_products remaining : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | p :: after_products =>
      match find_right_existential_in_product ds lhs before_products [] p
        after_products with
      | Some rule => Some rule
      | None => find_right_existential_in_formula ds lhs
          (before_products ++ [p])%list after_products
      end
  end.

Definition right_existential_substitution_candidate (goal : judgment)
    : option Cyclic.rule_instance :=
  let q := goal.(judgment_sequent) in
  find_right_existential_in_formula goal.(judgment_definitions)
    q.(antecedent) [] q.(succedent).

(** ** Discharge succedent atoms supplied by a singleton antecedent

    [find_atom_upto_tags] returns not just the matching atom but also the two
    propositions required by the verified rule: membership in the complete
    antecedent product and successful comparison modulo predicate trace tags.
    Carrying these proofs in a dependent result avoids trusting a separate
    Boolean search routine. *)
Fixpoint find_atom_upto_tags (needle : atom) (haystack : product)
    : option { found : atom |
        In found haystack /\ atom_eqb_upto_tags found needle = true }.
Proof.
  destruct haystack as [|candidate rest].
  - exact None.
  - destruct (atom_eqb_upto_tags candidate needle) eqn:Hmatch.
    + exact (Some (exist _ candidate (conj (or_introl eq_refl) Hmatch))).
    + destruct (find_atom_upto_tags needle rest) as
          [[found [Hin Hfound]] |].
      * exact (Some (exist _ found (conj (or_intror Hin) Hfound))).
      * exact None.
Defined.

Definition right_discharge_at_head
    (ds : definitions) (lhs : product) (before_products : formula)
    (before_atoms : product) (supplied : atom) (after_atoms : product)
    (after_products : formula) : option Cyclic.rule_instance.
Proof.
  (* A right atom containing existential variables need not have the same
     value under the base and witness valuations.  Reject it unless the
     reflection checker proves that it is entirely free. *)
  destruct (atom_freeb supplied) eqn:Hfree; [|exact None].
  destruct (find_atom_upto_tags supplied lhs) as
      [[assumption [Hin Hmatch]] |]; [|exact None].
  exact (Some (right_discharge_rule ds lhs assumption before_products
    before_atoms supplied after_atoms after_products Hin Hmatch Hfree)).
Defined.

Fixpoint find_right_discharge_in_product
    (ds : definitions) (lhs : product) (before_products : formula)
    (before_atoms remaining : product) (after_products : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | supplied :: after_atoms =>
      match right_discharge_at_head ds lhs before_products before_atoms
        supplied after_atoms after_products with
      | Some rule => Some rule
      | None => find_right_discharge_in_product ds lhs before_products
          (before_atoms ++ [supplied])%list after_atoms after_products
      end
  end.

Fixpoint find_right_discharge_in_formula
    (ds : definitions) (lhs : product)
    (before_products remaining : formula) : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | p :: after_products =>
      match find_right_discharge_in_product ds lhs before_products [] p
        after_products with
      | Some rule => Some rule
      | None => find_right_discharge_in_formula ds lhs
          (before_products ++ [p])%list after_products
      end
  end.

Definition right_discharge_candidate (goal : judgment)
    : option Cyclic.rule_instance :=
  match goal.(judgment_sequent).(antecedent) with
  | [lhs] => find_right_discharge_in_formula goal.(judgment_definitions) lhs
      [] goal.(judgment_sequent).(succedent)
  | _ => None
  end.

(** ** Injective-constructor equalities on the left

    The original prover declares exactly [s] and [cons] to be injective.  A
    same-headed equality using either symbol may therefore be replaced by
    pointwise argument equalities.  Keeping this whitelist in the generator
    is important: right-side function decomposition is sound for every
    function symbol, whereas the converse implication used on the left
    requires injectivity. *)
Definition injective_constructorb (name : string) : bool :=
  String.eqb name "s" || String.eqb name "cons".

Definition left_function_equality_at_head
    (ds : definitions) (before_products : formula)
    (before_atoms : product) (left_term right_term : term)
    (after_atoms : product) (after_products rhs : formula)
    : option Cyclic.rule_instance.
Proof.
  destruct left_term as [n|x|left_name left_args];
    [exact None|exact None|].
  destruct right_term as [m|y|right_name right_args];
    [exact None|exact None|].
  destruct (string_dec left_name right_name) as [Hname | Hname];
    [subst right_name|exact None].
  destruct (injective_constructorb left_name) eqn:Hinjective;
    [|exact None].
  destruct (Nat.eq_dec (List.length left_args) (List.length right_args))
    as [Harity | Harity]; [|exact None].
  exact (Some (left_function_equality_rule ds before_products before_atoms
    left_name left_args right_args after_atoms after_products rhs Harity)).
Defined.

(** Scan every atom of the selected antecedent product.  Prefix accumulators
    preserve the exact list order so the resulting premise changes only the
    chosen equality. *)
Fixpoint find_left_function_equality_in_product
    (ds : definitions) (before_products : formula)
    (before_atoms remaining : product) (after_products rhs : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | a :: after_atoms =>
      match a with
      | Eq left_term right_term =>
          match left_function_equality_at_head ds before_products before_atoms
            left_term right_term after_atoms after_products rhs with
          | Some rule => Some rule
          | None => find_left_function_equality_in_product ds before_products
              (before_atoms ++ [a])%list after_atoms after_products rhs
          end
      | _ => find_left_function_equality_in_product ds before_products
          (before_atoms ++ [a])%list after_atoms after_products rhs
      end
  end.

(** The OCaml [bij_eqs] rule searches the complete left disjunction rather
    than only singleton antecedents.  This second scan mirrors that scope and
    rewrites one occurrence; repeated simplification handles later ones. *)
Fixpoint find_left_function_equality_in_formula
    (ds : definitions) (before_products remaining rhs : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | p :: after_products =>
      match find_left_function_equality_in_product ds before_products [] p
        after_products rhs with
      | Some rule => Some rule
      | None => find_left_function_equality_in_formula ds
          (before_products ++ [p])%list after_products rhs
      end
  end.

Definition left_function_equality_candidate (goal : judgment)
    : option Cyclic.rule_instance :=
  let q := goal.(judgment_sequent) in
  find_left_function_equality_in_formula goal.(judgment_definitions) []
    q.(antecedent) q.(succedent).

(** Recognize [f(xs) = f(ys)] and expose the verified pairwise-equality
    decomposition.  Constructor names and arities are checked here, so the
    rule kernel receives the exact propositional equalities it needs. *)
Definition right_function_equality_at_head
    (ds : definitions) (lhs before_products : formula)
    (before_atoms : product) (left_term right_term : term)
    (after_atoms : product) (after_products : formula)
    : option Cyclic.rule_instance.
Proof.
  destruct left_term as [n|x|left_name left_args];
    [exact None|exact None|].
  destruct right_term as [m|y|right_name right_args];
    [exact None|exact None|].
  destruct (string_dec left_name right_name) as [Hname | Hname];
    [subst right_name|exact None].
  destruct (Nat.eq_dec (List.length left_args) (List.length right_args))
    as [Harity | Harity]; [|exact None].
  exact (Some (right_function_equality_rule ds lhs before_products
    before_atoms left_name left_args right_args after_atoms after_products
    Harity)).
Defined.

Fixpoint find_right_function_equality_in_product
    (ds : definitions) (lhs before_products : formula)
    (before_atoms remaining : product) (after_products : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | a :: after_atoms =>
      match a with
      | Eq left_term right_term =>
          match right_function_equality_at_head ds lhs before_products
            before_atoms left_term right_term after_atoms after_products with
          | Some rule => Some rule
          | None => find_right_function_equality_in_product ds lhs
              before_products (before_atoms ++ [a])%list after_atoms
              after_products
          end
      | _ => find_right_function_equality_in_product ds lhs before_products
          (before_atoms ++ [a])%list after_atoms after_products
      end
  end.

Fixpoint find_right_function_equality_in_formula
    (ds : definitions) (lhs before_products remaining : formula)
    : option Cyclic.rule_instance :=
  match remaining with
  | [] => None
  | p :: after_products =>
      match find_right_function_equality_in_product ds lhs before_products
        [] p after_products with
      | Some rule => Some rule
      | None => find_right_function_equality_in_formula ds lhs
          (before_products ++ [p])%list after_products
      end
  end.

Definition right_function_equality_candidate (goal : judgment)
    : option Cyclic.rule_instance :=
  let q := goal.(judgment_sequent) in
  find_right_function_equality_in_formula goal.(judgment_definitions)
    q.(antecedent) [] q.(succedent).

Definition simplification_candidate (goal : judgment)
    : option Cyclic.rule_instance :=
  match goal.(judgment_sequent).(antecedent) with
  | [p] =>
      match find_reflexive_equality goal.(judgment_definitions) [] p
        goal.(judgment_sequent).(succedent) with
      | Some rule => Some rule
      | None =>
          match right_reflexive_equality_candidate goal with
          | Some rule => Some rule
          | None =>
              match find_left_equality_substitution
                goal.(judgment_definitions) [] p
                goal.(judgment_sequent).(succedent) with
              | Some rule => Some rule
              | None =>
                  match right_existential_substitution_candidate goal with
                  | Some rule => Some rule
                  | None =>
                      match right_discharge_candidate goal with
                      | Some rule => Some rule
                      | None =>
                          match left_function_equality_candidate goal with
                          | Some rule => Some rule
                          | None => right_function_equality_candidate goal
                          end
                      end
                  end
              end
          end
      end
  | _ =>
      match right_reflexive_equality_candidate goal with
      | Some rule => Some rule
      | None =>
          match right_existential_substitution_candidate goal with
          | Some rule => Some rule
          | None =>
              match left_function_equality_candidate goal with
              | Some rule => Some rule
              | None => right_function_equality_candidate goal
              end
          end
      end
  end.

(** ** Structural propositional rules *)

Definition left_disjunction_candidate (goal : judgment)
    : option Cyclic.rule_instance :=
  match goal.(judgment_sequent).(antecedent) with
  | first :: second :: tail =>
      Some (left_disjunction_rule goal.(judgment_definitions) first
        (second :: tail)
        goal.(judgment_sequent).(succedent))
  | _ => None
  end.

Definition right_conjunction_candidate (goal : judgment)
    : option Cyclic.rule_instance.
Proof.
  destruct goal as [ds [lhs rhs]]. simpl.
  destruct rhs as [|right_product alternatives]; [exact None|].
  destruct alternatives as [|other alternatives']; [|exact None].
  destruct right_product as [|a rest]; [exact None|].
  destruct rest as [|b tail]; [exact None|].
  destruct (formula_freeb lhs) eqn:Hlhs; [|exact None].
  destruct (atom_freeb a) eqn:Ha; [|exact None].
  destruct (product_freeb (b :: tail)) eqn:Hrest; [|exact None].
  exact (Some (right_conjunction_rule ds lhs a (b :: tail)
    Hlhs Ha Hrest)).
Defined.

(** ** Definition unfolding *)

Definition right_unfold_clause_candidate
    (standard_only : bool)
    (ds : definitions) (offset : nat) (lhs : formula)
    (before_products : formula) (before_atoms : product)
    (tag : option nat) (name : string) (args : list term)
    (after_atoms : product) (after_products : formula) (c : clause)
    : option Cyclic.rule_instance.
Proof.
  destruct (in_dec clause_eq_dec c (lookup_definition name ds))
    as [Hin | Hnotin]; [|exact None].
  destruct (match_terms c.(clause_head) args) as [s|] eqn:Hmatched.
  - destruct standard_only.
    + exact None.
    + exact (Some (matched_right_unfold_at_rule ds lhs before_products
        before_atoms tag name args after_atoms after_products c s Hin
        (match_terms_sound _ _ _ Hmatched))).
  - destruct standard_only; [|exact None].
    destruct (Nat.eq_dec (List.length args) (List.length c.(clause_head)))
      as [Harity | Harity]; [|exact None].
    exact (Some (standard_right_unfold_at_rule ds offset lhs before_products
      before_atoms tag name args after_atoms after_products c Hin Harity)).
Defined.

(** Visit every atom of one right-hand product.  [before_atoms] is an
    accumulator, so the source judgment reconstructed by
    [matched_right_unfold_at_rule] is definitionally the original one. *)
Fixpoint right_unfold_product_candidates
    (standard_only : bool)
    (ds : definitions) (offset : nat) (lhs before_products : formula)
    (before_atoms remaining : product) (after_products : formula)
    : list Cyclic.rule_instance :=
  match remaining with
  | [] => []
  | a :: after_atoms =>
      let later := right_unfold_product_candidates standard_only ds offset
        lhs before_products (before_atoms ++ [a])%list after_atoms
        after_products in
      match a with
      | Pred tag name args =>
          (List.concat (map
            (fun c => option_to_list
              (right_unfold_clause_candidate standard_only ds offset lhs
                before_products before_atoms tag name args after_atoms
                after_products c))
            (lookup_definition name ds)) ++ later)%list
      | _ => later
      end
  end.

(** Visit every product of the succedent formula.  This is the set-like scan
    performed by [ruf_formula] in the OCaml implementation; source order is
    retained to keep search deterministic. *)
Fixpoint right_unfold_formula_candidates
    (standard_only : bool) (ds : definitions) (offset : nat)
    (lhs before_products remaining : formula)
    : list Cyclic.rule_instance :=
  match remaining with
  | [] => []
  | p :: after_products =>
      (right_unfold_product_candidates standard_only ds offset lhs
         before_products [] p after_products ++
       right_unfold_formula_candidates standard_only ds offset lhs
         (before_products ++ [p])%list after_products)%list
  end.

Definition right_unfold_candidates (goal : judgment)
    : list Cyclic.rule_instance :=
  let ds := goal.(judgment_definitions) in
  let q := goal.(judgment_sequent) in
  right_unfold_formula_candidates false ds (fresh_variable_offset q)
    q.(antecedent) [] q.(succedent).

(** Equation-producing unfolding is kept as a separate, lower-priority
    family.  The OCaml unifier often turns these cases into an immediately
    useful substitution.  Until that exact composition is reproduced here,
    trying raw equation branches before induction causes the depth-first
    search to spend its bound on constraints such as [x = 0]. *)
Definition standard_right_unfold_candidates (goal : judgment)
    : list Cyclic.rule_instance :=
  let ds := goal.(judgment_definitions) in
  let q := goal.(judgment_sequent) in
  right_unfold_formula_candidates true ds (fresh_variable_offset q)
    q.(antecedent) [] q.(succedent).

Definition left_unfold_candidate (goal : judgment)
    : option Cyclic.rule_instance.
Proof.
  destruct goal as [ds q].
  destruct q as [lhs rhs]. simpl.
  destruct lhs as [|p alternatives]; [exact None|].
  destruct alternatives as [|other alternatives']; [|exact None].
  destruct p as [|a context]; [exact None|].
  destruct a as [u v | u v | tag name args]; [exact None|exact None|].
  destruct tag as [tag|]; [|exact None].
  set (offset := fresh_variable_offset (mk_sequent [Pred (Some tag) name args :: context] rhs)).
  set (fresh := fresh_tag (mk_sequent [Pred (Some tag) name args :: context] rhs)).
  destruct (Nat.eq_dec tag fresh) as [Heq | Htag]; [exact None|].
  destruct (product_belowb offset (Pred (Some tag) name args :: context))
    eqn:Hbelow; [|exact None].
  destruct (formula_freeb rhs) eqn:Hrhsfree; [|exact None].
  destruct (formula_belowb offset rhs) eqn:Hrhsbelow; [|exact None].
  exact (Some (left_unfold_rule ds offset tag fresh name args context rhs
    Htag Hbelow Hrhsfree Hrhsbelow)).
Defined.

(** Build the arbitrary-position wrapper for one selected tagged predicate.
    [Hbefore] below is not an optimization: it prevents duplicate source tags
    from making list rotation change which semantic rank is observed. *)
Definition left_unfold_at_candidate
    (ds : definitions) (rhs : formula) (offset fresh : nat)
    (before : product) (tag : nat) (name : string) (args : list term)
    (after : product) : option Cyclic.rule_instance.
Proof.
  destruct (in_dec Nat.eq_dec tag (product_tags before))
    as [Hduplicate | Hbefore]; [exact None|].
  destruct (Nat.eq_dec tag fresh) as [Heq | Htag]; [exact None|].
  destruct (product_belowb offset
    (Pred (Some tag) name args :: before ++ after)) eqn:Hbelow;
    [|exact None].
  destruct (formula_freeb rhs) eqn:Hrhsfree; [|exact None].
  destruct (formula_belowb offset rhs) eqn:Hrhsbelow; [|exact None].
  destruct before as [|first before'].
  - (* No rotation is needed at the head.  Keeping the original rule record
       avoids making the certificate checker reduce through a transport
       wrapper on the overwhelmingly common induction step. *)
    exact (Some (left_unfold_rule ds offset tag fresh name args after rhs
      Htag Hbelow Hrhsfree Hrhsbelow)).
  - exact (Some (left_unfold_at_rule ds offset (first :: before') tag fresh
      name args after rhs Hbefore Htag Hbelow Hrhsfree Hrhsbelow)).
Defined.

(** Scan all atoms of the unique antecedent product in source order.  This
    corresponds to [Prod.elements preds] in the OCaml left-rule generator. *)
Fixpoint left_unfold_product_candidates
    (ds : definitions) (rhs : formula) (offset fresh : nat)
    (before remaining : product) : list Cyclic.rule_instance :=
  match remaining with
  | [] => []
  | a :: after =>
      let later := left_unfold_product_candidates ds rhs offset fresh
        (before ++ [a])%list after in
      match a with
      | Pred (Some tag) name args =>
          (option_to_list (left_unfold_at_candidate ds rhs offset fresh
             before tag name args after) ++ later)%list
      | _ => later
      end
  end.

Definition left_unfold_candidates (goal : judgment)
    : list Cyclic.rule_instance :=
  match goal.(judgment_sequent).(antecedent) with
  | [p] =>
      let q := goal.(judgment_sequent) in
      left_unfold_product_candidates goal.(judgment_definitions)
        q.(succedent) (fresh_variable_offset q) (fresh_tag q) [] p
  | _ => []
  end.

(** Rule order mirrors the implemented portion of the OCaml priority list:
    propositional splitting, right unfolding, then left unfolding.  Backlinks
    require access to the current graph and are therefore generated by the
    graph-search module rather than here. *)
Definition generate_rules (goal : judgment) : list Cyclic.rule_instance :=
  (option_to_list (left_disjunction_candidate goal) ++
   option_to_list (right_conjunction_candidate goal) ++
   right_unfold_candidates goal ++
   (* Keep source order here.  Besides matching the deterministic clause/atom
      traversal of the port, this tends to follow the oldest trace tag.  A
      different order can find a structurally closed graph whose cycle does
      not satisfy global progress, forcing certification to reject it. *)
   left_unfold_candidates goal ++
   standard_right_unfold_candidates goal)%list.

(** Small computations demonstrate that the generators are syntax directed,
    rather than a table indexed by benchmark names. *)
Example generated_identity_closes_arbitrary_variable :
  match generate_axiom
    (mk_judgment []
      (mk_sequent [[Eq (Var (free_var 42)) (Var (free_var 42))]]
        [[Eq (Var (free_var 42)) (Var (free_var 42))]]))
  with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

(** Identity compares inductive predicates modulo their trace tags and may
    choose a strict-subset product from any RHS disjunct.  The surrounding
    equality demonstrates that non-predicate atoms are still checked too. *)
Example generated_identity_is_tag_insensitive_at_arbitrary_rhs_position :
  match generate_axiom
    (mk_judgment []
      (mk_sequent
        [[Pred (Some 4) "P" [Var (free_var 0)];
          Eq (Const 0) (Const 1);
          Pred None "Extra" []]]
        [[Pred None "Unrelated" []];
         [Pred (Some 91) "P" [Var (free_var 0)];
          Eq (Const 0) (Const 1)]]))
  with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

(** Ignoring tags must not accidentally make equality symmetric.  OCaml
    [Prod.mem] and the verified Boolean comparison both retain the ordered
    term pair for Eq/Neq atoms. *)
Example generated_identity_keeps_equality_orientation_exact :
  identity_candidate []
    [Eq (Var (free_var 0)) (Var (free_var 1))]
    [[Eq (Var (free_var 1)) (Var (free_var 0))]] = None.
Proof. vm_compute. reflexivity. Qed.

Example generated_left_disjunction_has_two_premises :
  match left_disjunction_candidate
    (mk_judgment [] (mk_sequent [[Eq zero zero]; [Neq zero (succ zero)]] [[]]))
  with
  | Some rule => Nat.eqb (List.length rule.(Cyclic.rule_premises)) 2
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example generated_reflexive_simplification_removes_only_the_selected_atom :
  match simplification_candidate
    (mk_judgment []
      (mk_sequent [[Neq zero (succ zero); Eq (Const 3) (Const 3)]] [[]]))
  with
  | Some rule =>
      judgment_eqb
        (hd {| Cyclic.premise_judgment :=
                 mk_judgment [] (mk_sequent [] []);
               Cyclic.premise_edge := empty_edge |}
          rule.(Cyclic.rule_premises)).(Cyclic.premise_judgment)
        (mk_judgment [] (mk_sequent [[Neq zero (succ zero)]] [[]]))
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** Regression for the witness-producing RHS simplifier.  The equality
    chooses existential variable 0 to be [7], and that choice is substituted
    into the remaining predicate argument. *)
Example generated_right_existential_substitution_installs_the_witness :
  match simplification_candidate
    (mk_judgment []
      (mk_sequent [[]]
        [[Eq (Var (existential_var 0)) (Const 7);
          Pred None "P" [Var (existential_var 0)]]])) with
  | Some rule =>
      match rule.(Cyclic.rule_premises) with
      | [premise] =>
          judgment_eqb premise.(Cyclic.premise_judgment)
            (mk_judgment []
              (mk_sequent [[]] [[Pred None "P" [Const 7]]]))
      | _ => false
      end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** The standard unfolding kernel emits [actual = fresh-existential].  The
    first simplification orients that equation and the second installs the
    witness, so both syntactic orientations reach the same premise. *)
Example generated_right_existential_substitution_orients_then_solves :
  match simplification_candidate
    (mk_judgment []
      (mk_sequent [[]]
        [[Eq (Const 7) (Var (existential_var 0));
          Pred None "P" [Var (existential_var 0)]]])) with
  | Some orient_rule =>
      match orient_rule.(Cyclic.rule_premises) with
      | [oriented] =>
          match simplification_candidate oriented.(Cyclic.premise_judgment) with
          | Some solve_rule =>
              match solve_rule.(Cyclic.rule_premises) with
              | [solved] =>
                  judgment_eqb solved.(Cyclic.premise_judgment)
                    (mk_judgment []
                      (mk_sequent [[]] [[Pred None "P" [Const 7]]]))
              | _ => false
              end
          | None => false
          end
      | _ => false
      end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** [bij_eqs] parity regression.  The selected [cons = cons] equality is in
    the middle of the second antecedent product.  Decomposition must preserve
    both surrounding tagged predicates, the untouched first product, the RHS,
    and the left-to-right order of the two generated argument equations. *)
Example generated_left_constructor_injectivity_decomposes_middle_cons :
  match simplification_candidate
    (mk_judgment []
      (mk_sequent
        [[Pred (Some 3) "Untouched" []];
         [Pred (Some 4) "KeepL" [];
          Eq (cons (Var (free_var 0)) (Var (free_var 1)))
             (cons (Var (free_var 2)) (Var (free_var 3)));
          Pred (Some 5) "KeepR" []]]
        [[Pred None "Goal" []]])) with
  | Some rule =>
      match rule.(Cyclic.rule_premises) with
      | [premise] =>
          judgment_eqb premise.(Cyclic.premise_judgment)
            (mk_judgment []
              (mk_sequent
                [[Pred (Some 3) "Untouched" []];
                 [Pred (Some 4) "KeepL" [];
                  Eq (Var (free_var 0)) (Var (free_var 2));
                  Eq (Var (free_var 1)) (Var (free_var 3));
                  Pred (Some 5) "KeepR" []]]
                [[Pred None "Goal" []]]))
      | _ => false
      end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** Same-headed symbols are not automatically assumed injective on the left.
    Only the original prover's explicit [s]/[cons] whitelist may use the
    converse direction of constructor congruence. *)
Example generated_left_constructor_injectivity_rejects_unknown_function :
  left_function_equality_candidate
    (mk_judgment []
      (mk_sequent
        [[Eq (Fun "f" [Var (free_var 0)])
             (Fun "f" [Var (free_var 1)])]] [[]])) = None.
Proof. vm_compute. reflexivity. Qed.

(** The OCaml implementation accidentally raises [Invalid_argument] on a
    malformed known constructor with unequal arities.  The verified generator
    rejects that input safely because the semantic decomposition theorem
    requires equal list lengths. *)
Example generated_left_constructor_injectivity_rejects_arity_mismatch :
  left_function_equality_candidate
    (mk_judgment []
      (mk_sequent
        [[Eq (Fun "cons" [Var (free_var 0)])
             (Fun "cons" [Var (free_var 1); Var (free_var 2)])]] [[]])) = None.
Proof. vm_compute. reflexivity. Qed.

(** When both sides contain decomposable function equalities, the injective
    LHS rule is selected first.  This records the ordering of OCaml
    [bij_eqs] before [func_eqs] and prevents later refactoring from silently
    changing the search tree. *)
Example generated_left_constructor_injectivity_precedes_right_function :
  match simplification_candidate
    (mk_judgment []
      (mk_sequent
        [[Eq (succ (Var (free_var 0))) (succ (Var (free_var 1)))]]
        [[Eq (Fun "f" [Const 1]) (Fun "f" [Const 2])]])) with
  | Some rule =>
      match rule.(Cyclic.rule_premises) with
      | [premise] =>
          judgment_eqb premise.(Cyclic.premise_judgment)
            (mk_judgment []
              (mk_sequent
                [[Eq (Var (free_var 0)) (Var (free_var 1))]]
                [[Eq (Fun "f" [Const 1]) (Fun "f" [Const 2])]]))
      | _ => false
      end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** [simpl_rhs] parity regression.  The antecedent predicate and selected
    succedent predicate have different trace tags but identical semantic
    content.  The selected occurrence lies in the middle of the second RHS
    product, so this also checks both prefix accumulators. *)
Example generated_right_discharge_ignores_predicate_tags_and_keeps_context :
  match simplification_candidate
    (mk_judgment []
      (mk_sequent
        [[Pred (Some 7) "P" [Var (free_var 0)]]]
        [[Pred None "OtherAlternative" []];
         [Neq (Const 0) (Const 1);
          Pred (Some 99) "P" [Var (free_var 0)];
          Pred None "Keep" []]])) with
  | Some rule =>
      match rule.(Cyclic.rule_premises) with
      | [premise] =>
          judgment_eqb premise.(Cyclic.premise_judgment)
            (mk_judgment []
              (mk_sequent
                [[Pred (Some 7) "P" [Var (free_var 0)]]]
                [[Pred None "OtherAlternative" []];
                 [Neq (Const 0) (Const 1); Pred None "Keep" []]]))
      | _ => false
      end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** RHS discharge precedes constructor injectivity, as in the original
    simplifier sequence.  The known [cons] equality remains untouched while
    the supplied predicate is removed first. *)
Example generated_right_discharge_precedes_left_constructor_injectivity :
  match simplification_candidate
    (mk_judgment []
      (mk_sequent
        [[Eq (cons (Const 1) (Const 2)) (cons (Const 3) (Const 4));
          Pred (Some 1) "P" []]]
        [[Pred (Some 2) "P" []; Pred None "Goal" []]])) with
  | Some rule =>
      match rule.(Cyclic.rule_premises) with
      | [premise] =>
          judgment_eqb premise.(Cyclic.premise_judgment)
            (mk_judgment []
              (mk_sequent
                [[Eq (cons (Const 1) (Const 2)) (cons (Const 3) (Const 4));
                  Pred (Some 1) "P" []]]
                [[Pred None "Goal" []]]))
      | _ => false
      end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** This negative test protects the valuation side condition.  An
    existential variable may receive a different RHS witness value, so a
    syntactic antecedent match alone does not justify discharge. *)
Example generated_right_discharge_rejects_existential_atom :
  right_discharge_candidate
    (mk_judgment []
      (mk_sequent
        [[Pred None "P" [Var (existential_var 0)]]]
        [[Pred None "P" [Var (existential_var 0)]]])) = None.
Proof. vm_compute. reflexivity. Qed.
