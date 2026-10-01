From Stdlib Require Import List Bool Arith Lia String.

From CyclistRocq.FirstOrder Require Import Syntax Semantics.

Import ListNotations.
Open Scope string_scope.

(** * Executable infrastructure used by proof search

    The OCaml prover represents products and formulae by finite sets.  The
    reified Rocq syntax deliberately uses lists because lists are convenient
    graph labels and preserve the source order of clauses.  Search must not,
    however, confuse list order with logical meaning.  This file supplies the
    set-style operations used by matching, together with semantic lemmas that
    justify normalising a user goal before search begins.

    The second half implements a small, directional first-order matcher.  A
    returned substitution is checked syntactically before it is exposed.  This
    "compute, then verify" pattern keeps the trusted proof small: even if the
    heuristic matcher is later changed, [match_terms_sound] continues to be
    the gate through which its result must pass. *)

(** ** Products and formulae as finite sets *)

Definition normalize_product (p : product) : product :=
  nodup atom_eq_dec p.

Definition normalize_formula (f : formula) : formula :=
  nodup product_eq_dec (map normalize_product f).

Definition normalize_sequent (q : sequent) : sequent :=
  mk_sequent (normalize_formula q.(antecedent))
    (normalize_formula q.(succedent)).

Definition normalize_judgment (j : judgment) : judgment :=
  mk_judgment j.(judgment_definitions)
    (normalize_sequent j.(judgment_sequent)).

Lemma product_holds_forall i rho p :
  product_holds i rho p <->
  forall a, In a p -> atom_holds i rho a.
Proof.
  induction p as [|a p IH]; simpl.
  - split; [intros _ x H; contradiction|tauto].
  - rewrite IH. split.
    + intros [Ha Hp] x [-> | Hin]; auto.
    + intro Hall. split.
      * apply Hall. now left.
      * intros x Hin. apply Hall. now right.
Qed.

Lemma normalize_product_holds i rho p :
  product_holds i rho (normalize_product p) <-> product_holds i rho p.
Proof.
  unfold normalize_product. rewrite !product_holds_forall.
  setoid_rewrite nodup_In. tauto.
Qed.

Lemma normalize_formula_holds i rho f :
  formula_holds i rho (normalize_formula f) <-> formula_holds i rho f.
Proof.
  unfold normalize_formula, formula_holds.
  split.
  - intros [q [Hq Hholds]].
    apply nodup_In in Hq. apply in_map_iff in Hq.
    destruct Hq as [p [<- Hin]]. exists p. split; [exact Hin|].
    now apply (proj1 (normalize_product_holds i rho p)).
  - intros [p [Hin Hholds]]. exists (normalize_product p). split.
    + apply nodup_In, in_map. exact Hin.
    + now apply (proj2 (normalize_product_holds i rho p)).
Qed.

Lemma normalize_right_holds i rho f :
  right_holds i rho (normalize_formula f) <-> right_holds i rho f.
Proof.
  unfold right_holds. split; intros [witness H]; exists witness.
  - now apply (proj1 (normalize_formula_holds i _ f)).
  - now apply (proj2 (normalize_formula_holds i _ f)).
Qed.

Lemma normalize_sequent_holds ds q w :
  sequent_holds ds (normalize_sequent q) w <-> sequent_holds ds q w.
Proof.
  destruct w as [i rho]. unfold sequent_holds, normalize_sequent, mk_sequent;
    simpl. split; intros H Hmodel Hlhs.
  - apply (proj1 (normalize_right_holds i rho q.(succedent))).
    apply H; [exact Hmodel|].
    now apply (proj2 (normalize_formula_holds i rho q.(antecedent))).
  - apply (proj2 (normalize_right_holds i rho q.(succedent))).
    apply H; [exact Hmodel|].
    now apply (proj1 (normalize_formula_holds i rho q.(antecedent))).
Qed.

Lemma normalize_judgment_denote j w :
  denote (normalize_judgment j) w <-> denote j w.
Proof.
  destruct j as [ds q]. apply normalize_sequent_holds.
Qed.

Lemma normalize_judgment_valid j :
  Cyclic.Valid (normalize_judgment j) <-> Cyclic.Valid j.
Proof.
  split; intros H w; specialize (H w).
  - now apply (proj1 (normalize_judgment_denote j w)).
  - now apply (proj2 (normalize_judgment_denote j w)).
Qed.

(** Boolean set equality is used for heuristic matching.  It deliberately
    ignores multiplicity and order but still compares predicate tags.  Search
    uses the tag-insensitive operations from [Syntax] only when looking for a
    backlink companion. *)
Definition product_set_eqb (p q : product) : bool :=
  product_subsetb p q && product_subsetb q p.

Lemma product_set_eqb_spec p q :
  product_set_eqb p q = true <->
  forall a, In a p <-> In a q.
Proof.
  unfold product_set_eqb. rewrite Bool.andb_true_iff.
  rewrite !product_subsetb_spec. firstorder.
Qed.

Definition product_mem_setb (p : product) (f : formula) : bool :=
  existsb (product_set_eqb p) f.

Definition formula_subsetb (small big : formula) : bool :=
  forallb (fun p => product_mem_setb p big) small.

Definition formula_set_eqb (f g : formula) : bool :=
  formula_subsetb f g && formula_subsetb g f.

Lemma product_mem_setb_spec p f :
  product_mem_setb p f = true <->
  exists q, In q f /\ forall a, In a p <-> In a q.
Proof.
  unfold product_mem_setb. rewrite existsb_exists.
  setoid_rewrite product_set_eqb_spec. firstorder.
Qed.

(** ** Variables, fresh names, and directional matching *)

Fixpoint term_variables (t : term) : list variable :=
  match t with
  | Const _ => []
  | Var x => [x]
  | Fun _ xs => List.concat (map term_variables xs)
  end.

Definition atom_variables (a : atom) : list variable :=
  match a with
  | Eq x y | Neq x y => (term_variables x ++ term_variables y)%list
  | Pred _ _ xs => List.concat (map term_variables xs)
  end.

Definition product_variables (p : product) : list variable :=
  nodup variable_eq_dec (List.concat (map atom_variables p)).

Definition formula_variables (f : formula) : list variable :=
  nodup variable_eq_dec (List.concat (map product_variables f)).

Definition sequent_variables (q : sequent) : list variable :=
  nodup variable_eq_dec
    (formula_variables q.(antecedent) ++ formula_variables q.(succedent))%list.

Definition is_free_variable (x : variable) : bool :=
  match x.(variable_kind) with Free => true | Existential => false end.

Definition is_existential_variable (x : variable) : bool :=
  match x.(variable_kind) with Free => false | Existential => true end.

Definition fresh_free_variable (q : sequent) : variable :=
  free_var (fresh_variable_offset q).

Definition fresh_existential_variable (q : sequent) : variable :=
  existential_var (fresh_variable_offset q).

Definition term_is_existential_variable (t : term) : bool :=
  match t with
  | Var x => is_existential_variable x
  | _ => false
  end.

Definition substitution_range_mem (t : term) (s : substitution) : bool :=
  existsb (fun binding => term_eqb t (snd binding)) s.

(** Add one directional binding.  Free variables may match any target term.
    As in the OCaml implementation, an existential pattern variable may only
    be renamed to a fresh existential variable; this prevents the matcher from
    silently capturing a witness already used by another binding. *)
Definition add_match_binding
    (x : variable) (target : term) (s : substitution) : option substitution :=
  match lookup_substitution s x with
  | Some old => if term_eqb old target then Some s else None
  | None =>
      match x.(variable_kind) with
      | Free => Some ((x, target) :: s)
      | Existential =>
          if term_is_existential_variable target &&
             negb (substitution_range_mem target s)
          then Some ((x, target) :: s)
          else None
      end
  end.

Definition zip_terms (xs ys : list term) : option (list (term * term)) :=
  if Nat.eqb (List.length xs) (List.length ys)
  then Some (combine xs ys)
  else None.

(** [match_equations] processes a finite work list of pattern/target pairs.
    The fuel counts pattern nodes.  Expanding a function removes its root and
    inserts only its strict subterms, so [equation_work_size] is sufficient
    fuel; using explicit fuel keeps the executable definition transparent to
    Rocq's termination checker. *)
Definition equation_work_size (work : list (term * term)) : nat :=
  fold_right (fun pair n => term_size (fst pair) + n) 0 work.

Fixpoint match_equations
    (fuel : nat) (work : list (term * term)) (s : substitution)
    : option substitution :=
  match fuel with
  | 0 => match work with [] => Some s | _ => None end
  | S fuel' =>
      match work with
      | [] => Some s
      | (pattern, target) :: rest =>
          match pattern with
          | Var x =>
              match add_match_binding x target s with
              | Some s' => match_equations fuel' rest s'
              | None => None
              end
          | Const n =>
              match target with
              | Const m =>
                  if Nat.eqb n m then match_equations fuel' rest s else None
              | _ => None
              end
          | Fun name args =>
              match target with
              | Fun name' args' =>
                  if String.eqb name name' then
                    match zip_terms args args' with
                    | Some pairs => match_equations fuel' (pairs ++ rest) s
                    | None => None
                    end
                  else None
              | _ => None
              end
          end
      end
  end.

Definition raw_match_terms (patterns targets : list term)
    : option substitution :=
  match zip_terms patterns targets with
  | Some work => match_equations (S (equation_work_size work)) work []
  | None => None
  end.

(** Never trust the heuristic matcher directly.  Reapplying the candidate
    substitution and checking syntactic equality gives a tiny reflection
    theorem, [match_terms_sound], which is what rule construction consumes. *)
Definition match_terms (patterns targets : list term)
    : option substitution :=
  match raw_match_terms patterns targets with
  | Some s =>
      if terms_eqb (map (subst_term s) patterns) targets then Some s else None
  | None => None
  end.

Lemma match_terms_sound patterns targets s :
  match_terms patterns targets = Some s ->
  map (subst_term s) patterns = targets.
Proof.
  unfold match_terms. destruct (raw_match_terms patterns targets) as [candidate|]
    eqn:Hcandidate; [|discriminate].
  destruct (terms_eqb (map (subst_term candidate) patterns) targets)
    eqn:Hcheck; [|discriminate].
  intro H. inversion H; subst candidate. now apply terms_eqb_spec.
Qed.

Example match_successor_pattern :
  match_terms [Fun "s" [Var (free_var 0)]] [Fun "s" [Const 7]] =
  Some [((free_var 0), Const 7)].
Proof. vm_compute. reflexivity. Qed.

Example match_rejects_constructor_clash :
  match_terms [Fun "s" [Var (free_var 0)]] [Const 7] = None.
Proof. vm_compute. reflexivity. Qed.

(** ** Substitution composition and checked symmetric unification

    Directional matching is enough when a definition head is treated purely
    as a pattern.  The original prover also compares sequents in situations
    where variables occur on both sides (most notably backlink discovery), so
    it additionally needs symmetric first-order unification.

    [compose_substitution newer older] represents "apply [older], then apply
    [newer]".  Existing ranges are updated, while bindings for variables not
    in [older]'s domain remain available through the appended [newer] list.
    Association-list lookup takes the first binding, hence this ordering is
    intentional. *)
Definition substitution_domain_mem (x : variable) (s : substitution) : bool :=
  existsb (fun binding => variable_eqb x (fst binding)) s.

Definition compose_substitution
    (newer older : substitution) : substitution :=
  (map (fun binding =>
          (fst binding, subst_term newer (snd binding))) older ++
   filter (fun binding => negb (substitution_domain_mem (fst binding) older))
     newer)%list.

Fixpoint term_occursb (x : variable) (t : term) : bool :=
  match t with
  | Const _ => false
  | Var y => variable_eqb x y
  | Fun _ args => existsb (term_occursb x) args
  end.

Definition subst_equation (one : substitution) (equation : term * term)
    : term * term :=
  (subst_term one (fst equation), subst_term one (snd equation)).

(** Extend a solved substitution with [x := t].  Applying the new binding to
    every old range is essential: after solving [x = y] and later [y = 0],
    the final binding for [x] must also read [0]. *)
Definition extend_unifier
    (x : variable) (t : term) (s : substitution) : substitution :=
  (x, t) :: map (fun binding =>
    (fst binding, subst_term [(x, t)] (snd binding))) s.

(** One work-list unifier.  The occurs check prevents cyclic substitutions
    such as [x := s(x)].  Both kinds of variables may be solved here; callers
    that need the stricter existential-renaming discipline use [match_terms]
    instead. *)
Fixpoint unify_equations
    (fuel : nat) (work : list (term * term)) (s : substitution)
    : option substitution :=
  match fuel with
  | 0 => match work with [] => Some s | _ => None end
  | S fuel' =>
      match work with
      | [] => Some s
      | (lhs, rhs) :: rest =>
          if term_eqb lhs rhs then unify_equations fuel' rest s else
          match lhs, rhs with
          | Var x, t =>
              if term_occursb x t then None else
              let one := [(x, t)] in
              unify_equations fuel' (map (subst_equation one) rest)
                (extend_unifier x t s)
          | t, Var x =>
              if term_occursb x t then None else
              let one := [(x, t)] in
              unify_equations fuel' (map (subst_equation one) rest)
                (extend_unifier x t s)
          | Const _, Const _ => None
          | Fun f xs, Fun g ys =>
              if String.eqb f g then
                match zip_terms xs ys with
                | Some pairs => unify_equations fuel' (pairs ++ rest) s
                | None => None
                end
              else None
          | _, _ => None
          end
      end
  end.

(** This deliberately generous bound is not a completeness theorem.  It is a
    total search budget large enough for the small terms produced by rule
    generation.  Exhaustion yields [None], which means only "not found". *)
Definition unification_fuel (work : list (term * term)) : nat :=
  let size := fold_right
    (fun equation n => term_size (fst equation) + term_size (snd equation) + n)
    0 work in
  S (size * S size).

Definition raw_unify_terms (lhs rhs : list term) : option substitution :=
  match zip_terms lhs rhs with
  | Some work => unify_equations (unification_fuel work) work []
  | None => None
  end.

(** As with directional matching, this final equality check is the trusted
    gate.  [unify_terms_sound] consequently depends only on Boolean equality
    reflection, not on a large invariant for the heuristic work-list code. *)
Definition unify_terms (lhs rhs : list term) : option substitution :=
  match raw_unify_terms lhs rhs with
  | Some s =>
      if terms_eqb (map (subst_term s) lhs) (map (subst_term s) rhs)
      then Some s
      else None
  | None => None
  end.

Lemma unify_terms_sound lhs rhs s :
  unify_terms lhs rhs = Some s ->
  map (subst_term s) lhs = map (subst_term s) rhs.
Proof.
  unfold unify_terms.
  destruct (raw_unify_terms lhs rhs) as [candidate|] eqn:Hcandidate;
    [|discriminate].
  destruct (terms_eqb (map (subst_term candidate) lhs)
    (map (subst_term candidate) rhs)) eqn:Hcheck; [|discriminate].
  intro H. inversion H; subst candidate. now apply terms_eqb_spec.
Qed.

Example unification_propagates_later_bindings :
  unify_terms [Var (free_var 0); Var (free_var 1)]
    [Var (free_var 1); Const 0] =
  Some [((free_var 1), Const 0); ((free_var 0), Const 0)].
Proof. vm_compute. reflexivity. Qed.

Example unification_occurs_check :
  unify_terms [Var (free_var 0)] [succ (Var (free_var 0))] = None.
Proof. vm_compute. reflexivity. Qed.
