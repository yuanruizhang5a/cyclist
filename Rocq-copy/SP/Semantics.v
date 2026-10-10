From Stdlib Require Import List Bool Arith Lia String Permutation.

From CyclistRocq.Cyclic Require Import Framework.
From CyclistRocq.SP Require Import Syntax.

Import ListNotations.
Open Scope string_scope.

(** * A finite-heap, ranked semantics

    Locations are natural numbers and [0] is the distinguished [nil].  A
    concrete heap is a finite association list.  Worlds carry a proof that no
    address occurs twice, so the list represents a finite partial map. *)
Definition location : Type := nat.
Definition nil_location : location := 0.
Definition cell : Type := (location * list location)%type.
Definition concrete_heap : Type := list cell.

Definition heap_wf (h : concrete_heap) : Prop := NoDup (map fst h).

Definition heap_disjoint (left right : concrete_heap) : Prop :=
  forall address fields fields',
    In (address, fields) left -> In (address, fields') right -> False.

Definition heap_join
    (left right whole : concrete_heap) : Prop :=
  heap_disjoint left right /\ Permutation (left ++ right) whole.

Lemma heap_disjoint_sym left right :
  heap_disjoint left right -> heap_disjoint right left.
Proof.
  intros H address fields fields' Hr Hl.
  exact (H address fields' fields Hl Hr).
Qed.

Lemma heap_join_empty_left h : heap_join [] h h.
Proof.
  split.
  - intros address fields fields' H; inversion H.
  - simpl. apply Permutation_refl.
Qed.

(** Free variables are supplied by a world.  Existential variables are read
    from a witness valuation local to one formula satisfaction derivation. *)
Definition valuation : Type := variable -> location.
Definition tag_valuation : Type := nat -> nat.

Definition merge_valuation (base witness : valuation) : valuation :=
  fun x =>
    match x.(variable_kind) with
    | Free => base x
    | Existential => witness x
    end.

Definition merge_tag_valuation
    (base witness : tag_valuation) (tag : trace_tag) : nat :=
  match tag with
  | Anonymous => 0
  | FreeTag n => base n
  | ExistentialTag n => witness n
  end.

Definition eval_term (rho : valuation) (t : term) : location :=
  match t with Nil => nil_location | Var x => rho x end.

Definition eval_terms (rho : valuation) (ts : list term) : list location :=
  map (eval_term rho) ts.

Definition pure_holds (rho : valuation) (a : pure_atom) : Prop :=
  match a with
  | Equal x y => eval_term rho x = eval_term rho y
  | Disequal x y => eval_term rho x <> eval_term rho y
  end.

Fixpoint pures_hold (rho : valuation) (ps : list pure_atom) : Prop :=
  match ps with
  | [] => True
  | p :: rest => pure_holds rho p /\ pures_hold rho rest
  end.

Definition points_to_holds
    (rho : valuation) (p : points_to) (h : concrete_heap) : Prop :=
  eval_term rho p.(points_address) <> nil_location /\
  h = [(eval_term rho p.(points_address), eval_terms rho p.(points_fields))].

(** The following generic spatial semantics is parameterized by the meaning
    of inductive predicates.  It is used both while defining ranked predicates
    and when interpreting a user formula. *)
Inductive spatial_atom : Type :=
| CellAtom (p : points_to)
| PredicateAtom (p : tagged_predicate).

Definition heap_spatial_atoms (h : symheap) : list spatial_atom :=
  map CellAtom h.(heap_points) ++ map PredicateAtom h.(heap_predicates).

Definition predicate_semantics : Type :=
  tagged_predicate -> concrete_heap -> Prop.

Definition spatial_atom_holds_with
    (pred_holds : predicate_semantics) (rho : valuation)
    (a : spatial_atom) (h : concrete_heap) : Prop :=
  match a with
  | CellAtom p => points_to_holds rho p h
  | PredicateAtom p => pred_holds p h
  end.

Fixpoint spatial_holds_with
    (pred_holds : predicate_semantics) (rho : valuation)
    (atoms : list spatial_atom) (h : concrete_heap) : Prop :=
  match atoms with
  | [] => h = []
  | atom :: rest =>
      exists owned frame,
        heap_join owned frame h /\
        spatial_atom_holds_with pred_holds rho atom owned /\
        spatial_holds_with pred_holds rho rest frame
  end.

Definition symheap_holds_with
    (pred_holds : predicate_semantics) (rho : valuation)
    (h : concrete_heap) (sh : symheap) : Prop :=
  pures_hold rho sh.(heap_pure) /\
  spatial_holds_with pred_holds rho (heap_spatial_atoms sh) h.

(** [predicate_holds_rank ds r P xs h] means that [P(xs)] owns exactly [h]
    and has an unfolding derivation of positive height [r].  At [S n], a
    clause body may use predicates of any rank at most [n].  The explicit
    syntactic substitution is equivalent to ordinary clause instantiation,
    but is especially convenient for a proof-producing executable generator. *)
Fixpoint predicate_holds_rank
    (ds : definitions) (rank : nat) (name : string)
    (arguments : list location) (h : concrete_heap) : Prop :=
  match rank with
  | 0 => False
  | S smaller =>
      exists c s rho,
        In c (lookup_definition name ds) /\
        eval_terms rho (map (subst_term s) c.(clause_head)) = arguments /\
        symheap_holds_with
          (fun p owned =>
             exists child_rank,
               child_rank <= smaller /\
               predicate_holds_rank ds child_rank p.(predicate_name)
                 (eval_terms rho p.(predicate_arguments)) owned)
          rho h (subst_heap s c.(clause_body))
  end.

Definition tag_bounds_rank
    (tau : trace_tag -> nat) (tag : trace_tag) (rank : nat) : Prop :=
  match tag with
  | Anonymous => True
  | _ => rank <= tau tag
  end.

Definition formula_predicate_holds
    (ds : definitions) (rho : valuation) (tau : trace_tag -> nat)
    (p : tagged_predicate) (h : concrete_heap) : Prop :=
  exists rank,
    predicate_holds_rank ds rank p.(predicate_name)
      (eval_terms rho p.(predicate_arguments)) h /\
    tag_bounds_rank tau p.(predicate_tag) rank.

Definition constraint_holds
    (tau : trace_tag -> nat) (c : ordinal_constraint) : Prop :=
  match c.(constraint_order) with
  | Strict => tau c.(constraint_left) < tau c.(constraint_right)
  | NonStrict => tau c.(constraint_left) <= tau c.(constraint_right)
  end.

Fixpoint constraints_hold
    (tau : trace_tag -> nat) (cs : list ordinal_constraint) : Prop :=
  match cs with
  | [] => True
  | c :: rest => constraint_holds tau c /\ constraints_hold tau rest
  end.

(** Existential variable and tag witnesses are chosen once per formula, then
    shared by its constraints and selected disjunct. *)
Definition formula_holds
    (ds : definitions) (base_rho : valuation) (base_tau : tag_valuation)
    (h : concrete_heap) (f : formula) : Prop :=
  exists witness_rho witness_tau sh,
    In sh f.(formula_heaps) /\
    let rho := merge_valuation base_rho witness_rho in
    let tau := merge_tag_valuation base_tau witness_tau in
    constraints_hold tau f.(formula_constraints) /\
    symheap_holds_with (formula_predicate_holds ds rho tau) rho h sh.

Record world : Type := {
  world_variables : valuation;
  world_tags : tag_valuation;
  world_heap : concrete_heap;
  world_heap_wf : heap_wf world_heap
}.

Definition sequent_holds (ds : definitions) (q : sequent) (w : world) : Prop :=
  formula_holds ds w.(world_variables) w.(world_tags) w.(world_heap)
    q.(antecedent) ->
  formula_holds ds w.(world_variables) w.(world_tags) w.(world_heap)
    q.(succedent).

Definition denote (j : judgment) (w : world) : Prop :=
  sequent_holds j.(judgment_definitions) j.(judgment_sequent) w.

(** Framework trace tags are free antecedent tag identifiers.  Their semantic
    rank is the ordinal assignment stored in the world. *)
Definition rank_of_tag (j : judgment) (w : world) (tag : nat) : nat :=
  w.(world_tags) tag.

Module SeparationLogicTheory <: Framework.THEORY.
  Definition World := world.
  Definition Judgment := judgment.
  Definition Sequent := World -> Prop.
  Definition judgment_eqb := judgment_eqb.
  Definition backlink_eqb := backlink_eqb.
  Definition denote := denote.
  Definition tags := judgment_tags.
  Definition rank := rank_of_tag.
End SeparationLogicTheory.

Module Cyclic := Framework.Make SeparationLogicTheory.

(** Basic semantic facts used by rules and regression tests. *)
Lemma pures_hold_in rho ps a :
  pures_hold rho ps -> In a ps -> pure_holds rho a.
Proof.
  revert a. induction ps as [|p ps IH]; intros a Hholds Hin; simpl in *.
  - contradiction.
  - destruct Hholds as [Hp Hps]. destruct Hin as [-> | Hin]; auto.
Qed.

Lemma reflexive_disequality_false rho t :
  ~ pure_holds rho (Disequal t t).
Proof. simpl. intuition. Qed.

Lemma points_to_owns_exactly_one rho p h :
  points_to_holds rho p h -> List.length h = 1.
Proof. intros [_ ->]. reflexivity. Qed.

Lemma points_to_never_owns_nil rho fields h :
  points_to_holds rho (pto Nil fields) h -> False.
Proof. intros [H _]. apply H. reflexivity. Qed.

Lemma ranked_unfolding ds rank name args h :
  predicate_holds_rank ds (S rank) name args h ->
  exists c s rho,
    In c (lookup_definition name ds) /\
    eval_terms rho (map (subst_term s) c.(clause_head)) = args /\
    symheap_holds_with
      (fun p owned =>
         exists child_rank,
           child_rank <= rank /\
           predicate_holds_rank ds child_rank p.(predicate_name)
             (eval_terms rho p.(predicate_arguments)) owned)
      rho h (subst_heap s c.(clause_body)).
Proof. exact (fun H => H). Qed.

Lemma constraint_strict_unit tau a b :
  constraint_holds tau (lt_constraint a b) <-> tau a < tau b.
Proof. reflexivity. Qed.

(** A concrete existential-witness example: [exists x', x'=nil * emp]
    holds in the empty heap under every free-variable environment. *)
Definition zero_valuation : valuation := fun _ => nil_location.
Definition zero_tags : tag_valuation := fun _ => 0.

Definition existential_emp_formula : formula :=
  singleton_formula
    (mk_heap [Equal (Var (existential_var 0)) Nil] [] []).

Lemma existential_emp_has_witness ds rho tau :
  formula_holds ds rho tau [] existential_emp_formula.
Proof.
  exists zero_valuation, zero_tags,
    (mk_heap [Equal (Var (existential_var 0)) Nil] [] []).
  simpl. repeat split; auto.
Qed.

Example empty_heap_is_well_formed : heap_wf [].
Proof. constructor. Qed.
