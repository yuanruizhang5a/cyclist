From Stdlib Require Import List Bool Arith ZArith String.
From Stdlib Require Import Sorting.Permutation.
From CyclistRocq.FirstOrderNew Require Export Compiler Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(** This is syntax-derived scheduling, not unification or semantic evidence.
    A rigid RHS head confronted with a Free argument suggests a left induction
    variable. Exist arguments are potential RHS witnesses and never blockers.
    A known structural mismatch invalidates the WHOLE clause's blocker list. *)
Definition rhs_blocker := (variable * nat)%type.
Fixpoint head_blockers_at depth (pattern actual : term) {struct pattern}
    : option (list rhs_blocker) :=
  match pattern with
  | Var _ => Some []
  | Const c => match actual with
    | Var (Free n) => Some [(Free n,depth)]
    | Var (Exist _) => Some []
    | Const c' => if Z.eqb c c' then Some [] else None
    | Fun _ _ => None end
  | Fun f ps => match actual with
    | Var (Free n) => Some [(Free n,depth)]
    | Var (Exist _) => Some []
    | Const _ => None
    | Fun g us => if String.eqb f g then
        (fix walk (xs ys : list term) : option (list rhs_blocker) := match xs,ys with
          | [],[] => Some []
          | p::xs',u::ys' => match head_blockers_at (S depth) p u,walk xs' ys' with
            | Some bs,Some rest => Some (bs ++ rest) | _,_ => None end
          | _,_ => None end) ps us
        else None end
  end.
Fixpoint head_list_blockers patterns actuals : option (list rhs_blocker) := match patterns,actuals with
  | [],[] => Some []
  | p::ps,a::args => match head_blockers_at 0 p a,head_list_blockers ps args with
    | Some bs,Some rest => Some (bs ++ rest) | _,_ => None end
  | _,_ => None end.
Definition atom_rhs_blockers d a := match a with
  | Pred _ name args => flat_map (fun c =>
      if String.eqb c.(clause_name) name && Nat.eqb (List.length c.(head)) (List.length args) then
        match head_list_blockers c.(head) args with Some bs => bs | None => [] end
      else []) d
  | _ => [] end.
Definition rhs_blockers d j := flat_map (flat_map (atom_rhs_blockers d)) j.(succedent).

Fixpoint relevance_term_size t := match t with
  | Const _ | Var _ => 1
  | Fun _ args => S (fold_right Nat.add 0 (map relevance_term_size args)) end.
Definition left_principal j rd := match rd with
  | RDLeftUnfoldAt pi ai _ => match nth_error j.(antecedent) pi with
    | Some p => nth_error p ai | None => None end
  | RDLeftUnfold ai _ => match j.(antecedent) with
    | [p] => nth_error p ai | _ => None end
  | _ => None end.
Fixpoint minimum_blocker_depth (bs : list rhs_blocker) := match bs with
  | [] => None
  | (_,depth)::rest => Some (match minimum_blocker_depth rest with
      | None => depth | Some other => Nat.min depth other end) end.
Record relevance_score := {
  blocker_depth : option nat;
  blocker_occurrences : nat;
  principal_term_size : nat
}.
Definition score_left_proposal blockers j p :=
  match left_principal j p.(proposal_descriptor) with
  | Some (Pred _ _ args) =>
    let variables := List.concat (map term_vars args) in
    let hits := filter (fun vn => existsb (variable_eqb (fst vn)) variables) blockers in
    {| blocker_depth := minimum_blocker_depth hits;
       blocker_occurrences := List.length hits;
       principal_term_size := fold_right Nat.add 0 (map relevance_term_size args) |}
  | _ => {| blocker_depth := None; blocker_occurrences := 0; principal_term_size := 0 |} end.
(** Counts retain RHS clause/product occurrence multiplicity. Repeating the
    same variable on the LHS does not manufacture extra RHS blocker hits.
    Irrelevant principals all tie and retain source order. *)
Definition relevance_before a b := match a.(blocker_depth),b.(blocker_depth) with
  | Some da,Some db =>
    if da <? db then true else if db <? da then false else
      if b.(blocker_occurrences) <? a.(blocker_occurrences) then true else
      if a.(blocker_occurrences) <? b.(blocker_occurrences) then false else
        a.(principal_term_size) <=? b.(principal_term_size)
  | Some _,None => true | None,Some _ => false | None,None => true end.

(** Insertion of an EARLIER source item before equal scores makes this stable.
    Scores are computed once, rather than recomputed at every comparison. *)
Fixpoint relevance_insert {A} (before : A -> A -> bool) x xs := match xs with
  | [] => [x]
  | y::rest => if before x y then x::xs else y::relevance_insert before x rest end.
Fixpoint relevance_sort {A} (before : A -> A -> bool) xs := match xs with
  | [] => [] | x::rest => relevance_insert before x (relevance_sort before rest) end.
Definition scored_left_order blockers j proposals :=
  map fst (relevance_sort (fun a b => relevance_before (snd a) (snd b))
    (map (fun p => (p,score_left_proposal blockers j p)) proposals)).
Definition order_left_proposals d j proposals := match rhs_blockers d j with
  | [] => proposals | blockers => scored_left_order blockers j proposals end.

Lemma relevance_insert_permutation {A} before (x : A) xs :
  Permutation (x::xs) (relevance_insert before x xs).
Proof.
  induction xs as [|y xs IH]; cbn; [reflexivity|].
  destruct (before x y); [reflexivity|].
  transitivity (y::x::xs); [apply perm_swap|now apply perm_skip].
Qed.
Lemma relevance_sort_permutation {A} before (xs : list A) :
  Permutation xs (relevance_sort before xs).
Proof.
  induction xs as [|x xs IH]; cbn; [reflexivity|].
  transitivity (x::relevance_sort before xs);
    [now apply perm_skip|apply relevance_insert_permutation].
Qed.
Lemma scored_left_order_permutation blockers j proposals :
  Permutation proposals (scored_left_order blockers j proposals).
Proof.
  unfold scored_left_order.
  assert (map fst (map (fun p => (p,score_left_proposal blockers j p)) proposals) = proposals) as E.
  { rewrite map_map; apply map_id. }
  rewrite <- E at 1; apply Permutation_map; apply relevance_sort_permutation.
Qed.
Theorem order_left_proposals_permutation d j proposals :
  Permutation proposals (order_left_proposals d j proposals).
Proof.
  unfold order_left_proposals; destruct (rhs_blockers d j);
    [reflexivity|apply scored_left_order_permutation].
Qed.
Corollary order_left_proposals_length d j proposals :
  List.length (order_left_proposals d j proposals) = List.length proposals.
Proof. symmetry; apply Permutation_length, order_left_proposals_permutation. Qed.
Corollary order_left_proposals_membership d j proposals p :
  In p (order_left_proposals d j proposals) <-> In p proposals.
Proof.
  split; intro H.
  - eapply Permutation_in; [apply Permutation_sym, order_left_proposals_permutation|exact H].
  - eapply Permutation_in; [apply order_left_proposals_permutation|exact H].
Qed.
Lemma no_rhs_blockers_keep_source_order d j proposals : rhs_blockers d j = [] ->
  order_left_proposals d j proposals = proposals.
Proof. intro H; unfold order_left_proposals; now rewrite H. Qed.

(** Optional syntactic pruning detector, separate from the permutation-preserving
    orderer. EXACT list/term equality is tested after erasing logical predicate
    annotations. This is not semantic equivalence or a completeness theorem.
    Fully closed, branching-open, or still-old-group programs are not flagged. *)
Definition erase_sequent_logical_tags j :=
  {| antecedent := map (map erase_tag) j.(antecedent);
     succedent := map (map erase_tag) j.(succedent) |}.
Definition uninformative_left_program j program := match program with
  | ProgramApply p _ => if sequent_eqb j p.(proposal_conclusion) then
      match left_principal j p.(proposal_descriptor),program_frontier program with
      | Some (Pred old_tag _ _),[frontier] =>
        sequent_eqb (erase_sequent_logical_tags j) (erase_sequent_logical_tags frontier) &&
        negb (existsb (Nat.eqb old_tag) (logical_tags frontier))
      | _,_ => false end
    else false
  | _ => false end.
Definition filter_informative_left_programs j programs :=
  filter (fun p => negb (uninformative_left_program j p)) programs.
Lemma filtered_left_programs_included j programs p :
  In p (filter_informative_left_programs j programs) -> In p programs.
Proof. unfold filter_informative_left_programs; rewrite filter_In; tauto. Qed.
