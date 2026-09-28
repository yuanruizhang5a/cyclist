From Stdlib Require Import List Bool Arith Lia String.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.ConstructiveEpsilon.

From CyclistRocq.Cyclic Require Import Framework.

Import ListNotations.
Open Scope string_scope.

Inductive formula : Type :=
| Atom (name : string)
| NegAtom (name : string)
| Conj (left right : formula)
| Disj (left right : formula)
| Next (body : formula)
| Always (body : formula)
| Eventually (body : formula).

Fixpoint formula_eqb (a b : formula) : bool :=
  match a, b with
  | Atom x, Atom y | NegAtom x, NegAtom y => String.eqb x y
  | Conj a b, Conj c d | Disj a b, Disj c d =>
      formula_eqb a c && formula_eqb b d
  | Next a, Next b | Always a, Always b | Eventually a, Eventually b =>
      formula_eqb a b
  | _, _ => false
  end.

Definition trace : Type := nat -> string -> bool.
Definition world : Type := (trace * nat)%type.

Fixpoint eval (f : formula) (tr : trace) (now : nat) : Prop :=
  match f with
  | Atom p => tr now p = true
  | NegAtom p => tr now p = false
  | Conj a b => eval a tr now /\ eval b tr now
  | Disj a b => eval a tr now \/ eval b tr now
  | Next a => eval a tr (S now)
  | Always a => forall k, eval a tr (now + k)
  | Eventually a => exists k, eval a tr (now + k)
  end.

Definition traceable (f : formula) : bool :=
  match f with
  | Always _ | Next (Always _) => true
  | _ => false
  end.

Record occurrence : Type := {
  occurrence_tag : option nat;
  occurrence_formula : formula
}.

Definition option_nat_eqb (x y : option nat) : bool :=
  match x, y with
  | None, None => true
  | Some a, Some b => Nat.eqb a b
  | _, _ => false
  end.

Definition occurrence_eqb (x y : occurrence) : bool :=
  option_nat_eqb x.(occurrence_tag) y.(occurrence_tag) &&
  formula_eqb x.(occurrence_formula) y.(occurrence_formula).

Fixpoint judgment_eqb (x y : list occurrence) : bool :=
  match x, y with
  | [], [] => true
  | a :: xs, b :: ys => occurrence_eqb a b && judgment_eqb xs ys
  | _, _ => false
  end.

Fixpoint backlink_eqb (x y : list occurrence) : bool :=
  match x, y with
  | [], [] => true
  | a :: xs, b :: ys =>
      formula_eqb a.(occurrence_formula) b.(occurrence_formula) &&
      backlink_eqb xs ys
  | _, _ => false
  end.

Definition judgment : Type := list occurrence.

Definition denote (j : judgment) (w : world) : Prop :=
  exists o, In o j /\ eval o.(occurrence_formula) (fst w) (snd w).

Fixpoint judgment_tags (j : judgment) : list nat :=
  match j with
  | [] => []
  | o :: js =>
      match o.(occurrence_tag) with
      | Some t => t :: judgment_tags js
      | None => judgment_tags js
      end
  end.

Definition failure_exists (a : formula) (tr : trace) (now : nat) : Prop :=
  exists k, ~ eval a tr (now + k).

Definition failure_distance (a : formula) (tr : trace) (now : nat) : nat :=
  match excluded_middle_informative (failure_exists a tr now) with
  | left H =>
      proj1_sig
        (epsilon_smallest
           (fun k => ~ eval a tr (now + k))
           (fun k => excluded_middle_informative
                       (~ eval a tr (now + k))) H)
  | right _ => 0
  end.

Lemma failure_distance_spec a tr now :
  failure_exists a tr now ->
  ~ eval a tr (now + failure_distance a tr now).
Proof.
  intro Hex.
  unfold failure_distance.
  destruct (excluded_middle_informative (failure_exists a tr now))
    as [Hsome | Hnone].
  - destruct (epsilon_smallest
      (fun k : nat => ~ eval a tr (now + k))
      (fun k : nat => excluded_middle_informative
        (~ eval a tr (now + k))) Hsome) as [k [Hk Hmin]].
    exact Hk.
  - contradiction.
Qed.

Lemma failure_distance_min a tr now k :
  failure_exists a tr now ->
  ~ eval a tr (now + k) ->
  failure_distance a tr now <= k.
Proof.
  intros Hex Hk.
  unfold failure_distance.
  destruct (excluded_middle_informative (failure_exists a tr now))
    as [Hsome | Hnone].
  - destruct (epsilon_smallest
      (fun n : nat => ~ eval a tr (now + n))
      (fun n : nat => excluded_middle_informative
        (~ eval a tr (now + n))) Hsome) as [n [Hn Hmin]].
    apply Hmin. exact Hk.
  - contradiction.
Qed.

Lemma failure_distance_shift a tr now :
  eval a tr now ->
  failure_exists a tr now ->
  failure_distance a tr now = S (failure_distance a tr (S now)).
Proof.
  intros Hnow Hex.
  assert (Hex_next : failure_exists a tr (S now)).
  {
    destruct Hex as [k Hk].
    destruct k as [|k].
    - exfalso. apply Hk. rewrite Nat.add_0_r. exact Hnow.
    - exists k. replace (S now + k) with (now + S k) by lia. exact Hk.
  }
  pose proof (failure_distance_spec a tr now Hex) as Hfail.
  pose proof (failure_distance_spec a tr (S now) Hex_next) as Hfail_next.
  pose proof (failure_distance_min a tr now
    (S (failure_distance a tr (S now))) Hex) as Hupper.
  specialize (Hupper ltac:(replace
    (now + S (failure_distance a tr (S now))) with
    (S now + failure_distance a tr (S now)) by lia; exact Hfail_next)).
  assert (Hpositive : 0 < failure_distance a tr now).
  {
    destruct (failure_distance a tr now) eqn:Hd; [|lia].
    rewrite Nat.add_0_r in Hfail. contradiction.
  }
  destruct (failure_distance a tr now) as [|d] eqn:Hd; [lia|].
  assert (Hlower : failure_distance a tr (S now) <= d).
  {
    apply failure_distance_min; [exact Hex_next|].
    replace (S now + d) with (now + S d) by lia.
    exact Hfail.
  }
  lia.
Qed.

Definition occurrence_rank (o : occurrence) (w : world) : nat :=
  let tr := fst w in
  let now := snd w in
  match o.(occurrence_formula) with
  | Always a => 2 * failure_distance a tr now + 1
  | Next (Always a) => 2 * failure_distance a tr (S now) + 2
  | _ => 0
  end.

Fixpoint rank_of_tag (j : judgment) (w : world) (tag : nat) : nat :=
  match j with
  | [] => 0
  | o :: js =>
      match o.(occurrence_tag) with
      | Some t => if Nat.eqb tag t then occurrence_rank o w
                  else rank_of_tag js w tag
      | None => rank_of_tag js w tag
      end
  end.

Definition untagged (f : formula) : occurrence :=
  {| occurrence_tag := None; occurrence_formula := f |}.

Definition tagged (t : nat) (f : formula) : occurrence :=
  {| occurrence_tag := Some t; occurrence_formula := f |}.

Module LTLTheory <: Framework.THEORY.
  Definition World := world.
  Definition Judgment := judgment.
  Definition Sequent := World -> Prop.
  Definition judgment_eqb := judgment_eqb.
  Definition backlink_eqb := backlink_eqb.
  Definition denote := denote.
  Definition tags := judgment_tags.
  Definition rank := rank_of_tag.
End LTLTheory.

Module Cyclic := Framework.Make LTLTheory.
