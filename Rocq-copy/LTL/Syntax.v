From Stdlib Require Import List Bool Arith Lia String.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.ConstructiveEpsilon.

From CyclistRocq.Cyclic Require Import Framework.

Import ListNotations.
Open Scope string_scope.

(* The syntax of LTL formulae in negation normal form (NNF).
   Negation is pushed inward to atoms, so there is no general negation
   connective — only [NegAtom] for the negation of a literal.
   The seven constructors correspond exactly to the seven formula shapes
   handled by the cyclic proof rules in Rules.v. *)
Inductive formula : Type :=
| Atom (name : string)        (* atomic proposition p            *)
| NegAtom (name : string)     (* negated atomic proposition ¬p   *)
| Conj (left right : formula) (* conjunction  a ∧ b              *)
| Disj (left right : formula) (* disjunction  a ∨ b              *)
| Next (body : formula)       (* next-step    ◯ a                *)
| Always (body : formula)     (* always       □ a                *)
| Eventually (body : formula). (* eventually   ◇ a                *)

(* Decidable boolean equality on formulae.
   Returns true iff the two formulae are syntactically identical.
   Used to compare sequents and backlink targets in the proof checker. *)
Fixpoint formula_eqb (a b : formula) : bool :=
  match a, b with
  | Atom x, Atom y | NegAtom x, NegAtom y => String.eqb x y
  | Conj a b, Conj c d | Disj a b, Disj c d =>
      formula_eqb a c && formula_eqb b d
  | Next a, Next b | Always a, Always b | Eventually a, Eventually b =>
      formula_eqb a b
  | _, _ => false
  end.

(* A [trace] is an infinite sequence of states, represented as a function
   from a time index (nat) and an atom name (string) to a truth value (bool).
   [tr t p = true] means atom p holds at time t.
   The entire infinite future is encoded in a single total function, so
   temporal operators just shift the time index rather than consuming the
   sequence. *)
Definition trace : Type := nat -> string -> bool.

(* A [world] pairs a trace with a current time index.
   The trace is the full infinite history; [now] is the cursor into it,
   marking where evaluation starts.  Temporal operators advance [now]
   while keeping the same trace. *)
Definition world : Type := (trace * nat)%type.

(* Semantic evaluation of an LTL formula.
   [eval f tr now] holds iff formula [f] is satisfied by trace [tr]
   at time [now].  The definition follows the standard LTL trace semantics:
     - Atom/NegAtom: look up the atom at the current moment.
     - Conj/Disj: standard logical connectives, time is unchanged.
     - Next: advance time by one step.
     - Always: the body must hold at every future time (now, now+1, now+2, …).
     - Eventually: the body must hold at some future time. *)
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

(* Decides whether a formula is "traceable", i.e. whether it carries a
   progress tag in the cyclic proof.
   Only [Always a] and [Next (Always a)] are traceable because these are
   the formulae that must make measurable progress (decrease in rank) at
   each cycle of the proof, ensuring soundness of backlinks.
   All other formulae are untagged (anonymous). *)
Definition traceable (f : formula) : bool :=
  match f with
  | Always _ | Next (Always _) => true
  | _ => false
  end.

(* An [occurrence] is a formula together with an optional numeric tag.
   Tags identify formulae that are tracked for progress across a backlink.
   - [occurrence_tag = Some t]: the formula is traceable and has tag [t].
   - [occurrence_tag = None]:   the formula is untagged (not tracked). *)
Record occurrence : Type := {
  occurrence_tag : option nat;
  occurrence_formula : formula
}.

(* Boolean equality on [option nat], used when comparing occurrence tags. *)
Definition option_nat_eqb (x y : option nat) : bool :=
  match x, y with
  | None, None => true
  | Some a, Some b => Nat.eqb a b
  | _, _ => false
  end.

(* Boolean equality on occurrences: two occurrences are equal iff
   their tags and formulae are both equal. *)
Definition occurrence_eqb (x y : occurrence) : bool :=
  option_nat_eqb x.(occurrence_tag) y.(occurrence_tag) &&
  formula_eqb x.(occurrence_formula) y.(occurrence_formula).

(* Boolean equality on judgments (lists of occurrences), comparing them
   element-by-element including their tags.
   Used to decide whether two sequents in the proof tree are identical,
   which is needed to detect exact backlink targets. *)
Fixpoint judgment_eqb (x y : list occurrence) : bool :=
  match x, y with
  | [], [] => true
  | a :: xs, b :: ys => occurrence_eqb a b && judgment_eqb xs ys
  | _, _ => false
  end.

(* Boolean equality on judgments that ignores tags, comparing only the
   underlying formulae.
   Used for backlink matching: a backlink is valid if the current sequent
   contains the same formulae as the backlink target, regardless of how
   tags may have been refreshed. *)
Fixpoint backlink_eqb (x y : list occurrence) : bool :=
  match x, y with
  | [], [] => true
  | a :: xs, b :: ys =>
      formula_eqb a.(occurrence_formula) b.(occurrence_formula) &&
      backlink_eqb xs ys
  | _, _ => false
  end.

(* A [judgment] is a sequent: a finite list of tagged formulae (occurrences).
   Semantically it represents the disjunction of its formulae (see [denote]).
   The cyclic proof rules operate on judgments, splitting, extending, or
   consuming occurrences one step at a time. *)
Definition judgment : Type := list occurrence.

(* The denotation of a judgment at a world: the judgment holds iff at least
   one of its formulae holds at the given world.
   This gives judgments their disjunctive semantics, matching the one-sided
   sequent calculus style used by the cyclic prover. *)
Definition denote (j : judgment) (w : world) : Prop :=
  exists o, In o j /\ eval o.(occurrence_formula) (fst w) (snd w).

(* Collects all numeric tags that appear in a judgment.
   The resulting list is used by the framework to track which formulae
   carry progress obligations across backlinks. *)
Fixpoint judgment_tags (j : judgment) : list nat :=
  match j with
  | [] => []
  | o :: js =>
      match o.(occurrence_tag) with
      | Some t => t :: judgment_tags js
      | None => judgment_tags js
      end
  end.

(* [failure_exists a tr now] holds iff [Always a] is *not* satisfied at
   [(tr, now)], i.e. there exists a future time step at which [a] fails.
   This is the precondition that makes [failure_distance] meaningful. *)
Definition failure_exists (a : formula) (tr : trace) (now : nat) : Prop :=
  exists k, ~ eval a tr (now + k).

(* The first time step (relative to [now]) at which [a] fails on [tr].
   Formally, this is the smallest [k] such that [~ eval a tr (now + k)].
   If no such [k] exists (i.e. [Always a] genuinely holds), the function
   returns 0 as a dummy value — [failure_distance_spec] ensures it is only
   used when [failure_exists] holds.
   This is computed using [epsilon_smallest], which requires classical logic
   and constructive epsilon (hence the imports at the top of the file). *)
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

(* [failure_distance] lands precisely on a failing step:
   if [Always a] eventually fails, then [a] does not hold at time
   [now + failure_distance a tr now].
   This is the key correctness property of [failure_distance]. *)
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

(* [failure_distance] is minimal: no earlier time step fails.
   If [k] is any witness that [a] fails at [now + k], then the
   failure distance is at most [k].
   Together with [failure_distance_spec] this characterises
   [failure_distance] as the exact minimum. *)
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

(* The failure distance decreases by exactly one when we step forward in
   time, provided the current moment is safe ([eval a tr now]) but a future
   failure exists.
   Concretely: if [a] holds now but [Always a] will eventually fail, then
   [failure_distance a tr now = S (failure_distance a tr (S now))].
   This strictly-decreasing property is what makes [occurrence_rank] a
   valid termination measure for the cyclic proof: each application of the
   Always or Next(Always) rule reduces the rank by at least one. *)
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

(* The rank of a single occurrence at a world.
   Only traceable formulae ([Always a] and [Next (Always a)]) have a
   non-zero rank; all other formulae get rank 0.
   The rank is defined in terms of [failure_distance] so that it
   strictly decreases as time advances under an [Always] or [Next(Always)]
   formula, giving the cyclic proof checker its termination certificate.
   The factor of 2 and the offsets (+1, +2) interleave the ranks of
   [Always a] and [Next (Always a)] so that they are always distinct and
   comparable by the framework's well-foundedness check. *)
Definition occurrence_rank (o : occurrence) (w : world) : nat :=
  let tr := fst w in
  let now := snd w in
  match o.(occurrence_formula) with
  | Always a => 2 * failure_distance a tr now + 1
  | Next (Always a) => 2 * failure_distance a tr (S now) + 2
  | _ => 0
  end.

(* Looks up the rank of the occurrence with tag [tag] in judgment [j]
   at world [w].
   Scans [j] linearly; returns 0 if no occurrence with that tag is found.
   Used by the [Framework] to retrieve the rank of a tagged formula when
   verifying that a backlink makes progress. *)
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

(* Smart constructor: wraps a formula in an untagged occurrence.
   Use for formulae that do not carry a progress obligation
   (everything except [Always _] and [Next (Always _)]). *)
Definition untagged (f : formula) : occurrence :=
  {| occurrence_tag := None; occurrence_formula := f |}.

(* Smart constructor: wraps a formula in a tagged occurrence with tag [t].
   Use for [Always _] and [Next (Always _)] formulae that must be tracked
   for progress across a backlink. *)
Definition tagged (t : nat) (f : formula) : occurrence :=
  {| occurrence_tag := Some t; occurrence_formula := f |}.

(* Bundles the LTL-specific definitions into the [Framework.THEORY] interface.
   [Framework.Make] then produces the generic cyclic proof infrastructure
   (proof trees, backlink validation, soundness theorem) instantiated to LTL.
   Each field maps a name required by the interface to its LTL definition:
     - World     : a trace paired with a time cursor
     - Judgment  : a disjunctive sequent of tagged formulae
     - Sequent   : a world-indexed proposition
     - denote    : the disjunctive semantics of a judgment
     - tags      : extract numeric tags from a judgment
     - rank      : retrieve the rank of a tagged formula at a world *)
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

(* The fully instantiated cyclic proof module for LTL.
   [Cyclic] exports everything needed to build and check cyclic proofs:
   proof trees, rule application, backlink checking, and the soundness
   theorem that a complete cyclic proof witnesses semantic validity. *)
Module Cyclic := Framework.Make LTLTheory.
