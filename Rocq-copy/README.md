# Cyclist-style cyclic derivations in Rocq

This directory is a standalone Rocq 9.1 reimplementation of the generic
cyclic-derivation ideas used by the surrounding OCaml repository.  It uses a
shallow semantic embedding and does not depend on the OCaml build.

## Build

From the repository root:

```sh
make -C Rocq-copy
```

The build has no delete/clean target.  Generated Rocq objects are ignored by
`Rocq-copy/.gitignore`.

## Architecture

`Cyclic/Framework.v` exposes `Framework.THEORY` and `Framework.Make`.
A logic supplies:

```coq
Module Type THEORY.
  Parameter World Judgment : Type.
  Definition Sequent := World -> Prop.
  Parameter judgment_eqb : Judgment -> Judgment -> bool.
  Parameter backlink_eqb : Judgment -> Judgment -> bool.
  Parameter denote : Judgment -> Sequent.
  Parameter tags : Judgment -> list nat.
  Parameter rank : Judgment -> World -> nat -> nat.
End THEORY.
```

`denote j` is the actual shallow sequent: a function from semantic worlds to
Rocq's `Prop`.  `Judgment` is only the reified label needed by an executable
graph checker; arbitrary functions into `Prop` cannot be compared by a Boolean
program.

After applying the functor, a theory gets:

- theorem-backed `axiom_instance` and `rule_instance` records;
- open, axiom, inference, and backlink graph nodes;
- an immutable script API (`begin_build`, `ApplyRule`, `CloseWith`,
  `AddBacklink`, and `run_script`);
- structural, tag-relation, relational-closure, and trace-witness checks; and
- `certificate_sound`, which turns an accepted proof-carrying certificate into
  a theorem of its root shallow sequent.

Every rule instance contains both its ordinary rule theorem and its local
countermodel/trace theorem.  The latter says that a false conclusion selects a
false premise, valid tag pairs do not increase the semantic rank, and
progressing pairs strictly decrease it.

The executable relational checker uses the same stay/decrease algebra as the
repository's relational checker: relations are composed, path relations are
saturated, and every loop relation must acquire a decreasing diagonal.  A
certificate additionally carries a kernel-checked trace-routing witness.  The
witness is conservative but makes the semantic link proof-producing: before a
trace starts its finite potential decreases; after it starts, every edge either
progresses semantically or decreases the finite potential.  The generic
soundness theorem packages these two quantities into a well-founded
lexicographic measure.

## Defining another logic

1. Define a semantic `World`, a reified `Judgment`, and `denote : Judgment ->
   World -> Prop`.
2. Instantiate `Framework.Make`.
3. Prove each local rule as an ordinary Rocq theorem, then package it as a
   `rule_instance` with its countermodel and tag-rank obligations.
4. Build a complete finite graph with the script commands.  Inference commands
   append fresh open nodes; backlinks point to existing matching nodes.
5. Supply the finite trace witness and its edge theorem, prove the executable
   check by `vm_compute`, and apply `certificate_sound`.

`LTL/` is a complete worked instance of this recipe.

## LTL instance

`LTL/Syntax.v` defines the same formula constructors as `src/ltl`: atoms,
negated atoms, conjunction, disjunction, next, eventually, and always.  Worlds
are infinite Boolean traces paired with a time index.  Tagged finite lists
denote one-sided sequents by semantic disjunction.

Only `Always A` and `Next (Always A)` are traceable.  Their ranks use the least
future counterexample to `A`; odd/even phases justify both progressing edges
used by the OCaml implementation:

```text
Always A  -->  Next (Always A)  -->  Always A at the next time
```

`LTL/Rules.v` proves the axiom, disjunction, conjunction, eventually, always,
next, weakening, and exact-backlink rules.  `LTL/Examples.v` contains:

- an acyclic certificate for `p \/ ~p`;
- a six-node cyclic certificate for `Eventually p \/ Always (~p)`;
- builder/whole-graph checks;
- rejected open, dangling, malformed-tag, and non-progressing graphs; and
- exported Rocq theorems `excluded_middle_ltl` and
  `eventually_or_always_not`.

The optional experimental cut and OCaml proof-search heuristics are not
ported.  Certificate construction is explicit rather than automatic.

## Trusted assumptions

There are no `Admitted` proofs or project-defined axioms.  The LTL least-future
counterexample construction uses Rocq's standard classical informative
excluded middle.  `Print Assumptions eventually_or_always_not.` reports that
standard-library assumption explicitly.
