# Rocq Separation-Logic Reimplementation

## Summary

Implement a proof-producing port of the original `src/seplog` entailment
prover under `Rocq-copy/SP`, using the unchanged `Rocq-copy/Cyclic` framework
and the architecture of `FirstOrder` and `LTL`—never `FirstOrderNew`.

The port will prioritize a sound, kernel-checked core. Unsupported behavior
will return bounded non-success and be documented; it will never be filled
with project axioms or admitted proofs. Separate `disprove`, `modelcheck`,
`satcheck`, `satexpgen`, textual parsing, and CLI integration are out of
scope.

## Implementation

### Syntax and semantics

- Add beginner-commented modules for:
  - Free/existential variables, `nil`, substitutions, and unification.
  - Anonymous/free/existential trace tags and ordinal `<`/`<=` constraints.
  - Equalities, disequalities, points-to atoms, tagged predicates, symbolic
    heaps, disjunctive formulas, sequents, inductive clauses, definitions,
    and judgments.
  - Exact equality, tag-insensitive backlink equality, normalization,
    freshening, and executable side-condition checks.
- Use a standard finite-heap model:
  - Locations are naturals with a distinguished `nil`.
  - Concrete heaps are finite partial maps from locations to field lists.
  - Points-to owns exactly one heap cell; separating conjunction uses
    disjoint heap partitions.
  - Free variables/tags come from the world; existential variables/tags
    receive formula-local witnesses.
  - Ranked predicate satisfaction unfolds an inductive clause at rank `S n`,
    with recursive predicates interpreted at smaller ranks.
  - Ordinal constraints restrict tag-rank assignments, providing the
    natural-number measure required by `Cyclic`.
- Instantiate `Framework.THEORY` with separation-logic judgments, denotation,
  visible antecedent trace tags, and their semantic ranks.

### Verified rules and automation

Implement theorem-backed rule kernels and executable generators in the
original priority order:

1. Identity modulo tags and pure inconsistency/ex-falso.
2. Left and right disjunction splitting.
3. Left existential variable/tag instantiation.
4. Equality substitution, right existential substitution,
   equality/disequality discharge, constraint simplification, and
   normalization.
5. Bound introduction and constraint-driven tag instantiation.
6. Points-to introduction, predicate introduction, and points-to
   instantiation.
7. Right and left inductive unfolding, including fresh variables/tags and
   strict child-rank constraints.
8. Exact backlinks plus explicit verified substitution, weakening, and
   left/right transformations.
9. Lemma-style partial backlinks only if their frame and freshness
   obligations can be proved without trust gaps.

For difficult OCaml operations, implement the largest proved-sound subset. A
missing generator must return no candidate; it must not manufacture an
unchecked rule instance.

### Certification and search

- Adapt the FirstOrder certification bridge locally in `SP` so a successful
  executable graph check becomes a `Cyclic.certificate`; do not change
  `Cyclic`.
- Implement finite, fuel-bounded iterative deepening with the original
  high-level rule priority.
- Continue exploring when a syntactically closed graph fails global progress
  or witness checking.
- Use a cheap deterministic trace-witness heuristic followed by bounded finite
  enumeration.
- Expose:
  - `search_config` with minimum and maximum search depth.
  - `verified_proof goal`, containing a checked certificate and root-matching
    proof.
  - `search`, `solvedb`, and `search_sound`.
- Do not add benchmark-specific theorem dispatchers. A benchmark counts as
  search-supported only when general rule generation and graph search return
  a checked certificate.

### Definitions, examples, and integration

- Reify all definitions from `examples/sl.defs`.
- Reify the required dependency closure for the selected ATVA and Songbird
  examples.
- Add explicit acyclic and cyclic teaching examples, including rejected open,
  malformed-backlink, and non-progressing graphs.
- Register SP modules in `Rocq-copy/_CoqProject` and `Rocq-copy/Makefile`, and
  update the Rocq README with the new logic and build entry points.
- Organize responsibilities across `Syntax.v`, `Semantics.v`, `Rules.v`,
  automation/rule-generation modules, certification/search modules, and
  definition/benchmark modules under `Rocq-copy/SP`.

## Benchmark and Test Plan

Attempt these nine original inputs through general search:

1. `base/01.tst`, case 1.
2. `base/01.tst`, case 2.
3. `base/02.tst`, case 1.
4. `base/07.tst`, case 1.
5. `base/19.tst`, case 1.
6. `base/21.tst`, case 1.
7. `atva-2014/01.tst`, case 1.
8. `songbird/ls2_entail_ls_01.tst`.
9. `songbird/lsevenodd_01.tst`.

Testing will include:

- Unit proofs for substitution, normalization, heap disjointness, points-to
  ownership, existential witnesses, ordinal constraints, and ranked
  unfolding.
- Positive and rejected-side-condition tests for every connected rule
  generator.
- Acyclic and cyclic certificate checks plus malformed/open/non-progressing
  rejection tests.
- Full incremental compilation with Rocq 9.1.
- A scan proving there are no project `Axiom`, `Admitted`, `admit`, or `Abort`
  commands.
- `Print Assumptions` on `search_sound` and representative exported theorems.
- `git diff --exit-code -- Rocq-copy/Cyclic` to confirm the cyclic framework
  is unchanged.
- A source/import scan confirming `FirstOrderNew` is unused.

Each benchmark evaluation is isolated and limited to 15 minutes. After an
unsuccessful or timed-out attempt, diagnose the search tree and make one
material improvement before retrying. A benchmark receives at most three
attempts; after the third failure it is marked unsupported and work moves on.

## Audit and Assumptions

Create `Rocq-copy/SP/SP_IMPLEMENTATION_AUDIT.md` containing:

- A module-by-module and rule-by-rule mapping from `src/seplog`.
- Separate `Fully realized`, `Partially realized`, and `Not realized` tables.
- The semantic model and trusted assumptions.
- Search/certification limitations and differences from OCaml behavior.
- Per-benchmark outcome, duration, trial count, and failure reason.
- Clear separation between explicit example certificates and general-search
  successes.
- Recommended next work for omissions caused by complexity or the testing
  limit.

Defaults locked for implementation:

- Standard-library classical principles are allowed and reported.
- Project-defined axioms and admitted obligations are forbidden.
- Soundness takes priority over exact search parity.
- No parser, CLI, or non-entailment separation-logic engines are included.
- Existing files are not deleted, and `Cyclic` remains byte-for-byte
  unchanged.
