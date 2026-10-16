# First-order labelled process logic

LPL implements the agreed G3FOPL syntax, semantics, rule kernels, local
generation, and certification bridge using Rocq 9.1 and its standard library.
The controlling decisions are D1–D4 in [the plan](IMPLEMENTATION_PLAN.md).
The generic `Cyclic/` directory is unchanged.

## Build and verify

From `Rocq-copy/`:

```sh
make lpl                 # dependencies and all benchmark units
make lpl-benchmarks      # rerun each benchmark under timeout 600s, write report
```

[BENCHMARK_RESULTS.md](BENCHMARK_RESULTS.md) records commands, actual timings,
exit statuses, coverage, graph sizes, assumptions, and the development timeout.
The accompanying JSON records source hashes; linked compiler logs preserve
`Print Assumptions` output. The runner never increases the ten-minute limit
or deletes files. `make all` also includes the LPL development.
[VALIDATION.md](VALIDATION.md) records the independent kernel check, existing
LTL/FirstOrder regressions, and the immutable-directory/source audit.

## Files

| File | Responsibility |
| --- | --- |
| `Signature.v` | Arbitrary finitary signatures with decidable syntactic symbol equality |
| `Syntax.v` | Terms, named binding, all Boolean connectives, quantifiers, programs, labels, occurrences, reflected arity/purity/tag checks, capture-avoiding FOL substitution and preservation proofs |
| `Semantics.v` | Arbitrary nonempty models, shallow FOL and LPL meanings, updates, finite execution traces, guarded sequents, substitution and freshness proofs |
| `Progress.v` | Execution/counterexample sequences, mathematical minima of summed trace lengths, rank transport and descent, framework instance |
| `Rules.v` | Proof-backed axioms and rules, context routing, structural rules, manual pure terminal boundary |
| `RuleGeneration.v` | Finite local scans, concrete requests, reflected checks, successful-result guarantees |
| `Certification.v` | Structural/witness reflection and `raw_check_sound` through `certificate_sound` |
| `Benchmarks/` | Explicit scripts, witnesses, pure proofs, semantic examples and negative checks |

## Instantiate one shared kernel

Rocq functor applications generate distinct inductive types. Create one kernel
and pass that same module to generation and certification:

```coq
From CyclistRocq.LPL Require Import Signature Rules RuleGeneration Certification.

Module MyKernel.
  Module Core := MakeRules MySignature.
  Module Model <: Core.Pr.Sem.INTERPRETATION.
    Definition interpretation := Core.Pr.Sem.Model
      Carrier an_element interpret_functions interpret_predicates.
  End Model.
  Include Core.ForModel Model.
End MyKernel.

Module G := MakeRuleGeneration MySignature MyKernel.
Module C := MakeCertification MySignature MyKernel.
```

`Carrier` can be any nonempty type; predicate interpretations return `Prop`.
Neither semantic equality nor predicate truth needs a decision procedure.
Functions need not be injective, and their ranges need not be disjoint.
[Support.v](Benchmarks/Support.v) gives a concrete integer instance;
[Signatures.v](Benchmarks/Signatures.v) gives an arbitrary-model functor and
an independent Boolean signature.

## Semantic conventions

* `Join` evaluates by list append, retaining repeated boundary states and
  allowing successive different states. `Empty` evaluates to `[]` and remains
  a two-sided unit. Every asserted **complete** label must be nonempty.
* Program execution composition overlaps one matching endpoint. It is separate
  from label append. Assignments and tests produce two-state traces; tests
  evaluate their guard on that stutter. Star zero is the successful true test,
  so every finite unfolding includes its final stutter.
* `denote` guards the sequent implication with assertion admissibility. No
  default state interprets an empty assertion. Boolean nonemptiness reflection,
  admissible-world validity, and false-sequent extraction are proved.
* Named `All` and `Ex` bodies must recursively be pure FOL. `formula_wfb` rejects
  any program modality or temporal operator inside either body. Modalities and
  temporal operators outside a quantified formula remain permitted.
* Quantification writes one uniform value to every trace state. `pure_head`
  proves agreement with ordinary FOL at the first state. `subst_fo` renames
  conflicting binders and has a proved semantic substitution law. The raw
  substitution helper is accompanied by its explicit capture condition.
  `pureb_spec` relates recognition to an inductive FOL grammar;
  `judgment_wfb_spec` specifies arities, recursively pure quantifier bodies,
  label checks, and tag uniqueness. `subst_fo_wf` and `subst_fo_pure` prove
  preservation under capture-avoiding substitution.
* Eigenvariable checks inspect contexts, principal formulas **and labels**,
  including assignment targets and terms in nested updates. Fresh-variable
  semantic/rank transport is proved by an invertible state transformation.

Only succedent boxes, suffixes and dual suffixes can carry occurrence tags.
Tags are unique within a well-formed judgment. Ranks use the manuscript's
minimum counterexample measure, the **sum of component-trace lengths**.
The fallback for an empty counterexample set or absent tag is zero; existence
and minimum-specification proofs exclude that fallback for false admissible
trace elements.

## Rules and local generation

Every concrete rule requires well-formed source/premise syntax. Each record
contains ordinary soundness and one countermodel step respecting every pair
on its selected edge. Choice/star selection uses a minimum counterexample;
assignment/test and continuing suffix/dual-suffix edges have proved strict
descent. The first suffix-right premise has no recursive principal pair.
Star unfolding and backlinks provide no progress by themselves.

The rule families are:

| Family | Public names used in requests |
| --- | --- |
| Assignment/test/sequence/choice/star | `B.Assign`, `B.Test`, `B.Seq`, `B.Choice`, `B.Star`, and corresponding `D.*`, each with `.L`/`.R` |
| Trace | `At.L/R`, `First.L/R`, `Suffix.L/R`, `DualSuffix.L/R`, singleton suffix-left axiom |
| Boolean | `Not.L/R`, `And.L/R`, `Or.L/R`, `Impl.L/R` |
| Quantifiers | `All.L/R`, `Ex.L/R` |
| Structural | `Wk.L/R`, `Exchange`, `Cut`, `Sub.World`, `Sub.Trace`, `Backlink.exact`, `Backlink.tags` |

The [expansion catalog](RULE_EXPANSIONS.md) fixes ordered premise lists. Both
left box-choice and left box-star have **two** premises. Weakening has **one
context-only** premise and is never an axiom.

```coq
G.generate_axiom j                       (* option axiom_instance *)
G.generate_rules j                       (* list rule_instance *)
G.generate_requested j request           (* option rule_instance *)
```

`generate_rules` scans eligible positions without choosing a proof strategy.
It stops at the pure terminal shape. Concrete `Local side index name` requests
select one finite local scheme. `Instantiate` supplies a quantifier term;
`Eigen` supplies an eigenvariable; `SubstituteWorld`, `SubstituteTrace`, `Cut`,
`ExchangeAdjacent`, `BacklinkExact`, and `BacklinkTags` supply explicit choices.
Backlink tag renamings are finite lists of pairs, checked against the supplied
companion. Successful-result theorems establish the input conclusion,
well-formed premises, and valid edge endpoints/progress inclusion.

Rules match the catalog's literal label constructors. Assignment/test steps
expose a final `Join sigma (StateLabel U)`; temporal steps expose an initial
state update. `RotateLabels` and `UnitLabels` let the caller explicitly present
equivalent label parentheses/units at a chosen path. Their one-premise schemes
and preservation proofs are documented in the catalog. They do not run a
normalization search. Failed requests mean that a verified instance was not
generated, not that the goal is false.

There is no proof-search loop, unification, automatic witness selection,
backlink discovery, solver integration, or project FirstOrder/LTL import.

## Manual proofs and certificates

`close_atoms` implements the atom/equality-at-update terminal boundary.
`close_pure` is the separately justified compound-pure extension. Both require
shape evidence and a caller-supplied shallow proof; generators do not synthesize
predicate truth or pure proof terms.

[AssignmentChange.v](Benchmarks/AssignmentChange.v) is a six-node generated
acyclic proof that an assignment changes the next-state value. Its pure leaves
are discharged with ordinary Rocq proofs. [Cyclic.v](Benchmarks/Cyclic.v) and
[CyclicTags.v](Benchmarks/CyclicTags.v) are actual 11/12-node star cycles with
backlinks and explicit tag/potential witnesses. Their exported validity follows
from `raw_check_sound`, which constructs the semantic certificate and applies
the unchanged framework's `certificate_sound`.

The cyclic examples preserve a first-state observation. The guarded decrement
loop and nested program benchmarks separately prove invariants at **every
visited state**, for all finite iteration counts, by semantic induction. Those
two complex examples are direct semantic proofs, not cyclic certificates; no
claim that a star execution must reach its loop exit is made.

The framework's witness can follow at most one tag per node and is conservative.
Acceptance of every manuscript preproof is not claimed. Negative graphs test
actual structural/tag failures and a closed nonprogressing cycle using proved
local rule records. Object-level occurrence uniqueness is checked by LPL;
it is not attributed to the generic checker.

## Assumptions and scope

There are no admitted proofs or project-defined soundness axioms. The reported
standard-library principles are classical excluded middle, definite and
indefinite description, and functional extensionality. Explicit abstract
signature/model parameters carry no constructor or predicate-induction laws.

Completeness, proof search, acceptance of all pathwise manuscript traces,
automatic pure-FOL reasoning, and changes to the OCaml prover are outside scope.
