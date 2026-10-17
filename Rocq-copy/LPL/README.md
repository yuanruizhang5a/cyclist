# Labelled process logic: G3PPL and its FOPL instance

LPL provides a parameterized G3PPL theory and a G3FOPL specialization in Rocq
9.1.0 using the standard library and the unchanged `Cyclic/` framework.
The opaque-carrier and primitive-syntax refinement follows
[refine-2-plan.md](refine-2-plan.md) and the
[recorded decisions](REFINEMENT_DECISIONS.md). The first-order compatibility
proofs and migration map are in [FOPL_COMPATIBILITY.md](FOPL_COMPATIBILITY.md).

## Build and verify

From `Rocq-copy/`:

```sh
python3 -B LPL/build.py --common
python3 -B LPL/run_benchmarks.py --suite all
make -C LPL fopl
make -C LPL ppl
make -C LPL check
```

The runner has 15 original FOPL units and 14 PPL units. It compiles each unit
with `timeout --signal=KILL 600s`, records actual results, and writes
[BENCHMARK_RESULTS.md](BENCHMARK_RESULTS.md) plus JSON and timestamped logs.
Dependency artifacts are validated with compiler, source, dependency, and
artifact hashes. [VALIDATION.md](VALIDATION.md) records independent kernel
checking of every project module and the immutable-scope audit.

The supported build configuration is local to `LPL/`; its `_CoqProject` maps
`..` to `CyclistRocq`. The parent build files retain their historical layout.
Existing compatible `Cyclic/*.vo` dependencies are read without rebuilding
those physical files. If they are missing, the builder stops and requests an
LPL-local staged build. All generated LPL files stay under this directory.
The builder runs the compiler with `LPL/` as its working directory, keeping
tactic caches local as well. Build commands suppress unused globalization files.
`make -C LPL check` reruns the benchmarks, audits every source/build entry and
legacy-preservation statement, then independently checks every project module.
Baseline and development verification records are retained alongside the final run.

## Shared implementation

The eight root `.v` files implement the generic theory directly, including
`TraceSafety.v`. `FOPL/` supplies first-order payloads, interpretations, and extra rules.
There is one production implementation of the common rule and certification
kernels. `FOPL/LegacyReference/` is an import-only copy of the frozen reference
used solely by `FOPL/Compatibility.v`. Its syntax, semantics and progress remain
separate from production code; its signature interface is shared with FOPL
and checked byte-for-byte against the immutable `../LPL-old/` signature.
[CLEANUP.json](CLEANUP.json) records the recoverable archive of obsolete
snapshots, logs, duplicate files and generated artifacts.

| File | Responsibility |
| --- | --- |
| `Signature.v` | Decidable reified vocabulary: atoms, action payloads, extension tokens, world terms, and relation symbols |
| `Syntax.v` | Shared recursive syntax, relation contexts, sorted labels/substitutions, tags, equality, fresh-world checks, and reflected well-formedness |
| `Semantics.v` | Arbitrary frames, explicit model laws, finite-trace semantics, label mappings, relations, admissibility, substitution, and fresh-world transport |
| `Progress.v` | Execution histories, minimum summed counterexample lengths, arbitrary atomic-successor descent, and the framework adapter |
| `Rules.v` | Common primitive/derived rules, all four atomic-action rules, relational structural rules, and both cut-context variants |
| `RuleGeneration.v` | Finite local scans and concrete verified requests, including relation indices and fresh successors |
| `Certification.v` | Checker reflection and `raw_check_sound` through `certificate_sound` |
| `TraceSafety.v` | Reusable all-visited-state invariant lemmas, conditional on action preservation and a proved head-observation property |
| `PPL/Instance.v` | Plain propositional vocabulary/frame adapters |
| `FOPL/*.v` | First-order signature, terms, updates, quantifier operations/proofs, deterministic assignment rules, manual terminals, and thin adapters |

The primitive formula constructors are exactly `Truth`, `Atom`, `Neg`, `Conj`,
`Extension`, `First`, `Suffix`, and `Box`. Programs use `Atomic`, `Test`, `Seq`,
`Choice`, and `Star`. `Atom : L.atom -> formula` and
`Atomic : L.action -> program` take opaque carriers with syntactic equality and
unary Boolean payload checks. The shared implementation never inspects a
predicate application, equality term, or assignment payload.

| Derived operator | Definition |
| --- | --- |
| `Falsity` | `Neg Truth` |
| `Disj a b` | `Neg (Conj (Neg a) (Neg b))` |
| `Impl a b` | `Neg (Conj a (Neg b))` |
| `Coextension x a` | `Neg (Extension x (Neg a))` |
| `DualSuffix a b` | `Neg (Suffix (Neg a) (Neg b))` |
| `Diamond p a` | `Neg (Box p (Neg a))` |

These are definitions, so each derived expression equals its expansion in
syntax as well as meaning. `Next`, `Eventually`, and `Always` remain derived
definitions. Every formula is false on the empty trace; Boolean and duality
laws assume a nonempty trace. `pureb` classifies a nonmodal fragment, while
each instance separately proves its head-state semantic property.

PPL uses the proposition and action types directly and has no extension tokens.
FOPL owns `atom_payload` (`Predicate` / `Equality`) and `assignment`
(`Assignment`), with terms, substitutions and arity checks inside `FOPL/`.
`All` uses `Extension`; `Ex` uses its dual. Quantified bodies remain pure.

Semantic states and predicate truth need no decision procedures. The frame's
atomic-trace law proves that atomic executions are exactly length-two traces
of its action relation. Support and substitution laws justify interpretation
of user-defined world terms. Custom relation interpretations receive their
interpreted label arguments; they are never assumed to be action relations.

## Instantiate plain PPL

Implement `VOCABULARY` with action/proposition/relation symbol types and their
syntactic equality decisions. Implement `FRAME Vocabulary` with a nonempty
state type, action relations, proposition meanings, and custom relation meanings.
Create the semantic instance, then one graph kernel shared by both consumers:

```coq
From CyclistRocq.LPL.PPL Require Import Instance.
From CyclistRocq.LPL Require Import Progress Rules RuleGeneration Certification.

Module I := MakeInstance MyVocabulary MyFrame.
Module Pr := MakeProgress I.Language I.Syn I.Sem.
Module K.
  Module Core := MakeRules I.Language I.Syn I.Sem Pr.
  Module Model := I.Model.
  Include Core.ForModel Model.
End K.
Module G := MakeRuleGeneration I.Language I.Syn I.Sem Pr K.
Module C := MakeCertification I.Language I.Syn I.Sem Pr K.
```

[Support.v](Benchmarks/PPL/Support.v) instantiates a finite nondeterministic
protocol. [Instances.v](Benchmarks/PPL/Instances.v) also instantiates Boolean
vocabularies, an arbitrary-frame functor, and structured world terms with a
state-flipping operation. Keeping the graph kernel outside `MakeInstance`
also avoids a Rocq 9.1 module-substitution anomaly encountered during development.

## Instantiate FOPL

The original signature/model interface remains available under `FOPL/`:

```coq
From CyclistRocq.LPL.FOPL Require Import Signature Rules RuleGeneration Certification.

Module K.
  Module Core := MakeRules MySignature.
  Module Model <: Core.Pr.Sem.INTERPRETATION.
    Definition interpretation := Core.Pr.Sem.Model
      Carrier an_element interpret_functions interpret_predicates.
  End Model.
  Include Core.ForModel Model.
End K.
Module G := MakeRuleGeneration MySignature K.
Module C := MakeCertification MySignature K.
```

Import the instantiated syntax through its exported modules, as illustrated in
[FOPL benchmark support](FOPL/Benchmarks/Support.v). The familiar `Pred`, `Equal`,
`All`, `Ex`, and `Assign` spellings are expression-building helpers or
notations over primitive shared syntax. Structural traversals match the
primitive constructors and FOPL-owned payloads; `Ex` is the negated universal
encoding. Qualified generic constructors remain in `Syn.Shared`.
The FOPL facade retains the relation-free legacy fragment, while the shared
judgment type also supports explicit relational extensions. No extra relational
premise is required by an original assignment rule.
Generation and certification export the supplied first-order kernel directly;
retain the original `K` module above for qualified first-order rule access.
Their internal `K` namespace is the shared generic kernel.

## Semantic conventions

- Labels append their complete state lists. Empty components are units;
  repeated boundary states remain repeated and different endpoints are allowed.
  Every complete assertion label must be nonempty.
- Program composition overlaps one common endpoint. Atomic actions and tests
  produce two-state traces. Tests evaluate their guard on `[s; s]`, as selected
  by the user for T1. Zero iterations are the successful true test, including
  its final stutter; iteration is finite and may stop at any finite point.
- A judgment is `R ; Gamma => Delta`. Its meaning is guarded by label
  admissibility, then true relational assumptions, then the antecedent.
  Relational assumptions are untagged. Their exact syntax matters for backlinks.
- Action relations interpret their two endpoint labels as singleton traces;
  longer trace endpoints are not reduced to a head or last state. The primitive
  action-rule request uses world-term endpoints, matching its world-variable
  rule display. Unsupported endpoint shapes fail explicitly.
- FOPL quantifiers change the bound variable uniformly throughout the trace.
  Their bodies must recursively be pure FOL; quantifier eigenvariables are fresh
  for labels, nested updates, assignment targets, contexts, and bodies.
- Only succedent boxes, suffixes, and expanded dual suffixes may carry unique occurrence
  tags. Rank is the minimum sum of component-trace lengths of a counterexample
  history. False admissible trace elements have proved attained minima.

## Requests, certificates, and evidence

`generate_axiom` recognizes structural closures. `generate_rules` scans the
current judgment only; plain PPL retains ordinary propositional generation.
FOPL retains its manual pure-terminal boundary. `generate_requested` checks
explicit inputs and returns a record already containing ordinary soundness
and a counterstep satisfying every advertised pair on its selected edge.

At each occurrence, the common candidate order is disjunction, implication,
diamond, dual suffix, then the primitive constructor. All applicable views
contribute candidates, including overlapping encodings. FOPL inserts its
quantifier and assignment candidates before primitive fallback. Named requests
still check exact conclusions, every premise, tags, and freshness.

PPL-specific requests include `AtomicEigen side position successor`,
`AtomicUse side position relation_index`, relation weakening/contraction/exchange,
and `CutRelations` with both relational and formula context partitions.
Substitution, cuts, label algebra, positions, and companion/tag maps remain
explicit requests. The FOPL request language adds its original `Instantiate`
and `Eigen` cases and deterministic assignment candidates around the shared scans.

There is no proof search, automatic witness/backlink discovery, solver, or
semantic truth oracle. Pure terminals carry caller-supplied Rocq proofs.
Manual graph scripts and finite tag/potential witnesses are certified through
`certificate_sound`. The framework's witness selects at most one tag per node;
acceptance of every manuscript preproof and completeness are outside scope.
The cyclic prefix-invariant examples and the separate all-visited-state semantic
proofs retain their distinct proof modes in the reports.
