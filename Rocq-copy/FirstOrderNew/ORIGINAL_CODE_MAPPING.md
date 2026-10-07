# Mapping the original first-order code to `FirstOrderNew`

## Scope and how to read this map

The **original code** here is `src/firstorder/` (the nine OCaml implementation
files and their `.mli` interfaces), together with the generic prover it calls
and the supplied `examples/fo.defs`. This follows the scope stated in
[`PLAN.md`](PLAN.md). `Rocq-copy/FirstOrder/` is an earlier Rocq implementation,
not the source used for this mapping. Paths in the first column below are
relative to the repository root; bare `.v` names are in this directory.

The correspondence is **functional**, not a line-for-line port. OCaml sets and
mutable rule combinators become lists, pure programs, and proved rule instances.
Successful Rocq search has a stronger output contract: a checked graph and a
semantic validity theorem. A correspondence does not imply that both programs
enumerate the same candidates or accept the same cyclic graphs.

## File-by-file map of `src/firstorder`

Each `.mli` declares the API of its same-named `.ml`; the mapping applies to
both files. `dune` is treated separately below.

| Original file(s) and responsibility | Realization in `FirstOrderNew` | Important difference or limit |
| --- | --- | --- |
| [`term.ml`](../../src/firstorder/term.ml), [`term.mli`](../../src/firstorder/term.mli): free/existential variable spelling, constants, functions, recursive term traversal, substitution, directional and repeated-head unification, fresh variables, term parser | `Syntax.v` defines `Free`/`Exist`, `Const`/`Var`/`Fun`, equality and recursive `term_vars`; `Substitution.v` defines simultaneous `subst_term` and freshening; `Matching.v` defines `match_term`, `match_terms`, `head_match`, `head_match_terms`; `Input.v` lexes, interns names and parses terms. | Variables are interned as natural-number IDs; OCaml variable printing and hash/set containers are not ported. Matching has explicit fuel and is incomplete when exhausted. |
| [`atom.ml`](../../src/firstorder/atom.ml), [`atom.mli`](../../src/firstorder/atom.mli): equality, disequality, tagged predicates, tag operations, atom variables, substitution, atom matching and parser | `Syntax.v` defines `Eq`, `Deq`, `Pred`, `erase_tag`, `atom_logical_eqb`, `atom_vars`, `atom_tag`, `retag`; `Substitution.v` supplies `subst_atom`; `Matching.v` and `RuleGeneration.v` match atoms; `Input.v` parses atoms and tags; `Semantics.v` defines their truth. | `Input.v` correctly parses `!=` as `Deq` and resolves function-headed equality. Recursive atom variables and tag-erased logical equality correct incomplete/ineffective original paths; exact graph equality remains tag-sensitive. |
| [`prod.ml`](../../src/firstorder/prod.ml), [`prod.mli`](../../src/firstorder/prod.mli): sets of conjunctive atoms, tags, substitution, directional subsumption and universalizing clause variables | `Syntax.v` uses `product := list atom`, membership/subset, tags and normalization; `Substitution.v` maps substitution over products; `Matching.v` implements directional product matching and tracked-tag inclusion; `RuleGeneration.v` builds bounded candidate matches; `Unfolding.v` freshens and universalizes left clause variables; `Semantics.v` interprets conjunction. | Lists retain order and duplicate occurrences for trace accounting; logical set-like comparison is separate from exact list/graph equality. |
| [`form.ml`](../../src/firstorder/form.ml), [`form.mli`](../../src/firstorder/form.mli): DNF disjunctions, formula tags, substitution and left/right subsumption | `Syntax.v` defines `formula := list product`, normalization and variable traversal; `Substitution.v` defines `subst_formula`; `RuleGeneration.v` has `match_left_formulas`, `match_right_formulas`, `formula_entailsb`; `Semantics.v` interprets disjunction; `LocalRules.v` proves coverage and split rules. | DNF identity checks coverage of **every antecedent** product (`Syntax.v:identityb`), correcting the original reversed coverage in `rules.ml:id_axiom`. |
| [`seq.ml`](../../src/firstorder/seq.ml), [`seq.mli`](../../src/firstorder/seq.mli): sequent pair, parsing, tags, variables, substitution and directional sequent subsumption | `Syntax.v` defines the `sequent` record, exact equality, `sequent_vars`, `trace_tags`; `Substitution.v` defines `subst_sequent`; `Input.v` defines raw and validated sequent parsing; `RuleGeneration.v` generates sequent-level matching/backlink plans; `LocalRules.v` checks weakening and backwards substitution; `Semantics.v` defines `denote` and `valid`. | Input validation checks predicate/function arities and antecedent variable scope. Exact backlink labels and logical inclusion are deliberately distinct. |
| [`case.ml`](../../src/firstorder/case.ml), [`case.mli`](../../src/firstorder/case.mli): clause body/head, parsing and class-preserving freshening | `Definitions.v` defines `clause`, head/body operations and well-formedness; `Substitution.v` has generic renaming helpers; `Unfolding.v` defines proved `left_clause`/`right_clause` freshening and head equations; `Input.v` parses clauses. | Left unfolding makes fresh free eigenvariables from both source variable classes. Clause-header and head-name disagreement is diagnosed instead of silently ignored. |
| [`defs.ml`](../../src/firstorder/defs.ml), [`defs.mli`](../../src/firstorder/defs.mli): ordered predicate definitions and definition-file parsing | `Definitions.v` defines ordered `definitions` and signature checks; `Input.v` parses and validates a definition string; `SourceDefinitions.v` transcribes the supplied definition file; `Semantics.v` gives positive clauses a least-fixed-point interpretation. | There is no OCaml channel/file-I/O API in the Rocq core. Undefined predicates and inconsistent arities are reported by validation. |
| [`rules.ml`](../../src/firstorder/rules.ml), [`rules.mli`](../../src/firstorder/rules.mli): axioms, six simplifications, structural/instantiation rules, unfolding, folding, weakening/substitution backlinks and rule priority | `Rules.v` gives rule/trace-evidence types and axiom soundness; `Simplification.v` specifies the six bounded transformations; `LocalRules.v` proves checked simplification, structural, instantiation, weakening and substitution steps; `Unfolding.v` proves left/right unfolding; `Matching.v` handles head matching; `RuleGeneration.v` proposes ordered rules and backlinks; `Compiler.v` rebuilds proposals as certified rules; `Search.v` executes preparation and exact backlinks; `Rank.v` justifies trace progress. | Pure proposals are never accepted as proofs. `Compiler.v` verifies them against proved constructors. Simplification and candidate enumeration have budgets; exhausted search means unknown. Right conjunction uses a guarded binary split. The corrected identity axiom is in `Syntax.v`/`Semantics.v`. |
| [`prove.ml`](../../src/firstorder/prove.ml), [`prove.mli`](../../src/firstorder/prove.mli): connect parser, definitions, rule setup, generic prover and `cyclist fo prove` CLI | `Input.v` supplies parsing; `Compiler.v`/`FastGeneration.v` build active rule menus; `Search.v` and `LazySearch.v` implement bounded DFS and iterative deepening; `CertifiedSearch.v:Make.prove` checks the completed graph and `proved_sound` yields validity; `Benchmarks.v` and `Examples.v` exercise the interface. | `Cmdliner` CLI, `-D`/`-S` options, file loading and process exit behavior are not ported. `prove` returns an optional certified result, not the OCaml frontend result. |
| [`dune`](../../src/firstorder/dune): OCaml build declaration | `_CoqProject` and `Makefile` list and build Rocq modules. | Build systems and artifacts differ. |

## Supporting original files outside `src/firstorder`

| Original source | Realization in `FirstOrderNew` |
| --- | --- |
| [`examples/fo.defs`](../../examples/fo.defs) | `SourceDefinitions.v` is a literal AST transcript; `InputExamples.v` compares parsed text with that AST. The source refers to undefined `ADD_2`, so `source_definitions` is diagnosed and an explicit `closed_source_definitions` subset is used for checked examples and benchmarks. |
| [`src/generic/prover.ml`](../../src/generic/prover.ml), [`proofrule.ml`](../../src/generic/proofrule.ml), [`seqtactics.ml`](../../src/generic/seqtactics.ml) | `RuleGeneration.v` represents choices and compositions as pure proposals/programs; `Compiler.v` certifies them; `Search.v`/`LazySearch.v` perform bounded iterative-deepening search. |
| [`src/generic/proof.ml`](../../src/generic/proof.ml), [`proofnode.ml`](../../src/generic/proofnode.ml), [`tagpairs.ml`](../../src/generic/tagpairs.ml) | `Rules.v` records applications and native trace edges; `Adapter.v` converts native occurrence positions to framework graph tags and exposes graph operations; `Certification.v` packages graph obligations. The actual generic graph/checker implementation lives in `Rocq-copy/Cyclic/Framework.v`. |
| [`src/generic/soundcheck.ml`](../../src/generic/soundcheck.ml) and its C checker support | `Adapter.v`, `Witness.v`, `Certification.v` and `CertifiedSearch.v` check structural, relational and routing requirements before producing a theorem. The fixed nodewise routing witness used by the Rocq framework is more restrictive than the original relational trace criterion. |

## Reverse index: what each `FirstOrderNew` source contributes

This index covers every `.v` listed in `_CoqProject`. “New” means a proof or
integration layer required for the Rocq implementation, rather than a direct
OCaml source-file counterpart.

| `FirstOrderNew` file(s) | Original concern realized |
| --- | --- |
| `Syntax.v`, `Substitution.v` | `term`, `atom`, `prod`, `form`, `seq` data and substitution; `case` freshening primitives. |
| `Definitions.v`, `SourceDefinitions.v` | `case`, `defs`, and `examples/fo.defs`. |
| `Matching.v` | `term`/`atom`/`prod` matching and repeated-head matching used by `rules`. |
| `Input.v`, `InputExamples.v` | Parsers from `term`, `atom`, `prod`, `form`, `seq`, `case`, `defs`, plus parser regression examples. |
| `Semantics.v`, `Rank.v` | New model, least-fixed-point, validity and rank proofs for the calculus implemented by `rules`; the OCaml FO files have no corresponding semantic evaluator. |
| `Rules.v`, `Simplification.v`, `LocalRules.v`, `LocalRulesExamples.v` | `rules` axioms, simplifications, structural steps, substitution/weakening and their checked local evidence and examples. |
| `Unfolding.v`, `UnfoldingExamples.v` | `case` freshening and `rules` left/right unfolding and clause-head matching, with regressions. |
| `RuleGeneration.v`, `Compiler.v`, `CompilerExamples.v` | `rules.setup`/`gen_*_rules`/`dobackl` and generic `proofrule`/`seqtactics` composition, with rechecked proposals. |
| `Search.v`, `SearchExamples.v`, `LazySearch.v`, `LazySearchExamples.v` | `prove` and generic `prover` search, exact backlink execution and bounded iterative deepening. |
| `FastGeneration.v`, `Relevance.v`, `RelevanceExamples.v` | Search ordering/efficiency work around `rules.setup`; `Relevance.v` is separately tested and is not wired into the active search path. |
| `Adapter.v`, `AdapterExamples.v`, `Certification.v` | Integration of FO rule/trace data with generic proof graphs and soundness checks. |
| `Witness.v`, `WitnessExamples.v` | New synthesis of the routing witness required by the Rocq graph certificate. |
| `SealedCompiler.v`, `SealedCompilerExamples.v` | New opaque evidence boundary for compiled rules; no direct OCaml counterpart. |
| `CertifiedSearch.v` | The active proof-producing entry point corresponding to `prove.run` plus generic graph checking. |
| `Benchmarks.v`, `BenchmarkRuns.v`, `Examples.v` | Validation of inputs from `benchmarks/fo`, bounded search runs, and example certificates. |

## Status and interpretation

The source map describes implementation **coverage**, not completion of every
proof-search target. `Benchmarks.v` validates all nine active input transcripts,
but it does not assert all nine have certified proofs. The last completed
evaluation reported three fully certified benchmark cases; later integration
was not fully rebuilt at that snapshot. See [`EVALUATION.md`](EVALUATION.md) and
[`CAPABILITIES.md`](CAPABILITIES.md) for measured results and current limits,
and [`COMPATIBILITY.md`](COMPATIBILITY.md) for detailed source-line citations and
the correction ledger.
