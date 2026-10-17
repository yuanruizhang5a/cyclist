# LPL refinement 2 validation

The [saved plan](refine-2-plan.md) is implemented with opaque unary atom/action
carriers and exactly eight primitive formula constructors. API and generation
order are documented in [README.md](README.md) and
[RULE_EXPANSIONS.md](RULE_EXPANSIONS.md). The [machine summary](validation-logs/refine-2/Summary.json)
retains baseline, development and final results.

## Final verification

Compiler: `The Rocq Prover, version 9.1.0 / compiled with OCaml 4.14.1`.
Final benchmark run: `20261017T164319313299Z`.

| Check | Result |
| --- | --- |
| `python3 -B build.py --common` | Passed; 22 common modules, dependency/artifact hashes validated |
| `python3 -B run_benchmarks.py --suite all` | 29/29 passed: 15 FOPL and 14 PPL |
| Benchmark compilation time, summed | 39.036 seconds |
| Slowest benchmark | `FOPL/Benchmarks/Signatures.v`, 13.284 seconds |
| `python3 -B check_integrity.py --kernel --scope --log-dir validation-logs/refine-2` | Passed |
| Independent recursive kernel check | 51/51 modules; 82.098 seconds; exit 0 |
| Exact premise-shape checks | 50 FOPL / 53 PPL |
| Baseline theorem/lemma/example statements | 388 retained in order; no new cases |
| Fresh outside-LPL comparison | 3,992 files; zero added, missing or changed |

Every compiler/kernel command retains the **600-second limit**. The final
common build reused the current 22 artifacts; all changed modules had already
been recompiled during implementation. Every benchmark was compiled again in
the final run. Per-source commands, hashes and timings are retained in
[BENCHMARK_RESULTS.md](BENCHMARK_RESULTS.md) and [JSON](BENCHMARK_RESULTS.json).
The independent [kernel record](validation-logs/refine-2/KernelCheck.json)
and [output](validation-logs/refine-2/KernelCheck.log) cover all sources and
recursive dependencies without `-admit` or `-norec`.

## Preservation, representation and assumptions

The [source audit](validation-logs/refine-2/SourceAudit.json) checks all 51
sources against `_CoqProject` and the 22-common/29-benchmark build inventory,
artifact hashes, import boundaries, duplicate files and forbidden proof shortcuts.
No admitted obligations, project-defined axioms, disabled checks, custom tactics
or solver imports remain.

The [representation audit](validation-logs/refine-2/RepresentationAudit.json)
checks the exact eight constructors, unary syntactic/semantic interfaces,
derived definitions and view reconstruction lemmas, candidate order, shared
kernel reuse, checker endpoint and common polymorphic trace algebra.

All **185 frozen FOPL statements** remain textually unchanged and in order in
the [original-claim audit](validation-logs/refine-2/BenchmarkPreservation.json).
The [fresh baseline audit](validation-logs/refine-2/RefinementClaimPreservation.json)
compares all 388 statements across the existing 29 units; PPL normalization
removes only the obsolete empty atom arguments and action unit/value fields.
Rejection values, hypotheses, invariant statements, graph metrics, theorem
names and case counts are retained.

The legacy oracle differs from `../LPL-old/` only in imports; its signature
remains byte-identical. Production code never imports the oracle.
[FOPL/Compatibility.v](FOPL/Compatibility.v) proves full formula/program
semantics (including empty traces and raw syntax), labels, validity,
counterexample histories, minima and ranks. Tag/judgment well-formedness is
preserved forward because derived spellings equal their primitive expansions;
constructor-sensitive reflection is no longer meaningful. This representation
change is detailed in [FOPL_COMPATIBILITY.md](FOPL_COMPATIBILITY.md).

The targeted [assumptions audit](validation-logs/refine-2/Assumptions.log)
covers atomic descent, all four action rules, derived semantics, substitution,
quantifier rules, generation and `raw_check_sound`. It completed in
2.222 seconds with zero command errors. Its only principles
are classical excluded middle, definite/indefinite description, and dependent
functional extensionality from the standard library. Signature/model
hypotheses remain explicit parameters.

Labels still append, program traces overlap, complete assertions are nonempty,
tests observe `[s; s]`, and quantified bodies remain pure. Existing genuine
cycles, tag renaming, malformed/nonprogressing rejection, assignment/freshness
checks, nondeterminism and complex all-state invariants all pass. No semantic
oracle or proof search was introduced. The unchanged framework still selects
at most one tag per node.

## Baseline and actual development failures

Before theory edits, the plan, compiler, source snapshot/inventory and benchmark
claims were saved in `validation-logs/refine-2/baseline/`. That baseline passed
29/29 units with 40.200 summed
benchmark compile seconds. The baseline source snapshot also backs the claim audit.

The first [migration run](validation-logs/refine-2/MigrationRun.json) passed
22/29. FOPL Tests and PPL Tests/Nondeterminism needed to apply `Neg Truth` to
`Truth`; PPL Instances/SafetySystem/NestedProgram still used removed fields.
RegularPrograms reported its failing Nondeterminism dependency. The second
[development run](validation-logs/refine-2/DevelopmentRun2.json) passed 27/29;
SafetySystem and NestedProgram retained obsolete action arguments. All failures
and their original timings/logs are retained and were fixed without changing
claims. Common-layer development logs also retain syntax/conversion failures
encountered while adapting the proofs. A first assumptions probe used two
incorrect qualified names; its [log](validation-logs/refine-2/DevelopmentAssumptions.log)
is retained alongside the corrected successful audit. No timeout occurred.

## Scope and cleanup

The [outside baseline](validation-logs/refine-2/OutsideBaseline.json) was created
before implementation and compared by the final [scope audit](validation-logs/refine-2/OutsideAudit.json).
The cyclic framework, frozen reference, manuscript and unrelated workspace
files are unchanged, including pre-existing user files. `.git/` metadata is
excluded from this content comparison and was not modified.

Obsolete shared payload plumbing was removed from declarations. Safety overlap,
composition and finite powers now use `Semantics.TraceAlgebra`; useful public
adapters and the test-only oracle are retained. This migration made no source
file obsolete, required no garbage moves, and permanently deleted no files.
Historical refinement-1 cleanup records remain in [CLEANUP.json](CLEANUP.json).
Documentation links, Python syntax and `git diff --check` pass.
