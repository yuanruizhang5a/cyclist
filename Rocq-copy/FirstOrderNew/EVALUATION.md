# Evaluation of FirstOrderNew

Status snapshot: 2026-10-05. Implementation and verification were stopped at the
user's request. This report records the completed work and outstanding issues.
Paths below are relative to `Rocq-copy/FirstOrderNew/` unless stated otherwise.

## Overall assessment

**FirstOrderNew contains a substantial, formally verified FO foundation and a
functioning generic cyclic proof-search pipeline. It is not yet complete against
the acceptance criteria in PLAN.md.**

The main remaining work is achieving and validating all nine benchmark
certificates, improving computation costs, and completing the reproducible
build/check workflow.

There are two distinct success stages:

- **Raw search success:** a graph passes structural and routing-witness
  acceptance.
- **Fully certified success:** the original goal is tied to a certificate that
  passes the frozen framework's full checker and yields a semantic validity
  theorem.

Six benchmarks reached the first stage; three reached the second stage in the
last completed benchmark run. Those measurements precede the final
evidence-sealing integration and are not a fresh verification of that revision.

## 1. Finished parts

| Part | Main files | Assessment |
| --- | --- | --- |
| Written plan and source correspondence | `PLAN.md`, `COMPATIBILITY.md` | Implemented. The compatibility document needs updates for the latest integration changes. |
| FO syntax and basic operations | `Syntax.v`, `Substitution.v`, `Definitions.v`, `Matching.v` | Implemented and compiled: variable classes, integer/function terms, tagged predicates, DNF sequents, substitutions, freshness operations, matching and validation. |
| Input parsing | `Input.v`, `InputExamples.v` | Implemented and tested against all nine benchmark inputs. Handles disequality, nested terms, variable scope and undefined predicates. |
| Source definition transcription | `SourceDefinitions.v` | Implemented. The literal source library diagnoses undefined `ADD_2`; a validated closed subset is supplied. |
| General FO semantics | `Semantics.v` | Implemented with arbitrary admissible models and positive least-fixed-point predicate semantics. Stage monotonicity, unfolding, leastness and substitution transport are proved. |
| Rank foundation | `Rank.v` | Implemented. Bounded occurrence worlds are proved equivalent to ordinary sequent validity. Minimum-stage descent is also proved separately. |
| Local rule families | `Rules.v`, `LocalRules.v`, `Unfolding.v` | Generic, theorem-backed constructors cover identity, contradiction, all six simplifications, structural rules, instantiation, unfolding, folding, weakening and backwards substitution, subject to documented side conditions. |
| Cyclic adapter | `Adapter.v` | Implemented. Logical tags remain distinct from occurrence-level trace IDs. Native positions are converted to dense framework IDs with proved rank correspondence. |
| Reusable certification | `Certification.v` | Implemented. Graph-wide countermodel advancement, liveness and witness obligations are derived generically rather than separately for every example. |
| Rule enumeration and compilation | `RuleGeneration.v`, `Compiler.v` | Implemented. Proposed applications are reconstructed through checked native constructors; expected labels are not treated as evidence. |
| Bounded generic search | `Search.v`, `LazySearch.v`, `FastGeneration.v`, `CertifiedSearch.v` | Implemented and operational. Includes iterative deepening, backlinks, macro rules and demand-driven candidate execution. No benchmark-name dispatcher is used. |
| Routing-witness synthesis | `Witness.v` | Implemented with incremental pruning, cached liveness and potential synthesis. Successful output is proved to satisfy the framework witness checker. |
| Evidence sealing | `SealedCompiler.v` | Implemented and compiled. Preserves application data while placing semantic evidence behind an opaque, data-only boundary. Its end-to-end performance benefit remains unmeasured. |
| Relevance heuristic | `Relevance.v` | Implemented and separately tested, with a permutation proof for ordering. Not integrated into the active search pipeline. |

### Demonstrated end-to-end examples

`Examples.v` previously compiled full certificates and validity theorems for:

- Equality identity.
- `true |- N(0)`.
- The genuinely cyclic goal `O(x) |- N(x)`.
- A renamed, modified `Entry`/`Tally` predicate library.
- The renamed zero case.

These demonstrate a genuine generic prover rather than benchmark-specific
proof handlers. The example certificates still require rebuilding against the
latest evidence-sealing integration.

### Soundness and independence

The source audit found:

- No `Admitted`, project-defined proof axioms, or disabled checking mechanisms.
- Standard-library classical reasoning and description/choice principles are
  used and audited.
- The standalone core has no Cyclic or LTL imports.
- `proved j` requires both full checker acceptance and equality between the
  graph root and the requested goal.

The last checked `Cyclic` and `LTL` source/documentation hashes matched the
starting baseline. Existing user changes in those directories were preserved.

## 2. Unfinished benchmark acceptance

The following table records the last completed benchmark measurements, before
the final evidence-sealing integration. See `BenchmarkReport.md` for budgets,
timings and historical measurements.

| Benchmark | Raw search | Full certificate |
| --- | --- | --- |
| 01: odd implies natural | Found, 18 nodes | Verified in the last completed run |
| 02: even/odd implies natural | Found, 37 nodes | Not completed |
| 04: natural implies odd/even | Found, 15 nodes | Verified in the last completed run |
| 05: naturals imply `Q` | Unknown at a smaller depth; deeper runs timed out | Not obtained |
| 07: addition zero right | Found, 14 nodes | Verified in the last completed run |
| 08: addition preserves naturalness | Runs timed out | Not obtained |
| 09: addition successor right | Found, 43 nodes | Not completed |
| 13: naturals imply hydra | Unknown at a smaller depth; deeper runs timed out | Not obtained |
| 14: naturals imply `N2` | Found, 25 nodes | Not completed |

**The all-nine fully certified acceptance target has not been met.**

Timeouts do not establish invalidity, insufficient rules, or an unavoidable
trace-format obstruction.

## 3. Difficulties in the unfinished parts

### A. Search growth: benchmarks 05, 08 and 13

This is currently the largest operational difficulty. Contraction-style
unfolding retains the original predicate while adding descendants. Consequently:

- Antecedents accumulate predicate copies.
- More unfolding and backlink candidates become available.
- Matching and witness checking become more expensive.
- DFS can spend its budget unfolding hypotheses that are less useful for the
  current goal.

For benchmark 08, recorded attempts grew from 18 to 35 to 52 graph nodes. The
difficulty is therefore more than simply increasing the depth limit.

The new relevance heuristic addresses part of this by ordering hypotheses using
variables that block matching against right-hand clause heads. It has not been
integrated or evaluated on these three targets.

### B. Large dependent proof objects: benchmarks 02, 09 and 14

These goals already produced raw graphs. The obstacle occurred when staging and
checking the full dependent certificates.

Earlier benchmark compilation took approximately 559 seconds and 10.5 GiB peak
memory. Some larger staging attempts timed out or encountered a compiler signal.

The suspected cause is strong normalization of semantic evidence embedded in
graph payloads, rather than merely the number of graph nodes.

`SealedCompiler.v` was added to reduce this expansion. Its correctness and
application-data agreement are proved, but the larger benchmark certificates
have not yet been rerun successfully with that integration.

### C. Framework routing is stricter than the original trace criterion

The frozen framework requires one optional followed tag per node. That choice
must work across every relevant outgoing edge.

The original cyclic criterion allows a suitable progressing trace for each
infinite path. Such traces may depend on the path or traversal history.

A regression demonstrates a graph accepted by the relational criterion that
cannot use the fixed-node witness format. This is a genuine coverage limitation.
However, it has not been proved to explain the current benchmark failures.
Different graph layouts, ordering or unfolding may resolve some cases.

### D. Final-check rejection does not resume search

The active engine first searches using structural and routing acceptance, then
calls the stronger full-check packaging gate.

If that final gate rejects the selected graph, `prove` returns `None`; it does
not resume exploration of alternatives.

This does not undermine successful-result soundness. It is a control-flow and
completeness gap. It requires either a proof connecting the earlier acceptance
criterion to full acceptance, or final-check rejection integrated into
backtracking.

### E. Well-formedness preservation is not completely formalized

Local certificates establish semantic and trace obligations. They do not
universally establish that every premise satisfies `sequent_wfb`.

For example, general weakening can introduce an undefined predicate into a
stronger premise. That weakening remains semantically sound, but it does not
preserve the input-validation invariant.

The plan's blanket well-formedness-preservation requirement is therefore not
fully discharged. The required invariant must be stated precisely and enforced
or proved for generated applications.

## 4. Remaining engineering and verification work

- **Fresh whole-project verification is incomplete.** The latest engine
  integration compiled, but downstream example and benchmark certificates need
  rebuilding against it.
- The most recent broader `rocq check` was interrupted; it must not be reported
  as passed.
- `BenchmarkRuns.v`, `Relevance.v` and `RelevanceExamples.v` are not included in
  the default build/check manifests.
- Some Makefile import dependencies are missing, creating potential clean
  parallel-build races.
- Frozen Cyclic prerequisites are assumed to exist; a reproducible staged
  prerequisite build is still needed.
- `COMPATIBILITY.md` contains outdated adapter and integration descriptions.
- The planned local README is absent.
- The full source definition library cannot validate until the meaning of
  `ADD_2` is supplied. The implementation reports this rather than inventing a
  definition.

## 5. Bottom line

**Finished:** the principal formal semantics, local calculus, Cyclic adapter,
reusable certification machinery, parser, checked compiler, witness synthesis
and generic bounded search.

**Not finished:** all-nine certificate coverage, performance validation of the
latest changes, complete invariant preservation, final-certification
backtracking, and fresh reproducible whole-project verification.

The work is stronger than a prototype, but should currently be described as a
substantial verified FO implementation with demonstrated cyclic proofs and
incomplete benchmark acceptance, not a completed implementation of every
planned deliverable.

## 6. .v files not successfully compiled yet

Compilation status was inspected without restarting compilation. The check
used the existing `.v`/`.vo` timestamps and `make -n all`.

### Files with no successful compilation recorded

**None identified.** All 36 existing `.v` files have corresponding `.vo` files
newer than their own sources, consistent with the successful individual
compilations recorded during implementation. This does not establish that every
artifact is current with respect to later dependency changes.

### Files not yet successfully recompiled against the latest integration

| File | Last successful object timestamp (+0800, 2026-10-05) | Outstanding compilation |
| --- | --- | --- |
| `Examples.v` | 02:13:24 | Rebuild against the later `CertifiedSearch.vo` from 04:11:46, which integrates `SealedCompiler`. `make -n all` schedules this compilation. |
| `BenchmarkRuns.v` | 03:58:31 | Rebuild against that same later `CertifiedSearch.vo`. This file is absent from the default Makefile target, so it requires an explicit build or manifest integration. |

These are dependency-stale artifacts, not files that have never compiled, and
not established source-level compilation failures. Their latest integrated
versions remain unverified until the recompilations succeed.

`Relevance.v` and `RelevanceExamples.v` successfully compiled separately; their
remaining issue is integration into the build and active search workflow, not
compilation failure.
