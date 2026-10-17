# LPL integrity validation

The implementation contains **51 Rocq sources**, each listed exactly once in
`_CoqProject` and the build inventory. The eight generic implementations live
at the root; FOPL supplies its specialization, and the two benchmark suites
exercise both instances. [README.md](README.md) describes the public API.

## Fresh build and benchmarks

Run `20261017T054643680535Z` rebuilt every source from scratch using Rocq 9.1.0
(OCaml 4.14.1). All **29/29 benchmark units passed**: 15 FOPL and 14 PPL.
All 22 common modules were freshly compiled. The hard per-command limit
remains 600 seconds; the slowest benchmark took
**13.878 seconds**.
Commands, hashes, timings, proof modes, assumptions and compiler output are in
[BENCHMARK_RESULTS.md](BENCHMARK_RESULTS.md) and its
[JSON record](BENCHMARK_RESULTS.json).

From `Rocq-copy/LPL/`:

```sh
make check
```

This runs the benchmarks, source/build/reference audits and a recursive
`rocq check` of every project module. For a previously built full suite:

```sh
python3 -B check_integrity.py --kernel
```

## Independent checking and source integrity

All **51 modules** and their recursive dependencies passed independent kernel checking in **89.053 seconds** (exit 0).
The [machine record](validation-logs/integrity-20261017T054551957870Z/KernelCheck.json) contains the complete module
list and actual command; [output](validation-logs/integrity-20261017T054551957870Z/KernelCheck.log) is retained.
The check uses neither `-admit` nor `-norec`.

The [source audit](validation-logs/integrity-20261017T054551957870Z/SourceAudit.json) checks the source/project/build
inventories, compiled-artifact and dependency hashes, stale reports, duplicate
sources, import boundaries, unsupported namespaces and forbidden proof shortcuts.
There are no admitted proofs, project-defined axioms, disabled kernel checks,
custom tactics or external solver imports.

The [preservation audit](validation-logs/integrity-20261017T054551957870Z/BenchmarkPreservation.json) confirms all
**185 original FOPL theorem/lemma/example statements** remain unchanged and
in order. FOPL retains its **50** exact premise-shape checks; PPL has **53**.
Original FOPL cycles remain 11/12 nodes; PPL atomic-action cycles remain 12/13
nodes. Their explicit witnesses and backlinks are checked. Complex
all-visited-state invariants remain direct semantic proofs over arbitrary
finite stopping points. Those proof modes are distinguished in the report.

## Frozen reference and assumptions

The legacy syntax, semantics and progress remain separate test-only sources.
They differ from the immutable `../LPL-old/` sources only in imports. Their
shared `FOPL/Signature.v` must remain byte-identical to the frozen signature;
this is enforced on every integrity check. Production modules do not import
the oracle. Full arbitrary-signature/model semantic and rank preservation is
proved in [FOPL/Compatibility.v](FOPL/Compatibility.v); see
[FOPL_COMPATIBILITY.md](FOPL_COMPATIBILITY.md).

The compiler logs retain `Print Assumptions` output for representative rules,
certification, preservation and positive benchmark theorems. The audited
standard-library principles are classical excluded middle, definite and
indefinite description, and dependent functional extensionality. Signature,
model and preservation hypotheses remain explicit parameters.

The targeted [assumptions audit](validation-logs/integrity-20261017T054551957870Z/Assumptions.log)
also covers the minimum-successor lemma, all four atomic rules, generator
guarantees and checker soundness.

D1–D4 and T1 remain unchanged: labels append, asserted labels are nonempty,
quantifier bodies remain pure FOL with label-aware freshness, and test guards
are evaluated on `[s; s]`. Generation remains local; there is no proof search,
automatic backlink/witness discovery or semantic truth oracle. The unchanged
cyclic framework selects at most one tag per node; completeness is outside scope.

## Cleanup and build reliability

[CLEANUP.json](CLEANUP.json) records recoverable removal of obsolete snapshots,
diagnostic binaries, old verification runs, caches, a duplicated progress
summary, the invariant-helper forwarding file and the duplicate signature.
Original plans, requirements, manuscript sources, necessary semantic reference
files and all benchmark statements are retained. Current `.vo` files are kept
because Rocq imports require them; unused generated sidecar files are removed.

The [cleanup audit](validation-logs/integrity-20261017T054551957870Z/CleanupAudit.json) confirms all 1,353
original files remain unchanged or recoverable, and all surviving Rocq
implementations retain their declarations and proofs apart from import edits.
The project shrank from about 222 MiB to 130 MiB.

No files were permanently deleted. Removed files are stored outside the project
in the archive recorded by `CLEANUP.json`. The session could not write to
`~/Garbage`, so the recoverable archive is under `/tmp/`.

The [outside-file audit](validation-logs/integrity-20261017T054551957870Z/OutsideAudit.json) compares all manifested
non-LPL workspace files against their state at the start of this cleanup,
including pre-existing edits. No outside file was changed. `.git/` metadata
is excluded from the content manifest and was not edited.

[Failure-path checks](validation-logs/integrity-20261017T054551957870Z/BuildFailureChecks.json) verify that failed
compilations clear dependency-traversal state, failed common builds replace
old success reports, and outside report paths are rejected before writing.
Builds run from `LPL/`, suppress unused globalization output, and validate
compiler/source/dependency/artifact hashes. Python syntax, documentation links
and `git diff --check` are also checked.
