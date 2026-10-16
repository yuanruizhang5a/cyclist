# LPL implementation validation

The implementation follows D1–D4 and all eight implementation stages in
[IMPLEMENTATION_PLAN.md](IMPLEMENTATION_PLAN.md). The final syntax audit adds
explicit reflection for the FOL grammar and well-formedness predicates, plus
proofs that capture-avoiding and sorted label substitutions preserve their
syntax invariants. The API and semantic conventions are in [README.md](README.md).

## Learner comments

All 24 `.v` files now include reading guides and explanations of their central
definitions, proof strategies, module connections and benchmark steps. A
[comment audit](validation-logs/20261016T172216122771Z/CommentAudit.json) compares
each file with its version before annotation, removing nested comments and
preserving quoted strings: all code-token sequences are unchanged. It also
confirms that every current source hash matches the new successful benchmark
run and all 13 `Cyclic/` files retain their original bytes.

The benchmark build below was rerun after annotation. The independent kernel,
existing-theory regression and initial scope records are preserved from the
implementation verification; the comment update changes no definitions or
proof terms.

## Proof obligations

| Obligation | Implemented evidence |
| --- | --- |
| Arbitrary signatures and models | `Signature.v`, `Semantics.v`; independent Boolean and integer instances and an abstract-model functor in `Benchmarks/Signatures.v` |
| Recursive pure-FOL quantifier bodies, arities, labels and tags | `pureb_spec`, `term_wfb_spec`, `formula_program_wfb_spec`, `judgment_wfb_spec` in `Syntax.v` |
| Capture avoidance and substitution preservation | `subst_fo_correct` in `Semantics.v`; `subst_fo_wf`, `subst_fo_pure`, and sorted label-substitution preservation in `Syntax.v` |
| Assignments, tests and context freshness | Exact assignment/test semantic laws and `switch_semantics` in `Semantics.v`; the mutual freshness proof includes program assignments, test guards and bound variables |
| Both label-variable sorts | `eval_world_substitution`, `eval_world_label_substitution`, `eval_trace_label_substitution`; no world-to-trace substitution |
| Append labels and nonempty assertions | Label unit/length laws, `label_nonemptyb_spec`, `valid_admissible`, `false_sequent` in `Semantics.v` |
| Mathematical counterexample minima | `minimum_spec`, `false_minimum_exists` in `Progress.v`, using summed trace lengths |
| Trace transport and progress | `sequence_nonincrease`, `choice_nonincrease`, `star_nonincrease`, `assignment_decrease`, `test_decrease`, `suffix_decrease`, `dual_suffix_decrease`, and switch transport in `Progress.v` |
| All rule families and checked local generation | `Rules.v`, `RuleGeneration.v`; 50 exact premise-shape checks in `Benchmarks/RuleCoverage.v` |
| Certification through the unchanged framework | `raw_check_sound` in `Certification.v`, constructing a certificate and applying `certificate_sound` |
| Manual acyclic and cyclic certificates | Six-node assignment-change proof, 11-node star cycle, 12-node star cycle with explicit tag renaming; explicit graph scripts and witnesses |
| Complex all-visited-state invariants | `CounterLoop.v` and `NestedProgram.v`, proved for arbitrary finite iterations by semantic induction |

The star certificates preserve a first-state observation. The two complex
all-visited-state examples are direct semantic proofs, not cyclic certificates.
These proof modes are recorded separately in the benchmark report. Star does
not require an execution to reach a loop exit.

## Timed benchmark build

Run from `Rocq-copy/`:

```sh
make lpl
make lpl-benchmarks
```

All **15/15** isolated units passed after annotation in run
`20261016T172216122771Z`. Every unit used the unchanged 600-second limit;
the slowest took 6.953 seconds. [BENCHMARK_RESULTS.md](BENCHMARK_RESULTS.md)
contains individual commands, timings, logs and assumptions. Its JSON includes
hashes of all 24 LPL source files, including common dependencies. A final
`make -n lpl` reported that the build was current.

The one development timeout and the auxiliary proof simplification that fixed
it are documented in the report; the cyclic certificate was retained.

## Independent kernel check

The implementation was also checked independently before annotation with:

```sh
timeout --signal=KILL 600s rocq check -silent -Q . CyclistRocq \
  CyclistRocq.LPL.Syntax \
  CyclistRocq.LPL.Benchmarks.CyclicTags \
  CyclistRocq.LPL.Benchmarks.Quantifiers \
  CyclistRocq.LPL.Benchmarks.NestedProgram
```

The check **passed with exit 0 in 26.082 seconds**. It checks the new syntax
lemmas, shared rule/progress/certification
dependencies, cyclic certificate, quantifier proof, and arbitrary-predicate
invariant. The [machine record](validation-logs/20261016T165938090755Z/KernelCheck.json)
preserves its command, exit status and elapsed time; the silent compiler
output is retained beside it.

## Existing-theory regressions

Both regressions passed after build integration, with a 600-second limit:

| Command from `Rocq-copy/` | Seconds | Exit |
| --- | ---: | ---: |
| `timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LTL/Examples.v` | 2.266 | 0 |
| `timeout --signal=KILL 600s rocq compile -Q . CyclistRocq FirstOrder/Search.v` | 134.589 | 0 |

The commands, timings and retained output paths are in
[Regressions.json](validation-logs/20261016T165938090755Z/Regressions.json).
The final additional changes affect LPL syntax proofs and documentation;
neither regression imports LPL.

## Initial scope and assumptions audit

The [source audit](validation-logs/20261016T165938090755Z/SourceAudit.json)
compares against the preserved [baseline](validation-logs/20261016T165938090755Z/Baseline.json):

- All **13 files** in `Cyclic/`, including generated artifacts, match exactly;
  the directory contains no additional files.
- All **29 pre-existing non-LPL `.v` sources** retain their original bytes.
- All 24 initial LPL source hashes matched that implementation benchmark run;
  the comment audit above records the current sources.
- No admitted proofs, project-defined axioms, custom tactics, external-library
  imports, or project FirstOrder/LTL imports occur in LPL sources.
- `git diff --check` passes. Changes outside `LPL/` are the explicit build-file
  entries and top-level usage documentation.

`Print Assumptions` in the final benchmark logs reports only these
standard-library principles across the audited exported theorems and rule
kernels:

- `Classical_Prop.classic`
- `Description.constructive_definite_description`
- `ClassicalEpsilon.constructive_indefinite_description`
- `FunctionalExtensionality.functional_extensionality_dep`

Abstract signatures, model interpretations and the arbitrary benchmark
predicate remain explicit module parameters; they supply no constructor laws,
predicate decision procedures or unproved soundness statements. The finite
framework witness remains conservative, as described in the plan; acceptance
of every manuscript preproof and proof-search completeness are outside scope.
