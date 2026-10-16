# LPL benchmark results

UTC run: `20261016T165938090755Z`. **15/15 units passed.**

```text
The Rocq Prover, version 9.1.0
compiled with OCaml 4.14.1
```

Common dependencies: `make lpl-common`, exit 0, 0.002s.
Every isolated benchmark uses `timeout --signal=KILL 600s`; the limit is never increased.

| Unit | Seconds | Exit | Evidence | Compiler output / assumptions |
| --- | ---: | ---: | --- | --- |
| Labels | 0.465 | 0 | D1/D4, units, differing states, overlap; 1-node certificate | [log](benchmark-logs/20261016T165938090755Z/Labels.txt) |
| Signatures | 6.958 | 0 | arbitrary models and independent Boolean signature; leaf certificates | [log](benchmark-logs/20261016T165938090755Z/Signatures.txt) |
| Updates | 0.475 | 0 | identity, changed/dependent assignments, intermediate states; pure certificate | [log](benchmark-logs/20261016T165938090755Z/Updates.txt) |
| Tests | 0.531 | 0 | successful/failed and trace-sensitive tests; 2-node certificate | [log](benchmark-logs/20261016T165938090755Z/Tests.txt) |
| RegularPrograms | 0.453 | 0 | sequence, choice, zero/one/nested finite iteration; semantic validity | [log](benchmark-logs/20261016T165938090755Z/RegularPrograms.txt) |
| Booleans | 0.514 | 0 | mixed modal Boolean formula; 3-node certificate | [log](benchmark-logs/20261016T165938090755Z/Booleans.txt) |
| Quantifiers | 0.616 | 0 | capture avoidance, shadowing, eigenvariables; 2-node certificate | [log](benchmark-logs/20261016T165938090755Z/Quantifiers.txt) |
| Temporal | 0.468 | 0 | immediate/postponed suffix, dual, first, next-at-end, sum measure; certificate | [log](benchmark-logs/20261016T165938090755Z/Temporal.txt) |
| AssignmentChange | 0.551 | 0 | changed next-state value; 6-node certificate, 1 distinct tag | [log](benchmark-logs/20261016T165938090755Z/AssignmentChange.txt) |
| RuleCoverage | 0.992 | 0 | 50 exact rule/request premise shapes, positive/negative syntax checks | [log](benchmark-logs/20261016T165938090755Z/RuleCoverage.txt) |
| CheckerNegative | 0.349 | 0 | open/dangling/mismatched graphs, absent tags, closed nonprogressing cycle | [log](benchmark-logs/20261016T165938090755Z/CheckerNegative.txt) |
| Cyclic | 0.756 | 0 | 11-node star cycle, real backlink, 1 distinct tag, explicit potential | [log](benchmark-logs/20261016T165938090755Z/Cyclic.txt) |
| CyclicTags | 0.914 | 0 | 12-node star cycle, explicit tag-renaming backlink, 2 distinct tags | [log](benchmark-logs/20261016T165938090755Z/CyclicTags.txt) |
| CounterLoop | 0.457 | 0 | guarded integer decrement loop, every visited state and finite stopping point | [log](benchmark-logs/20261016T165938090755Z/CounterLoop.txt) |
| NestedProgram | 2.885 | 0 | nested sequence/choice/star, arbitrary uninterpreted predicate of unchanged variable | [log](benchmark-logs/20261016T165938090755Z/NestedProgram.txt) |

## Commands

Commands ran from `Rocq-copy/`, after compiling common dependencies.

```sh
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Labels.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Signatures.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Updates.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Tests.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/RegularPrograms.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Booleans.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Quantifiers.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Temporal.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/AssignmentChange.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/RuleCoverage.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/CheckerNegative.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Cyclic.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/CyclicTags.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/CounterLoop.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/NestedProgram.v
```

## Scope and assumptions

All requested primitive/derived rule families are implemented; generators return proof-backed records and check object syntax, conclusions, and edge endpoints. RuleCoverage checks 50 exact premise lists, including non-head positions and the empty context-only weakening premise. Pure goals stop at the caller-supplied proof boundary.

Cyclic and CyclicTags are actual star cycles with explicit finite tag/potential witnesses. They preserve a first-state observation. CounterLoop and NestedProgram separately prove properties of **every visited state**, over arbitrary finite iterations; these two complex invariants are direct semantic proofs, not cyclic graph certificates. No claim of mandatory loop exit is made.

Print Assumptions output is retained in the linked logs. The union for concrete exported theorems and representative rule/certification kernels consists only of standard-library classical excluded middle, definite/indefinite description, and functional extensionality. No project-defined soundness axioms or admitted proofs are used. Signature/model parameters in the abstract-model functors are explicit parameters, not soundness assumptions.

The framework witness is conservative: it chooses at most one tag per node. Acceptance of every manuscript preproof is not claimed. No proof search, witness discovery, external solver, or project FirstOrder/LTL imports are present.

## Development timeout and simplification

An initial Cyclic.v run hit the 600-second limit (exit 137) while kernel conversion compared an entire proof-carrying backlink record in an auxiliary existential example. That auxiliary check was replaced with a Boolean check of the node payload and companion index. The real backlink, star graph, semantic rules, certificate, and validity theorem were retained. The final timed run is reported above. No expensive obligation was retried with a larger limit.

## Immutable framework

```text
Cyclic/Framework.v  b9f93e89931a196bb1d2f7649f240cb65920ed972fa02a2ae4af46a2e7a3ce02
Cyclic/Relations.v  85f1f25747e3eb661f24f50b6a9e6aae3cbcb173169bb7bfb6d06ac7addeb90f
```

The complete Cyclic directory also matched the pre-implementation file manifest during the implementation audit.

See [VALIDATION.md](VALIDATION.md) for the independent kernel check, existing-theory regressions, and source-scope audit.
