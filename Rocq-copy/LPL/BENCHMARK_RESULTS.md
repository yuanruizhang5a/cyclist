# Refinement benchmark results

UTC run `20261017T054643680535Z`: **29/29 attempted units passed**.

Every unit was compiled with `timeout --signal=KILL 600s` after its dependencies. These records describe this run only; earlier reports/logs are historical evidence.

```text
The Rocq Prover, version 9.1.0
compiled with OCaml 4.14.1
```

| Suite | Unit | Seconds | Exit | Proof mode | Output / assumptions |
| --- | --- | ---: | ---: | --- | --- |
| fopl | Labels | 0.731 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-Labels.v.txt) |
| fopl | Signatures | 13.878 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-Signatures.v.txt) |
| fopl | Updates | 0.676 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-Updates.v.txt) |
| fopl | Tests | 0.765 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-Tests.v.txt) |
| fopl | RegularPrograms | 0.778 | 0 | semantic proof / instance checks | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-RegularPrograms.v.txt) |
| fopl | Booleans | 0.726 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-Booleans.v.txt) |
| fopl | Quantifiers | 0.744 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-Quantifiers.v.txt) |
| fopl | Temporal | 0.746 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-Temporal.v.txt) |
| fopl | AssignmentChange | 0.752 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-AssignmentChange.v.txt) |
| fopl | RuleCoverage | 1.343 | 0 | syntax / rule / checker checks | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-RuleCoverage.v.txt) |
| fopl | CheckerNegative | 0.505 | 0 | syntax / rule / checker checks | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-CheckerNegative.v.txt) |
| fopl | Cyclic | 1.122 | 0 | cyclic certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-Cyclic.v.txt) |
| fopl | CyclicTags | 1.335 | 0 | cyclic certificate | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-CyclicTags.v.txt) |
| fopl | CounterLoop | 0.868 | 0 | semantic proof / instance checks | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-CounterLoop.v.txt) |
| fopl | NestedProgram | 6.726 | 0 | semantic proof / instance checks | [log](benchmark-logs/refine-20261017T054643680535Z/FOPL-Benchmarks-NestedProgram.v.txt) |
| ppl | Instances | 1.069 | 0 | semantic proof / instance checks | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-Instances.v.txt) |
| ppl | LabelsRelations | 0.239 | 0 | syntax / rule / checker checks | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-LabelsRelations.v.txt) |
| ppl | AtomicActions | 1.104 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-AtomicActions.v.txt) |
| ppl | Nondeterminism | 0.746 | 0 | semantic proof / instance checks | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-Nondeterminism.v.txt) |
| ppl | Booleans | 0.446 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-Booleans.v.txt) |
| ppl | Tests | 0.450 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-Tests.v.txt) |
| ppl | RegularPrograms | 0.412 | 0 | semantic proof / instance checks | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-RegularPrograms.v.txt) |
| ppl | Temporal | 0.418 | 0 | semantic proof / generated certificate | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-Temporal.v.txt) |
| ppl | RuleCoverage | 0.920 | 0 | syntax / rule / checker checks | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-RuleCoverage.v.txt) |
| ppl | CheckerNegative | 0.259 | 0 | syntax / rule / checker checks | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-CheckerNegative.v.txt) |
| ppl | Cyclic | 0.862 | 0 | cyclic certificate | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-Cyclic.v.txt) |
| ppl | CyclicTags | 1.076 | 0 | cyclic certificate | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-CyclicTags.v.txt) |
| ppl | SafetySystem | 0.451 | 0 | semantic proof / instance checks | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-SafetySystem.v.txt) |
| ppl | NestedProgram | 0.671 | 0 | semantic proof / instance checks | [log](benchmark-logs/refine-20261017T054643680535Z/Benchmarks-PPL-NestedProgram.v.txt) |

## Checked coverage and graph sizes

| Suite | Unit | Premise-shape examples | Graph/tag measurements |
| --- | --- | ---: | --- |
| fopl | AssignmentChange | 0 | distinct_tag_count=1, graph_size=6 |
| fopl | RuleCoverage | 50 |  |
| fopl | Cyclic | 0 | graph_size=11, distinct_tag_count=1 |
| fopl | CyclicTags | 0 | graph_size=12, distinct_tag_count=2 |
| ppl | AtomicActions | 0 | br_graph_nodes=4, br_tag_count=0, bl_graph_nodes=2, bl_tag_count=0, dr_graph_nodes=2, dr_tag_count=0, dl_graph_nodes=4, dl_tag_count=0 |
| ppl | RuleCoverage | 53 |  |
| ppl | Cyclic | 0 | graph_size=12, distinct_tag_count=1 |
| ppl | CyclicTags | 0 | graph_size=13, distinct_tag_count=2 |

## Commands

Commands ran from `Rocq-copy/LPL/`.

```sh
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/Labels.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/Signatures.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/Updates.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/Tests.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/RegularPrograms.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/Booleans.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/Quantifiers.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/Temporal.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/AssignmentChange.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/RuleCoverage.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/CheckerNegative.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/Cyclic.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/CyclicTags.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/CounterLoop.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob FOPL/Benchmarks/NestedProgram.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/Instances.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/LabelsRelations.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/AtomicActions.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/Nondeterminism.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/Booleans.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/Tests.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/RegularPrograms.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/Temporal.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/RuleCoverage.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/CheckerNegative.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/Cyclic.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/CyclicTags.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/SafetySystem.v
timeout --signal=KILL 600s rocq compile -Q .. CyclistRocq -noglob Benchmarks/PPL/NestedProgram.v
```

## Evidence and limits

The source hashes and dependency hashes are retained in the JSON report. `Print Assumptions` output is in each compiler log; exported names are also listed in JSON. The JSON records admissibility, antecedent, relation, and execution example statements as nonvacuity evidence, retaining their conditions and negative cases. Concrete checker computations and semantic examples are distinguished from validity theorems in the source.

Cyclic/CyclicTags require real backlinks and explicit finite tag/potential witnesses. The complex all-visited-state invariants use direct semantic proofs. The framework selects at most one tag per node; acceptance of every manuscript preproof is not claimed.

T1 is resolved by the user: tests evaluate their guard on `[s; s]`. No benchmark is allowed to increase the 600-second cap. Failed/timed-out cases remain failures in this record.
