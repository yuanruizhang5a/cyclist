# Measured benchmark runs

## Current engine: `lazy_iddfs` / `fast_source_menu`

The current compiled `CertifiedSearch` uses demand-driven work-stack search and
`FastGeneration.fast_source_menu`. Universal RHS goals use source-style matched
right unfolding; equation fallback is generated only with RHS Exist variables.
The environment remains exactly `Benchmarks.Env.defs = closed_source_definitions`.
All nine source acceptance targets remain unchanged. No benchmark-name dispatch,
hand derivation, engine/witness edit, or frozen source change was introduced.

### Current single-depth search, independently measured

Every row uses matching **32**, candidates **16**, combinations **8**,
simplification **16**, search fuel **2000**, and macro fuel **64**. Depth is
fixed per probe, with a nominal **120-second** process deadline. Lazy fuel now
counts work-stack transitions, including administrative transitions; it is not
the old eager DFS pop count.

| Target | Depth 3 result | Nodes / backlinks / union tag width | Wall seconds | Deeper observations |
| --- | --- | --- | ---: | --- |
| 01 odd → natural | Found | 18 / 1 / 3 | 0.28 | already returned |
| 02 even/odd → natural | Unknown IterationsExhausted | — | 10.33 | depth 4 Found: 37 / 2 / 3, 1.64 s |
| 04 natural → odd/even | Found | 15 / 1 / 2 | 0.31 | already returned |
| 05 naturals → Q | Unknown IterationsExhausted | — | 98.89 | depths 4, 5, 6 timed out at 120.01 s each |
| 07 addition zero right | Found | 14 / 1 / 2 | 0.27 | already returned |
| 08 addition → natural | process timeout | — | 120.01 | depths 4, 5, 6 timed out at 120.01 s each |
| 09 addition successor right | Found | 43 / 1 / 5 | 17.68 | already returned |
| 13 naturals → hydra | Unknown IterationsExhausted | — | 4.07 | depths 4, 5, 6 timed out at 120.01 s each |
| 14 naturals → N2 | Found | 25 / 1 / 4 | 0.42 | already returned |

All timeout rows represent unfinished processes (exit 124), not invented Rocq
Unknown values or node counts. A single failed iterative-deepening iteration
returns IterationsExhausted and hides the internal bounded-attempt reason.

### Current IDDFS `1–11`

The same generation/search budgets were reasonable for the six returned goals:

| Target | Raw result | Depth | Nodes | Backlinks | Union width | Wall seconds |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 01 | Found | 3 | 18 | 1 | 3 | 0.50 |
| 02 | Found | 4 | 37 | 2 | 3 | 12.55 |
| 04 | Found | 3 | 15 | 1 | 2 | 0.94 |
| 07 | Found | 2 | 14 | 1 | 2 | 0.30 |
| 09 | Found | 3 | 43 | 1 | 5 | 25.72 |
| 14 | Found | 3 | 25 | 1 | 4 | 1.34 |

IDDFS was not attempted for 05/08/13 after their depth-4–6 probes each consumed
the full deadline. This preserves their targets and records the compute gap;
it does not claim semantic invalidity or a routing-format obstruction.

### Current small regression profile

Candidates 4, combinations 2, simplification 16, matching 32, search fuel 20,
macro fuel 64, a single depth-3 iteration. This current suite completed in
16.96 s (independent compilation), returning:

* **Found:** 01 (18 nodes), 04 (15), 07 (14), 14 (25).
* **Unknown IterationsExhausted:** 02, 05, 08, 09, 13.

`BenchmarkRuns.v` recomputes these actual results. The previous all-unknown
regression was removed: it is false for the new engine. The old quick timings
in the file are explicitly named `historical_quick_wall_ms`.

### Current full certificates and staging status

The owned file stages actual generic search results with dependent graph/depth
transcripts and search equalities, synthesizes witnesses from those graphs,
proves their original roots and the **full** `Prover.C.raw_check`, and constructs
typed `Prover.proved` values. It also proves `exists p, Prover.prove limits goal
= Some p` for each certified target without rerunning search lazily inside
`finish_proof`.

| Target | Current full status |
| --- | --- |
| 01 | `certificate_01`, `benchmark_01_valid`, `benchmark_01_prove_returns` compiled |
| 04 | `certificate_04`, `benchmark_04_valid`, `benchmark_04_prove_returns` compiled |
| 07 | `certificate_07`, `benchmark_07_valid`, `benchmark_07_prove_returns` compiled |
| 02 | raw Found; larger dependent staging attempts timed out or exited with signal 11 |
| 09 | raw Found; dependent staging exceeded the 120-second deadline |
| 14 | raw Found; larger dependent staging attempts timed out or exited with signal 11 |
| 05 / 08 / 13 | no returned raw graph at the requested larger profiles |

Thus the unchanged **all-nine typed-certificate acceptance target is not met**.
No false full-success assertions, fabricated certificates, or Admitted are
present. The full failures above are computation/compiler observations, not
failed witness constraints. In particular, no trace-format incompatibility
has been established by these runs.

Certificate checking uses a generic proved stabilization transport:
`path_closure_extend`/`relation_closure_extend` show that a tested stable small
closure equals every larger-fuel closure. `saturation_check_full` proves the
EXACT frozen `C.relational_check` result from those checks and proved lower
bounds on its default fuels. `raw_check_from_saturation` then combines this
with the actual structural check and synthesized-witness theorem. The
stabilization checks use `lazy`; default exponential relational fuel is never
materialized by VM. This is proved equality with the frozen checker, not an
alternative acceptor. The stabilization transport is closed under the global
context; validity retains the existing standard-library classical dependencies.

### Concrete unsuccessful-frontier diagnostics

The diagnostic runner uses the same lazy transitions, explicitly at **40 work
steps**, depth 3 and macro fuel 64. Root menu statistics are executable tests:

| Target | Axioms | Simplifiers | Choice programs | Choice frontier counts | Initial backlink plans |
| --- | ---: | ---: | ---: | --- | ---: |
| 05 | 0 | 0 | 3 | [1, 2, 2] | 0 |
| 08 | 0 | 0 | 4 | [1, 2, 2, 1] | 0 |
| 13 | 0 | 0 | 2 | [2, 2] | 0 |

All three root menus have **zero matched right-unfold candidates**, as expected
for these universal-variable heads under the restored source restriction.
They have respectively 2, 3 and 2 left-unfold candidates. The traced diagnostic
returns FuelExhausted after respectively **15, 14, 16 executed attempts**; the
last attempted program inputs, with parser/internal Free IDs, are:

* 05: `N_1(v2) & N_2(s(v2)) & N_0(v0) |- Q_0(v0,v2)`.
* 08: `ADD_2(v8,v1,v12) & ADD_4(s(v8),v1,s(v12)) &
  ADD_3(s(s(v8)),v1,s(s(v12))) & N_0(s(s(v8))) & N_1(v1) |- N_0(s(v12))`.
  Here `_2` etc. denote logical tags on **ADD**, not the undefined source name
  `ADD_2`. Attempted graph sizes include 18 → 35 → 52 nodes.
* 13: `N_1(v2) & N_3(s(v2)) & N_2(0) |- H_2(s(v2),0)`.

These are actual bounded trace observations, not hand-selected proof states or
an assertion that every attempted application succeeded. They expose remaining
search/growth work for the engine owner without weakening the acceptance target.

### Current owned-file build

From `Rocq-copy/FirstOrderNew`:

```sh
ulimit -s 65536
rocq compile -Q .. CyclistRocq BenchmarkRuns.v
```

The final current build succeeded in **558.66 s**, peak RSS **10940496 KB**.
It verified the three typed certificates,
their full raw checks, `prove`-Some existence statements, current raw-result
regressions, and stabilization lemmas. Standard large-nat timing-literal
warnings concern historical data. All three concrete failed-frontier assertions,
including the final 08 assertion, compiled. An earlier current build without
that last assertion succeeded in 486.00 s.

Follow-up gaps: finish dependent staging for 02/09/14 without stack/compiler
failure; improve/diagnose the native search growth for 05/08/13 using the above
frontiers; then rerun the unchanged all-nine typed-certificate target. No claim
of an inherent conservative trace barrier is justified by the current evidence.

## Historical eager-engine session (superseded; not current results)

The remainder preserves the previous measurements for comparison. Its engine
used eager `iddfs`/`compiled_source_menu`, with unrestricted equation fallback.
Statements of no verified certificate and all-unknown quick results below
describe that historical session only.

### Historical environment and method

The prover is `CertifiedSearch.Make Benchmarks.Env`; the environment is the
unchanged `closed_source_definitions`. All nine original acceptance targets
remain in `Benchmarks.active_benchmarks`. Every execution calls the same
generic compiler/menu/search API; no goal-name dispatch or hand derivation is
used. Raw `Found` means native search plus the engine's routing acceptance. It
does **not** mean that `Prover.prove` returned a fully checked certificate.

Goals were compiled independently in `/tmp/opencode/fo-bench-probes`, preventing
one unfinished computation from hiding other rows. Only compact raw-search
statistics used `vm_compute`; `C.relational_check`/`C.raw_check` were never
evaluated with VM. Full packaging probes used `lazy` reduction. Wall times
below include compilation/import overhead and concurrent process scheduling;
they are observations, not timing theorems or reproducible performance limits.

### Historical initial requested profile

Generation: candidates **16**, combinations **8**, simplification **16**,
matching fuel **32**. Search: fuel **2000 per depth**, macro fuel **64**,
depths **1–11**. Each process had a nominal 60-second timeout.

| Target | Actual outcome | Depth | Nodes | Backlinks | Max predicates/node | Wall seconds |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 01 `odd_implies_natural` | Raw Found | 3 | 18 | 1 | 3 | 17.49 |
| 02 `even_or_odd_implies_natural` | Process timeout; no Rocq result | — | — | — | — | not captured; deadline 60 |
| 04 `natural_implies_odd_or_even` | Raw Found | 3 | 17 | 1 | 2 | 46.52 |
| 05 `naturals_imply_q` | Process timeout; no Rocq result | — | — | — | — | 65.90 |
| 07 `addition_zero_right` | Raw Found | 2 | 14 | 1 | 2 | 9.68 |
| 08 `addition_preserves_natural` | Process timeout; no Rocq result | — | — | — | — | 65.90 |
| 09 `addition_successor_right` | Process timeout; no Rocq result | — | — | — | — | 65.82 |
| 13 `naturals_imply_hydra` | Process timeout; no Rocq result | — | — | — | — | 65.82 |
| 14 `naturals_imply_n2` | Process timeout; no Rocq result | — | — | — | — | 65.82 |

The observed timeout wall time can exceed the nominal deadline. Except for the
first 02 wrapper, timed-out commands explicitly returned exit status **124**.
The 02 wrapper terminated without printing a result or timing. A process
timeout is not a fabricated `Search.Unknown` value. Unknown results also
do not expose a retained graph, so no node count is supplied for them.

### Historical smaller complete uniform profile

Generation: candidates **4**, combinations **2**, simplification **16**,
matching fuel **32**. Search: fuel **20**, macro fuel **64**, one depth-**3**
iteration (`first_depth = last_depth = 3`).

| Target | Returned raw result | Wall seconds |
| --- | --- | ---: |
| 01 | `Unknown IterationsExhausted` | 0.80 |
| 02 | `Unknown IterationsExhausted` | 2.79 |
| 04 | `Unknown IterationsExhausted` | 3.17 |
| 05 | `Unknown IterationsExhausted` | 6.43 |
| 07 | `Unknown IterationsExhausted` | 0.81 |
| 08 | `Unknown IterationsExhausted` | 28.00 |
| 09 | `Unknown IterationsExhausted` | 15.47 |
| 13 | `Unknown IterationsExhausted` | 1.75 |
| 14 | `Unknown IterationsExhausted` | 8.71 |

The historical version of `BenchmarkRuns.v` recomputed/asserted each outcome,
retained the whole suite, and derived `prove = None` for these nine quick
runs. Those assertions are superseded by the current results above. This was
budget-dependent failure to find a proof, **not falsity** of the
goals. The iterative-deepening wrapper reports `IterationsExhausted` after
its single failed bounded attempt; it does not retain that attempt's reason.
No all-nine-success assertion is present.

### Historical focused reproduction of the three raw successes

Generation remains the initial 16/8/16/32 profile. A generic single-depth setting
avoids replaying earlier depth iterations; it does not change the input goal.

| Target | Search fuel | Single depth | Compact result | Union of graph trace IDs | Wall seconds |
| --- | ---: | ---: | --- | ---: | ---: |
| 01 | 2000 | 3 | Found; 18 nodes, 1 backlink, max node width 3 | 3 | 12.33 |
| 04 | 2000 | 3 | Found; 17 nodes, 1 backlink, max node width 2 | 2 | 10.20 |
| 07 | 100 | 2 | Found; 14 nodes, 1 backlink, max node width 2 | 2 | 8.65 |

Those historical statistics are not the current regression results. Computing
that union does not compute the
relational fuel. The frozen checker's fuel is `S (3^(width*width))`; its graph
path bound is `S (nodes*nodes*relation_fuel)`. Neither bound was eagerly
materialized using VM in these runs.

### Historical full `prove` attempts and confirmed blocker

The following independent probes reduced `Prover.solvedb`, which calls the
actual `Prover.prove` and `finish_proof`. All used `lazy`, not VM:

| Target/profile | Nominal deadline | Observed wall seconds | Outcome |
| --- | ---: | ---: | --- |
| 01, focused depth 3 / fuel 2000 | 20 s | 20.01 | exit 124; no returned Boolean/certificate |
| 04, focused depth 3 / fuel 2000 | 20 s | 20.01 | exit 124; no returned Boolean/certificate |
| 07, focused depth 2 / fuel 100 | 60 s | 65.87 | exit 124; no returned Boolean/certificate |
| 07, initial generation with fuel 100, depths 1–4 | 90 s | 98.81 | exit 124 during lazy proof reduction |

**No particular full certificate was successfully computed/verified in this
session.** Raw successes are not promoted to full successes. The generic
`full_benchmark_result_sound` theorem in the owned file is conditional on an
actual `Some` result and is not evidence that these timeout probes returned one.

An isolation probe for 07 reduced **only the raw-search summary** with `lazy`
at the focused depth-2/fuel-100 profile. It also timed out (nominal 30 s,
observed 32.92 s, exit 124), while the same raw summary completed by VM in
8.65 s. Thus expensive interpreted raw-search reduction is a confirmed
blocker already before full packaging. The experiments do not prove that the
relational checker alone causes the full timeout, nor that a returned graph
violates the witness format. The focused raw graphs have routing acceptance.

An intermediate 16/8/16/32 generation profile, fuel 100, depths 1–4 reproduced
01 and 07 raw graphs (13.80 s and 8.23 s). Independent 02 and 05 probes timed
out (nominal 60 s, observed 65.84 s each); 04 timed out (nominal 45 s,
observed 47.94 s). The remaining intermediate rows were not executed.

### Historical reproduction and integration follow-up

Temporary probes were compiled with:

```sh
rocq compile \
  -Q /home/zyr/myCode/cyclist/Rocq-copy CyclistRocq \
  -Q /tmp/opencode/fo-bench-probes Probe Raw01.v
```

The other goals used their own `RawXX.v`, `QuickXX.v`, or focused probe files.
`/usr/bin/time` measured complete process wall time; `timeout` imposed the
reported process deadline. The owned regression file is compiled from
`Rocq-copy/FirstOrderNew` using:

```sh
rocq compile -Q .. CyclistRocq BenchmarkRuns.v
```

The historical owned-file command **succeeded**: wall **194.41 s**, peak RSS
**476656 KB**. All twelve recomputed raw-result regressions passed (three
focused Found results and nine quick Unknown results), as did the suite and
no-packaged-proof lemmas. The compiler emitted only large-`nat` literal
representation warnings for the external millisecond timing data.
`Print Assumptions` on the two no-packaging results reports the existing
standard-library `Classical_Prop.classic` and
`ClassicalEpsilon.constructive_indefinite_description` dependencies. The new
file introduces no project axioms or `Admitted` obligations.

Necessary follow-ups belong to the engine/integration owner:

1. Provide an efficient, reusable raw-search reduction/caching boundary for
   full `prove` while retaining its actual native rule proofs, root equality,
   witness and frozen `raw_check`. No unchecked promotion of the summaries.
2. Retain per-depth search diagnostics/effort and distinguish candidate limits,
   search fuel, witness pruning, and final checker rejection. Current `Unknown`
   erases graphs and iterative deepening collapses earlier reasons.
3. Re-run all nine targets with recorded budgets and obtain full certificates
   for successes. Six initial results remain unmeasured beyond timeout; the
   small-profile Unknown results do not relax the all-nine acceptance target.
4. If witness-format rejection arises in later runs, record the concrete graph
   and rejected routing constraint before diagnosing a conservative trace
   barrier. This session establishes a compute barrier, not such a rejection.

No engine, witness, unfolding, manifest, or frozen framework source was changed
by this benchmark work.
