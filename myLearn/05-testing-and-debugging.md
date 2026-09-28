# 05 — Testing and debugging

Proof-search failures often have the same final symptom—“not proved”—despite
very different causes. This chapter gives a layered workflow for distinguishing
parser errors, inapplicable rules, bad strategy commitments, depth exhaustion,
and rejected cyclic links.

## 1. Build environment

The source declares its OCaml dependencies in
[`dune-project`](../dune-project) and its system dependencies in generated
[`cyclist.opam`](../cyclist.opam).

Core requirements include:

- OCaml 4.08 or newer (CI currently exercises OCaml 5.3);
- Dune;
- `stdlib-shims`, `dune-configurator`, `mparser-re`, `cmdliner`,
  `dune-build-info`, `hashcons`, `hashset`, and `ocamlgraph`;
- Spot development library discoverable as `libspot >= 2.15` through
  `pkg-config`;
- Z3 for the array-separation-logic path.

The canonical system-package pattern is documented in
[`Dockerfile`](../Dockerfile) and CI setup in
[`build.yml`](../.github/workflows/build.yml).

After installing Spot/system dependencies, the normal local flow is:

```bash
opam install . --deps-only --with-test
opam exec -- dune build
opam exec -- dune runtest
```

Useful complete checks:

```bash
opam exec -- dune build @all @runtest
opam exec -- make fmt-check
opam exec -- make doc
```

Do not edit generated `cyclist.opam` directly; its first line says to edit
`dune-project` instead.

### 1.1 State of the environment during this source audit

The active workspace environment did not have the project dependencies fully
installed. `dune build @all @runtest` failed before compilation because these
were unavailable:

```text
cmdliner
dune-build-info
mparser-re
hashcons
libspot >= 2.15 (pkg-config package)
```

This is an environment/setup failure, not a source failure. The tutorial was
therefore checked against source contracts and references, but the repository
could not be compiled in that environment. Establish a green baseline after
provisioning dependencies and before implementing your logic.

## 2. Baseline command set

After a successful build:

```bash
# Entire command tree
opam exec -- dune exec cyclist -- --help=plain

# A leaf's exact options
opam exec -- dune exec cyclist -- ltl prove --help=plain

# Small positive proof with human-readable proof output
opam exec -- dune exec cyclist -- \
  ltl prove --sequent '(p ∨ ¬p)' --show-proof

# Same proof as DOT
opam exec -- dune exec cyclist -- \
  ltl prove --sequent '(p ∨ ¬p)' --show-proof --dot

# Debug and statistics
opam exec -- dune exec cyclist -- \
  ltl prove --sequent '(◇ p ∨ □ ¬p)' --debug --stats --show-proof
```

If the public executable alias is unavailable in a partial build, use the
explicit executable path:

```bash
opam exec -- dune exec src/cli/cyclist.exe -- --help=plain
```

Record for your logic:

- one positive acyclic input;
- one negative input;
- one positive cyclic input;
- expected exit codes;
- proof node count, backlinks, and required search depth for stable small
  cases.

## 3. Failure-classification tree

```text
Command does not start
  |
  +-- build/link error ----------> Dune dependency/module wiring
  +-- CLI parse error -----------> Cmdliner term, option collision, input path
  `-- formula parse error -------> grammar/token/attempt/full-consumption

Command runs but reports no proof
  |
  +-- rule never appears in debug
  |     +-- not in assembled strategy
  |     +-- setup not called
  |     `-- earlier Rule.first family commits
  |
  +-- rule appears, no application
  |     +-- applicability/destructor mismatch
  |     +-- normalized shape differs
  |     `-- side condition or unification fails
  |
  +-- application appears, branch fails
  |     +-- wrong premise(s)
  |     +-- premise order exposes expensive failure
  |     +-- insufficient depth
  |     `-- required alternative hidden by first/eager policy
  |
  `-- backlink candidate disappears
        +-- selection did not include target
        +-- equal_upto_tags/matching failed
        +-- explicit substitution/weakening failed
        +-- tag relation malformed
        `-- global infinite-descent check rejected it
```

Use this tree before changing the rule. Increasing the depth cannot fix a rule
that is absent from the strategy or a backlink rejected for soundness.

## 4. Test rule functions below the search layer

Search combines too many variables for first-line testing. A `Rule.t` can be
applied directly to an open root:

```ocaml
module Proof = Generic.Proof.Make (Mylogic.Seq)

let goal = Mylogic.Seq.of_string "..."
let initial = Proof.mk goal
let applications = Mylogic.Rules.some_rule 0 initial
```

Each result is `(new_open_indices, new_proof)`. Inspect:

```ocaml
Proof.get_seq premise_index new_proof
Proof.find 0 new_proof
Proof.size new_proof
Proof.is_closed new_proof
```

For even clearer tests, keep the pure function passed to `Rule.mk_infrule`
named and expose it in `rules.mli` while developing:

```ocaml
val disj_applications : Seq.t -> Rule.infrule_app list
val disj : Rule.t
```

Then assert the exact nested application/premise shape and exact tag pairs
without decoding a proof graph. The existing Seplog and Firstorder interfaces
expose several pure rule functions in this style.

## 5. Observe search order

`--debug` sets `Lib.do_debug`, enabling messages emitted through:

```ocaml
debug (fun () -> expensive_message ())
```

The thunk avoids building the message when debugging is disabled. Follow this
style for new diagnostics.

The generic prover prints the node it is trying to close and the current proof.
`Rule.mk_infrule` logs discovered rule descriptions. Use unique, stable rule
descriptions; they are debugging data and appear in printed proofs.

When diagnosing strategy order, create a table from the log:

| Step | Node | Goal summary | First applicable family | Applications | Outcome |
|---:|---:|---|---|---:|---|
| 1 | 0 | ... | Simplify | 1 | premise 1 |
| 2 | 1 | ... | Backlink | 0 | continues |

If a later rule should have run, inspect the earlier `Rule.first` member. A
nonempty application list commits even if every resulting branch later fails.

## 6. Inspect proof and trace graphs

Human proof output shows sequents, descriptions, successor indices, and tag
relations. DOT output is better for cycles:

```bash
... --show-proof --dot > proof.dot
dot -Tsvg proof.dot -o proof.svg
```

`--dot` only changes the proof printer; pair it with `--show-proof`.

For soundness-level graphs, common options from `Soundcheck.term` include:

```text
--inf-desc METHOD
--unminimized-proofs
--dump-graphs
--graph-dir DIR
--repr node|edge|json
--rel-stats
```

Use an explicit, narrow `--graph-dir`; dumped graphs are diagnostic artifacts
and can be numerous during search.

### 6.1 What to inspect on every cyclic edge

| Check | Source code invariant |
|---|---|
| Target node exists | `Soundcheck.valid` |
| Progress relation is a subset of valid | `Soundcheck.valid` |
| Every pair's left tag occurs in source node | `Soundcheck.valid` |
| Every pair's right tag occurs in target node | `Soundcheck.valid` |
| Bud/companion goals agree modulo tags | `Proof.add_backlink` assertion |
| Every infinite proof path has required infinite progress | selected global checker |

If a direct checker test violates a structural condition, `check_proof` prints
the graph and asserts. If a structurally valid graph lacks global descent, it
returns false.

## 7. Separate depth, timeout, and divergence

Three failures look similar:

```text
depth exhaustion
  current IDFS bound is too small; next bound may work

timeout
  alarm interrupts the entire search; Frontend reports TIMEOUT

internal divergence
  a tactic such as repeat applies forever before returning control
```

Diagnosis:

1. Run with fixed `--depth N` and a generous timeout.
2. Increase `N` by one and compare whether debug reaches new goals.
3. If no output/progress occurs inside one rule invocation, audit `repeat` and
   rules that return unchanged sequents.
4. If applications multiply rapidly, count alternatives from `choice`,
   unification, unfolding, and backlink targets.

`--max-depth 0` disables the bound in `Frontend`; it does not disable timeout.
Use an explicit finite bound during development so faulty recursive strategies
fail predictably.

## 8. Test equality, ordering, and hashing together

Many logical values live in ordered and hashed containers. For representative
values `x`, `y`, and `z`, test:

```text
compare x y = 0  iff  equal x y
equal x y        implies hash x = hash y
compare is antisymmetric
compare is transitive
normalization preserves intended equality
substitution preserves container invariants
```

When equality deliberately ignores metadata—as LTL's internal tagged-formula
set ignores tags—write separate tests for container equality and public sequent
equality. Otherwise a later maintainer can “simplify” the code and erase a
necessary distinction.

## 9. Parser tests

For every constructor or command:

```text
minimal valid input
nested valid input
whitespace variants
Unicode/ASCII variants if supported
missing delimiter
unexpected trailing text
overlapping-prefix alternative
printer output parsed back
```

MParser's `attempt` should be targeted. Too little prevents alternatives after
input consumption; wrapping everything can hide where a grammar committed and
degrade error messages.

Definition/program file parsers should close channels in new code. Several
existing commands use direct `open_in`; a new implementation can improve local
resource handling with `Fun.protect` without requiring a repository-wide
refactor.

## 10. CLI tests and exit codes

[`tests/cli/dune`](../tests/cli/dune) walks `--help=plain` over every command
leaf because Cmdliner only constructs a leaf parser when selected. Add both the
group and leaf help checks for a new logic.

For behavior tests, capture exit code as well as output:

| Outcome | Common generic-prover exit |
|---|---:|
| proved | 0 |
| not found | 1 |
| timeout | 2 |
| CLI error | Cmdliner `cli_error` |

Specialized commands differ. For example, SL proof/disproof uses exit `255` for
an invalid entailment in some paths, while SLCOMP modes may normalize process
exit behavior and communicate via `sat/unsat/unknown` text. Read each command's
`Cmd.info ~exits` rather than imposing the generic convention.

## 11. Regression tests for strategy changes

A strategy change can preserve theorem-proving power in principle while making
the implementation unusably slow. For a small stable corpus, record:

```text
result
proof node count
backlink count
last_search_depth
elapsed time or a coarse upper bound
number of solver calls, if relevant
```

Use exact node/depth assertions only on small tests where proof shape is
intentionally stable. For larger benchmarks, use generous thresholds to avoid
machine-dependent flakes.

When changing rule order, include:

1. a goal solved by the newly prioritized rule;
2. a goal where that rule applies but its first branch fails;
3. a goal needing a later alternative;
4. a negative goal, to detect search explosion;
5. a cyclic goal, to detect changed companion selection/proof shape.

## 12. Global refs and test isolation

The repository uses mutable configuration refs for:

- rule strategies and definition setup;
- backlink selection;
- lemma levels and heuristics;
- debug/statistics;
- search bounds/output;
- soundness backend options;
- program state and proof caches.

Tests in one process must restore values or set every relevant option in their
fixture. A robust local helper is:

```ocaml
let with_ref r value f =
  let old = !r in
  Fun.protect ~finally:(fun () -> r := old) (fun () -> r := value; f ())
```

For larger integration tests, separate executables/processes give stronger
isolation.

## 13. Before/after implementation commands

Run narrow checks frequently:

```bash
# Format check
opam exec -- dune build @fmt

# Your new library and tests
opam exec -- dune build @src/mylogic/all
opam exec -- dune runtest src/mylogic/test

# CLI help smoke test
opam exec -- dune runtest tests/cli

# Everything
opam exec -- dune build @all @runtest

# API docs; useful for catching broken interfaces/doc links
opam exec -- dune build @doc
```

Then run at least one representative command for every existing library whose
shared code you changed. A `Generic.Proofrule` edit, for example, warrants LTL,
FO, SL, and program-prover smoke tests rather than only your new logic.

## 14. Review checklist

### Representation

- [ ] Type invariants are written near the type.
- [ ] All constructors preserve them.
- [ ] Compare/equal/hash agree.
- [ ] Exact and modulo-tag equality are distinct where needed.
- [ ] Freshening avoids every variable/tag in scope.

### Rules

- [ ] Empty list means inapplicable, not successful no-op.
- [ ] Alternatives and premises have the intended nesting.
- [ ] Side conditions are directly tested.
- [ ] Every edge relation has correct source/target orientation.
- [ ] Progress is a subset of valid and has a mathematical justification.

### Strategy

- [ ] Every `first` priority is intentional.
- [ ] Every `choice` branch is necessary.
- [ ] Every `repeat` body makes progress or eventually becomes inapplicable.
- [ ] Greedy backlinks are safe to commit to.
- [ ] Setup runs before search and test state is isolated.

### Integration

- [ ] Dune library dependencies are declared.
- [ ] CLI executable links the library.
- [ ] Command group/leaf are registered.
- [ ] Help smoke tests cover both.
- [ ] Exit behavior is documented and tested.

### Evidence

- [ ] Positive and negative acyclic tests.
- [ ] Positive and rejected cyclic tests.
- [ ] Parser/printer tests.
- [ ] Rule-level premise/trace tests.
- [ ] Representative performance baseline.
- [ ] Full build, tests, format, and docs pass.

## 15. Glossary tied to code

| Term | Meaning in this repository |
|---|---|
| sequent | Logic-specific proof goal implementing `Generic.Sequent.S` |
| application | One alternative way a rule can replace a conclusion by premises |
| premise/subgoal | An open proof node that must be closed |
| bud | Source leaf of a backlink |
| companion | Existing target node of a backlink |
| tag | Integer-backed identity for a traceable occurrence |
| valid pair | Permitted continuation of a trace across one edge |
| progressing pair | Valid transition representing a strict decrease |
| infinite descent | Global condition making cyclic reasoning sound |
| symbolic heap | Pure equalities/disequalities plus points-to and predicates |
| frame | Heap portion left over after matching a specification |
| IDFS | Iterative-deepening depth-first search used by ordinary provers |
| BFS abducer | Search carrying synthesized definitions in `Generic.Abducer` |
| setup | Concrete-logic step that compiles runtime definitions/config into strategy refs |

When debugging, name the layer and glossary object that failed—for example,
“the rule has no applications,” “the second premise is unprovable,” or “the
backlink's global trace condition fails.” That precision will save far more
time than treating every outcome as a generic prover failure.
