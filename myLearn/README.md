# Learning Cyclist for implementation work

This is an implementation-oriented guide to the Cyclist repository. It is not
an API brochure: the goal is to make you able to add a logic, add or reorder
rules, reason about cyclic soundness, expose a command, and test the result
without treating the framework as a black box.

The guide was prepared from the source at commit `d70ef23` on 2026-09-28.

## Documents in this guide

| Document | What you should learn |
|---|---|
| [01 — Architecture and execution](01-architecture-and-execution.md) | How a CLI input becomes a proof; the sequent, rule, proof, search, and soundness contracts |
| [02 — LTL vertical slice](02-ltl-vertical-slice.md) | A complete, small cyclic prover, read line by line in dependency order |
| [03 — Implementing a new logic](03-implementing-a-new-logic.md) | A concrete file plan, code templates, tag design, Dune/CLI wiring, and tests |
| [04 — Existing logic map](04-existing-logic-map.md) | What the first-order, separation-logic, while, procedure, ASL, and auxiliary tools contain |
| [05 — Testing and debugging](05-testing-and-debugging.md) | Environment setup, observability, failure diagnosis, test layers, and a completion checklist |

Read them in that order unless you are modifying an existing separation-logic
or program-verification feature. The alternative routes below tell you when to
branch.

## The repository in one figure

```text
                                     +-----------------------+
input text / files ----------------> | logic-specific parser |
                                     +-----------+-----------+
                                                 |
                                                 v
                                     +-----------------------+
                                     | concrete sequent      |
                                     | implements Sequent.S  |
                                     +-----------+-----------+
                                                 |
                  +------------------------------+----------------------+
                  |                                                     |
                  v                                                     v
        +---------------------+                               +------------------+
        | logic rules         | alternatives + premises      | Generic.Prover   |
        | Rule.mk_*           +------------------------------>| iterative DFS    |
        +---------------------+                               +--------+---------+
                                                                    |
                                                                    v
                                                           +------------------+
                                                           | Generic.Proof    |
                                                           | indexed graph    |
                                                           +--------+---------+
                                                                    |
                                                        backlink candidate
                                                                    |
                                                                    v
                                                           +------------------+
                                                           | Soundcheck       |
                                                           | infinite descent |
                                                           +--------+---------+
                                                                    |
                                                                    v
                                                           proof / no proof
                                                                    |
                                                                    v
                                                           Cmdliner frontend
```

The key design fact is that the generic engine knows almost nothing about a
logic. A logic supplies:

1. a concrete sequent type satisfying `Generic.Sequent.S`;
2. axioms and inference/backlink rules over that sequent;
3. valid and progressing tag transitions for every premise;
4. parsing, printing, a search strategy, and a command wrapper.

Everything else—proof graph mutation, bounded search, tactic combinators,
backtracking, and global cyclic soundness checking—is reusable.

## Recommended reading roadmap

Use the following checkpoints rather than simply reading every file in lexical
order. For every `.ml` file, read its `.mli` first when one exists. The
interface tells you which details are stable dependencies and which are local
implementation choices.

### Phase 0: establish a baseline

Read:

1. [`README.md`](../README.md)
2. [`dune-project`](../dune-project)
3. the root [`dune`](../dune) file
4. [`src/cli/dune`](../src/cli/dune)
5. [`src/cli/cyclist.ml`](../src/cli/cyclist.ml)

Then build and run the existing tests as described in
[05 — Testing and debugging](05-testing-and-debugging.md). Record a known-good
command before changing code.

Checkpoint: you can explain why `cyclist ltl prove` is a group/subcommand pair,
where `Ltl.Prove.cmd` comes from, and why adding a library to `src/cli/dune` is
separate from adding its command to `cyclist.ml`.

### Phase 1: learn one complete vertical slice

Read the LTL prover in this exact order:

1. [`src/ltl/form.mli`](../src/ltl/form.mli), then `form.ml`
2. [`src/ltl/seq.mli`](../src/ltl/seq.mli), then `seq.ml`
3. [`src/ltl/rules.mli`](../src/ltl/rules.mli), then `rules.ml`
4. [`src/ltl/prove.ml`](../src/ltl/prove.ml)
5. [`src/ltl/test/test.ml`](../src/ltl/test/test.ml)

Use [02 — LTL vertical slice](02-ltl-vertical-slice.md) beside the source.

Checkpoint: without running it, trace `(p ∨ ¬p)` from parser output to a
two-node proof. Explain why the disjunction rule has one premise, why the
conjunction rule has two, and why the outer rule-application list is different
from the inner premise list.

### Phase 2: open the generic engine underneath LTL

Read:

1. [`src/generic/sequent.mli`](../src/generic/sequent.mli)
2. [`src/generic/proofnode.mli`](../src/generic/proofnode.mli) and `proofnode.ml`
3. [`src/generic/proof.mli`](../src/generic/proof.mli) and `proof.ml`
4. [`src/generic/proofrule.mli`](../src/generic/proofrule.mli) and `proofrule.ml`
5. [`src/generic/seqtactics.mli`](../src/generic/seqtactics.mli) and `seqtactics.ml`
6. [`src/generic/prover.mli`](../src/generic/prover.mli) and `prover.ml`
7. [`src/generic/frontend.mli`](../src/generic/frontend.mli) and `frontend.ml`

Checkpoint: you can write the type of an inference-rule application from
memory and explain `Rule.first`, `Rule.choice`, `Rule.compose`, `Rule.repeat`,
and `Rule.attempt` operationally, including their effect on backtracking.

### Phase 3: understand cyclic soundness before adding a backlink

Read:

1. [`src/generic/tags.mli`](../src/generic/tags.mli)
2. [`src/generic/tagpairs.mli`](../src/generic/tagpairs.mli)
3. the `Seq` tagging invariant in [`src/ltl/seq.ml`](../src/ltl/seq.ml)
4. the `always`, `next`, and `backlink` rules in
   [`src/ltl/rules.ml`](../src/ltl/rules.ml)
5. [`src/generic/soundcheck.mli`](../src/generic/soundcheck.mli)
6. in `soundcheck.ml`, initially only `abstract_node`, `mk_abs_node`, `valid`,
   minimisation, and `check_proof`

Do not begin with the C/C++ graph algorithms. They implement several ways to
check the same abstract trace condition; they are not needed to instantiate a
new logic.

Checkpoint: for every edge in one of your rules, you can state which conclusion
tag maps to which premise tag, why every progressing pair must also be valid,
and what measure strictly decreases.

### Phase 4: choose the branch closest to your job

| Your intended change | Read next |
|---|---|
| Add a small new logic | [03 — Implementing a new logic](03-implementing-a-new-logic.md), then use LTL as the template |
| Add rules to first-order inductive reasoning | `firstorder/term` → `atom` → `prod` → `form` → `seq` → `case`/`defs` → `rules` |
| Add separation-logic entailment behavior | `seplog/term` → atomic spatial/pure modules → `heap` → `form` → `seq` → definitions → `unify` → `rules` |
| Add a while command or symbolic-execution rule | Learn the relevant SL layer, then `while/program` → `while/rules` → `while/prove` |
| Add procedure reasoning | Learn While first, then `procedure/program` → `procedure/rules` → `procedure/prove` |
| Add array-memory reasoning | `asl/asl_term` → constraints/arrays → `asl_heap` → `asl_form`/`asl_sat` → `asl_while` |
| Change proof search itself | Finish Phases 1–3, then modify `generic/prover.ml` with search-order regression tests |
| Change the global trace checker | Finish Phases 1–3, read `tests/soundness`, then study `soundcheck.ml` and the C/C++ files |
| Add abduction | Read `generic/abdrule` and `generic/abducer`, then `while/abdrules` and `while/abduce` |

The module-by-module map is in
[04 — Existing logic map](04-existing-logic-map.md).

### Phase 5: implement in vertical slices

Use this order, compiling after each numbered step:

1. formula/term representation, equality, ordering, printing, and parser;
2. sequent representation satisfying `Sequent.S`;
3. one axiom and one acyclic inference rule;
4. a search strategy and direct OCaml unit test;
5. a `Cmdliner` command and CLI smoke test;
6. all remaining acyclic rules;
7. tags and transition relations;
8. backlink generation;
9. positive, negative, cyclic, malformed-input, and search-bound tests;
10. profiling and rule-order tuning.

This sequence deliberately postpones backlinks. Empty tag sets are valid for an
acyclic first milestone; an incorrectly tagged cyclic rule can produce proofs
whose mathematical meaning is wrong even if the OCaml types compile.

## A practical six-session schedule

| Session | Source work | Deliverable |
|---|---|---|
| 1 | Phases 0–1 | A handwritten trace of the LTL tautology and a successful baseline run |
| 2 | `Proof`, `Proofnode`, `Proofrule` | A table showing how each rule changes an open proof node |
| 3 | `Prover`, tactics, `Frontend` | A prediction of search order for one multi-choice example, checked with `--debug` |
| 4 | tags, LTL cyclic rules, `Soundcheck` | A trace-transition diagram for one intended cycle in your logic |
| 5 | the domain branch closest to your logic | Your syntax/sequent design and rule inventory |
| 6 | [03 — Implementing a new logic](03-implementing-a-new-logic.md) | A first acyclic end-to-end prover command with tests |

## What not to read first

These files matter, but they are poor entry points:

- `src/generic/heighted_graph.c` and the other criterion/graph C files: soundness
  checker backends, not the logic-extension API.
- `src/seplog/rules.ml`: rich and useful after you know the generic contract,
  but too large to teach that contract cleanly.
- `src/procedure/rules.ml`: it combines nested entailment proving, frames,
  procedure proof caches, and program rules.
- benchmark result machinery: use benchmark inputs as examples, but understand
  the prover before studying performance scripts.
- `src/lib` implementation files in bulk: consult their `.mli` files on demand.
  `Lib.Blist` is an ordinary list API with extra combinators, not a lazy search
  stream.

## The shortest correct mental model

```text
A rule is a function from an open goal to zero or more applications.

zero applications       = rule is not applicable
multiple applications   = alternatives; search may backtrack among them
multiple premises       = obligations; every premise must be proved
axiom/backlink result   = no new open nodes; the current goal is closed

A proof is an indexed graph whose inference edges carry trace relations.
A backlink closes a leaf by pointing to an existing node.
A backlink is accepted only if the resulting abstract proof satisfies the
global infinite-descent condition.
```

Keep that model in view while reading the larger domain implementations.
