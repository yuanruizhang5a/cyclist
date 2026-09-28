# 01 — Architecture and execution

This chapter explains the reusable framework beneath every ordinary Cyclist
prover. The important modules live in `src/generic`; the LTL names used in
examples are concrete instances of those modules.

## 1. Layer and dependency map

```text
+--------------------------------------------------------------------------+
| src/cli                                                                  |
| Cmdliner command tree; knows every top-level logic library               |
+--------------------------------------+-----------------------------------+
                                       |
                 +---------------------+--------------------+
                 | logic libraries                          |
                 | ltl | fol | seplog | while | asl_while   |
                 | procedure                                |
                 +------+-----------------------------------+
                        | instantiate functors and provide rules
                        v
+--------------------------------------------------------------------------+
| src/generic                                                              |
| Sequent contract | proof graph | rule/tactic algebra | search | frontend |
| tags/relations | global cyclic soundness | generic abduction             |
+--------------------------------------+-----------------------------------+
                                       |
                                       v
+--------------------------------------------------------------------------+
| src/lib                                                                  |
| containers | variable managers | CPS unification | parsers | utilities   |
+--------------------------------------------------------------------------+

The C/C++ files under src/generic are backends for cyclic soundness checking.
They do not define the inference rules of any concrete logic.
```

Dune libraries are wrapped. For example, `src/ltl/dune` declares library
`ltl`, so code outside that library refers to `Ltl.Prove`, `Ltl.Seq`, and so
on. Inside the same library the modules are simply `Prove`, `Seq`, etc.

## 2. The end-to-end call path

For `cyclist ltl prove --sequent '...'`, the exact control flow is:

```text
src/cli/cyclist.ml
  builds Cmd.group "ltl" [Ltl.Prove.cmd]
      |
      v
src/ltl/prove.ml : cmd
  Cmdliner parses --sequent and common options
      |
      v
run
  Seq.of_string input
  F.prove_seq !Rules.axioms !Rules.rules seq
      |
      v
Generic.Frontend.Make(Prover).prove_seq
  timeout/stats wrapper
  F.idfs axiom_strategy rule_strategy seq
      |
      v
Generic.Prover.Make(Seq).idfs
  Proof.mk seq                 root 0 is open
  try axioms on current node
  otherwise enumerate rule applications
  recursively close all premises
      |
      +---- inference application ----> Proof.add_inf
      +---- axiom ---------------------> Proof.add_axiom
      +---- backlink ------------------> Proof.add_backlink
                                           |
                                           v
                                      Proof.check
                                           |
                                           v
                                      Soundcheck.check_proof
      |
      v
Frontend.process_result
  print proof / summary / status and select exit code
```

The command layer is intentionally thin. Mathematical behavior belongs in the
formula, sequent, and rules modules; generic search behavior belongs in
`src/generic`.

## 3. The one interface a logic must implement

[`src/generic/sequent.mli`](../src/generic/sequent.mli) defines:

```ocaml
module type S = sig
  type t
  val equal : t -> t -> bool
  val equal_upto_tags : t -> t -> bool
  val tags : t -> Tags.t
  val to_string : t -> string
  val pp : Format.formatter -> t -> unit
end
```

The functions are not interchangeable:

| Member | Consumer | Required meaning |
|---|---|---|
| `equal` | `Proof.ensure_add`, exact proof-node replacement; some selectors | Syntactic equality, including tags |
| `equal_upto_tags` | `Proof.add_backlink` assertion | Same logical goal after erasing trace-label identities |
| `tags` | `Proofnode.to_abstract_node` and `Soundcheck` | All trace labels present at this node |
| `pp` | proof and DOT printers | Structured `Format` output |
| `to_string` | status/debug messages | Usually implemented from `pp` |

An acyclic logic may return `Tags.empty` and define `equal_upto_tags = equal`.
A cyclic logic must decide which syntactic objects carry traces and preserve a
clear invariant about tag uniqueness and freshness.

The functors then specialize the engine:

```ocaml
module Proof  = Generic.Proof.Make (Seq)
module Rule   = Generic.Proofrule.Make (Seq)
module Prover = Generic.Prover.Make (Seq)
module F      = Generic.Frontend.Make (Prover)
```

Because OCaml applicative functors give compatible types for repeated
applications to the same module path, the `Proof.Make(Seq).t` used in `Rule`
and in `Prover` agrees.

## 4. Proof graph representation

Read [`proofnode.mli`](../src/generic/proofnode.mli) before
[`proof.ml`](../src/generic/proof.ml).

There are four node states:

| Node | Meaning | Successors |
|---|---|---:|
| `OpenNode` | An unproved goal | none |
| `AxiomNode` | Closed locally | none |
| `InfNode` | Result of an inference rule | one or more premises |
| `BackNode` | Bud closed by a link to an existing companion | one graph edge to target |

Internally a proof is approximately:

```ocaml
type t = (int * Node.t) Int.Map.t
(*          ^ parent node id       *)
```

The root is index `0` and records itself as its parent. The parent field lets
`Proof.get_ancestry` implement ancestral backlink selection.

### 4.1 How an inference changes a proof

Suppose node `4` is open and a rule returns two premises:

```text
Before                             After Proof.add_inf

0                                  0
`-- 4: Open(S)                     `-- 4: Inf(S, "R")
                                         |-- 7: Open(S1)
                                         `-- 8: Open(S2)
```

`Proof.add_inf`:

1. allocates consecutive fresh indices;
2. replaces the open node at `4` with an inference node;
3. stores `(valid, progressing)` relations for each edge;
4. inserts each premise as an open node with parent `4`;
5. returns `([7; 8], new_proof)`.

`Proof.add_axiom` replaces an open node without adding successors.
`Proof.add_backlink` replaces it with a link and asserts that source and target
are `equal_upto_tags`.

`Proof.add_inf` can mechanically be called with an empty premise list, but that
would create a leaf inference node and conflict with the documented proof
invariant. Represent a genuine zero-premise rule with `Rule.mk_axiom`.

The important invariants are documented in
[`proof.mli`](../src/generic/proof.mli): nonempty, rooted at `0`, connected,
indices valid, and only open/axiom/backlink nodes at leaves.

## 5. The exact meaning of a rule value

[`proofrule.mli`](../src/generic/proofrule.mli) defines:

```ocaml
type infrule_app =
  (seq_t * Tagpairs.t * Tagpairs.t) list * string

type infrule_f = seq_t -> infrule_app list

type t =
  int -> proof_t -> (int list * proof_t) Blist.t
```

Read the nested lists carefully:

```text
infrule_f conclusion
  = [ application 1; application 2; ... ]       alternatives (OR)

application
  = ([ premise 1; premise 2; ... ], description) obligations (AND)

premise
  = (sequent, valid_tag_pairs, progressing_tag_pairs)
```

Example:

```ocaml
[
  ([ (a, va, pa); (b, vb, pb) ], "R-left-choice");
  ([ (c, vc, pc) ], "R-right-choice");
]
```

means: the rule can prove the conclusion either by proving both `a` and `b`,
or by proving `c`. It does **not** mean that only one of `a` and `b` is needed.

`Blist.t` is a normal list. Generating many applications materializes many
alternatives and can make search expensive.

### 5.1 Constructors

| Constructor | Domain-level function | Result |
|---|---|---|
| `Rule.mk_axiom` | `seq -> string option` | Closes the node if it returns `Some description` |
| `Rule.mk_infrule` | `seq -> infrule_app list` | Replaces the node with each possible inference application |
| `Rule.mk_backrule` | selection plus `bud -> companion -> matches` | Tries links to selected proof nodes and retains sound candidates |

`mk_backrule eager ...` has an important switch:

- `eager = false`: retain every candidate that passes `Proof.check`, so search
  can backtrack among them;
- `eager = true`: commit to the first sound candidate.

## 6. Proof-rule combinators and search commitments

These combinators are the strategy language.

| Combinator | Operational behavior | Common trap |
|---|---|---|
| `fail` | no applications | Useful initial value for a strategy ref |
| `identity` | returns the same proof and current open node | It is a successful no-op |
| `attempt r` | use `r`; if inapplicable, use `identity` | Can hide an expected failure |
| `choice [r1; r2]` | concatenate all applications from both | Branch count can explode |
| `first [r1; r2]` | use applications of the first applicable rule family | Later families are never considered once one returns nonempty |
| `compose r r'` | apply `r`, then apply `r'` to every premise | Every premise must admit `r'`, unless it is wrapped in `attempt` |
| `compose_pairwise r rs` | apply corresponding follow-up rule to each premise | Extra rules are dropped; missing ones become `identity` |
| `sequence [r1; r2; ...]` | repeated `compose` | Not merely “try in order” |
| `repeat r` | recursively apply `r` to every generated premise until failure | Diverges when `r` can succeed without structural progress |
| `conditional p r` | apply `r` only when current sequent satisfies `p` | Predicate sees the sequent, not the whole proof |

The distinction between `first` and `choice` is central to both completeness
and performance:

```ocaml
Rule.first [ simplify; backlink; unfold ]
```

commits to simplification whenever it has at least one application. It still
backtracks among simplification's applications, but it will not try backlink or
unfold at that node.

```ocaml
Rule.choice [ backlink; unfold ]
```

exposes both families to the depth-first search.

### 6.1 `Seqtactics` versus `Proofrule`

`Generic.Seqtactics.Make(Seq)` combines pure sequent-level functions before
they are lifted with `Rule.mk_infrule`. It cannot inspect ancestry or other
proof nodes.

When two sequent rules are composed, it also composes their trace relations.
If the first edge has `(V, P)` and the second `(V', P')`, the composed edge is:

```text
valid       = V  ∘ V'
progressing = (P ∘ P') ∪ (V ∘ P') ∪ (P ∘ V')
```

That formula preserves the fact that a composed path is progressing if either
component contains a strict step. Use `Seqtactics` for simplification pipelines
like those in the first-order and separation-logic provers; use `Proofrule`
when a rule needs the proof graph, such as guided weakening or backlinking.

## 7. Iterative-deepening depth-first search

The active search implementation is
[`Generic.Prover.Make.idfs`](../src/generic/prover.ml).

For each bound from `minbound` through `maxbound`, it:

1. creates `Proof.mk seq`, containing open root `0`;
2. on an open node, tries the axiom strategy first;
3. if no axiom closes it, enumerates the main rule strategy's applications in
   list order;
4. for each application, recursively closes premises from left to right;
5. backtracks to later applications when a premise fails;
6. retries from a fresh root at the next bound when no proof is found.

Approximate pseudocode:

```ocaml
for bound = minbound to maxbound do
  let rec dfs remaining node proof =
    if remaining < 0 then None
    else
      match first_closing_axiom node proof with
      | Some proof -> Some proof
      | None ->
          first_success (
            for each (premises, proof') in rules node proof:
              fold_left
                (fun current premise -> dfs (remaining - 1) premise current)
                (Some proof') premises)
  in
  return first successful (dfs bound 0 (Proof.mk goal))
done
```

Consequences for implementers:

- list order is search order;
- premise order can affect time to failure;
- `Rule.first` choices can remove theoretically useful search branches;
- the bound is a search bound, not necessarily the printed proof's graph
  depth;
- a rule producing the unchanged goal can cause nontermination inside
  `Rule.repeat` or waste every depth bound;
- `max-depth 0` is interpreted by `Frontend.idfs` as unbounded (`max_int`).

## 8. Frontend behavior

[`frontend.ml`](../src/generic/frontend.ml) centralizes:

- `--min-depth`, `--max-depth`, and `--depth`;
- `--timeout`;
- `--show-proof` and `--dot`;
- `--debug`, `--stats`, and run identifiers;
- the soundness checker options;
- result printing and exit codes.

`gather_stats` returns a nested option:

| Value | Meaning |
|---|---|
| `None` | timeout wrapper fired |
| `Some None` | search completed without a proof |
| `Some (Some proof)` | success |

`process_result` converts that into `TIMEOUT`, `NOT_FOUND`, or `SUCCESS`.
Some specialized commands, such as SL disproof/model checking and While
abduction, use their own control loops and only reuse parts of the frontend.

## 9. Tags, edge relations, and global soundness

A cyclic proof is not sound merely because a bud has the same formula as an
earlier companion. The cycle must witness infinite descent in a well-founded
measure.

Cyclist represents the required information as:

```text
node tags:       trace values visible at a sequent
valid pair a->b: a trace at the conclusion may continue as b at the premise
progress pair:   that same transition is a strict decrease
```

For an inference edge from `S` to `S'`, a pair `(a, b)` therefore has:

- `a` in `Seq.tags S`;
- `b` in `Seq.tags S'`;
- a progressing pair also present in the valid relation.

`Soundcheck.valid` checks exactly these structural properties before invoking
the selected infinite-descent algorithm.

### 9.1 Backlink acceptance path

```text
open bud
   |
   v
selection function chooses candidate companion nodes
   |
   v
logic-specific matcher checks equal goal modulo tags
and constructs bud-tag -> companion-tag relation
   |
   v
Proof.add_backlink (asserts equal_upto_tags)
   |
   v
Proof.check
   |
   +-- abstract each node to tags + edges + progress
   +-- remove finite leaf branches and fuse safe unary nodes
   +-- validate structural relation invariants
   +-- run global infinite-descent checker
   |
   v
candidate retained or rejected
```

The default backend is the order-reduced Floyd–Warshall–Kleene C++ checker.
Other backends are selectable from the CLI. The logic-facing contract is the
same for all of them.

### 9.2 Tag design questions you must answer

Before coding a cyclic rule, write down:

1. What semantic entity is a trace following—an inductive predicate
   occurrence, temporal obligation, loop measure, or something else?
2. Which syntactic occurrences receive tags?
3. Are tags unique within a sequent?
4. When a rule copies, deletes, unfolds, folds, or substitutes an occurrence,
   where does its trace go?
5. Which transitions preserve the measure?
6. Which transitions strictly decrease it, and why?
7. What relation maps a bud's tags to a companion's tags?

Do not infer progress from “the formula got smaller” unless that is the actual
well-founded argument of the calculus.

## 10. Selection functions for backlinks

`Proofrule` supplies:

| Selector | Candidate nodes |
|---|---|
| `all_nodes` | every other proof node |
| `closed_nodes` | every other non-open node |
| `ancestor_nodes` | only ancestors of the bud |
| `syntactically_equal_nodes` | nodes for which `Seq.equal` holds |

`default_select_f` is a global mutable reference, configurable by integer.
Note the source's TODO in `syntactically_equal_nodes`: it currently uses
`Seq.equal`, not `equal_upto_tags`. A new logic should not assume that selector
will find tag-renamed goals. LTL defaults to `all_nodes` and performs its own
`equal_upto_tags` test in the matcher.

## 11. Mutable setup state

Many concrete provers expose:

```ocaml
let axioms = ref Rule.fail
let rules = ref Rule.fail
let setup defs = ...
```

This lets parsed inductive definitions compile into rule closures. It also
means:

- `setup` must run before search;
- multiple tests in one OCaml process can leak configuration unless reset;
- command-line side effects mutate shared refs;
- parallel proof searches in one process are not automatically isolated.

For a new logic without dynamic definitions, immutable `let axioms = ...` and
`let rules = ...` values are simpler. Match the existing `ref` interface only
if runtime setup or toggles require it.

## 12. Core source checklist

After this chapter, verify that you can answer all of these from code:

- What is the difference between a rule being inapplicable and producing zero
  premises?
- Where are fresh proof node indices generated?
- Which equality is checked when adding a backlink?
- At what point does global soundness reject a backlink?
- What search commitment does `Rule.first` introduce?
- Why can `Rule.repeat` diverge?
- What do the left and right components of a tag pair refer to?
- Why can rule order and premise order change runtime without changing the
  calculus?
- Why must `setup` precede `F.prove_seq` in several provers?

If any answer is uncertain, revisit `proof.ml`, `proofrule.ml`, and `prover.ml`
before reading a larger logic.
