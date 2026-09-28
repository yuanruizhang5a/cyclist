# 03 — Implementing a new logic

This chapter turns the source model into an implementation plan. “New logic”
can mean either a new calculus in its own library or additional behavior in an
existing prover. The first sections cover a new library; the final sections
show how to reduce the scope when extending an existing one.

## 1. Write the mathematical contract before the OCaml contract

Create a one-page design with these fields:

| Question | Your answer must be precise enough to code |
|---|---|
| Judgment/sequent | Exact components and their meaning |
| Formula/term syntax | Every constructor and binding convention |
| Normal form | Whether parsing or construction normalizes terms/formulas |
| Axioms | Decidable predicates over sequents |
| Inference rules | Principal object, premises, side conditions, alternatives |
| Structural rules | Explicit, admissible, or encoded in the representation? |
| Inductive/cyclic objects | Which occurrences carry a trace? |
| Progress measure | The well-founded value that strictly decreases |
| Backlink admissibility | Equality, subsumption, substitution, weakening? |
| Search policy | Rule priority, nondeterministic choices, bounds |
| Input format | Grammar and example strings/files |
| Expected results | Positive, negative, and cyclic examples |

For each inference rule, fill one row of a rule inventory:

| Rule | Applicability | Alternatives | Premises per alternative | Valid pairs | Progress pairs |
|---|---|---:|---:|---|---|
| `Id` | complementary atoms present | 1 | 0 | n/a | n/a |
| `R` | principal constructor exists | ... | ... | ... | ... |

If the last two columns are hand-waving, the cyclic part is not ready to code.

## 2. Choose the closest architectural pattern

```text
Does the logic need program states/commands?
  |
  +-- no --> Does it need terms, variables, substitutions, or inductive defs?
  |            |
  |            +-- no  --> clone the LTL module shape
  |            +-- yes --> use Firstorder as the structural template
  |                         and Seplog for advanced unification/tagging
  |
  +-- yes --> Is the assertion theory already Seplog?
               |
               +-- yes --> extend While or Procedure
               +-- no  --> use Asl_while/While as architecture, but provide
                            your own state/assertion operations
```

Do not copy `seplog/rules.ml` merely because it is feature-rich. Begin with the
smallest architecture that represents your judgment.

## 3. Target directory and dependency graph

For a standalone logic named `mylogic`, start with:

```text
src/mylogic/
  dune
  form.mli
  form.ml
  seq.mli
  seq.ml
  rules.mli
  rules.ml
  prove.mli
  prove.ml
  test/
    dune
    test.ml
```

Dependency direction:

```text
Form <- Seq <- Rules <- Prove <- src/cli/cyclist.ml
          ^       ^
          |       |
     Sequent.S  Proofrule.Make(Seq)
                  |
               Prover.Make(Seq)
```

Avoid a dependency from `Form` back to `Rules` or `Prove`. Parsing and semantic
data structures should remain usable independently of search.

## 4. Milestone A: an acyclic prover with empty tags

Build an acyclic end-to-end version first. It validates all integration points
without requiring a cyclic soundness argument.

### 4.1 `Form`

A small one-sided propositional example might expose:

```ocaml
(* form.mli *)
include Lib.BasicType

val atom : string -> t
val negatom : string -> t
val conj : t -> t -> t
val disj : t -> t -> t

val dest_atom : t -> string option
val dest_negatom : t -> string option
val dest_conj : t -> (t * t) option
val dest_disj : t -> (t * t) option

val parse : (t, 'a) MParser.t
```

Implementation obligations:

- `compare` is total, deterministic, and agrees with `equal`;
- `hash` agrees with `equal`;
- `pp` is unambiguous enough for proof output;
- the parser consumes exactly the grammar you document;
- constructors maintain any normalization invariant;
- destructors return `None` for the wrong constructor rather than relying on
  exceptions in ordinary rule applicability checks.

Use [`src/ltl/form.ml`](../src/ltl/form.ml) for an algebraic syntax example and
[`src/firstorder/term.ml`](../src/firstorder/term.ml) when variables,
functions, and substitutions are required.

### 4.2 `Seq`

For the first milestone, an ordered formula set is sufficient if contraction
is built into your calculus:

```ocaml
(* conceptual seq.ml skeleton *)
open Lib
open Generic

module FormulaSet = Treeset.Make (Form)
type t = FormulaSet.t

let equal = FormulaSet.equal
let equal_upto_tags = equal
let tags _ = Tags.empty
let pp = FormulaSet.pp
let to_string s = mk_to_string pp s

let empty = FormulaSet.empty
let add = FormulaSet.add
let remove = FormulaSet.remove
let exists = FormulaSet.exists
let find_suchthat_opt = FormulaSet.find_suchthat_opt
```

The real interface should include the constructors and queries needed by your
rules, while still satisfying:

```ocaml
include Generic.Sequent.S
```

Questions to settle now:

- Is the sequent ordered, a set, or a multiset?
- Is exchange implicit?
- Is contraction implicit?
- Can duplicate occurrences carry different semantic identities?
- Does equality normalize alpha-renaming, equations, or substitutions?

Do not use a set merely for convenience if multiplicity is proof-theoretically
meaningful.

### 4.3 First axiom

```ocaml
open Generic
module Rule = Proofrule.Make (Seq)

let identity =
  let is_axiom seq =
    if Seq.has_complementary_atoms seq then Some "Id" else None
  in
  Rule.mk_axiom is_axiom
```

Keep the mathematical predicate as a separately testable `Seq` function if it
has nontrivial logic.

### 4.4 First one-premise inference

```ocaml
let disj =
  let apply seq =
    match Seq.find_suchthat_opt Form.is_disj seq with
    | None -> []
    | Some principal ->
        let left, right = Option.get (Form.dest_disj principal) in
        let context = Seq.remove principal seq in
        let premise = Seq.add right (Seq.add left context) in
        [
          ( [ (premise, Tagpairs.empty, Tagpairs.empty) ],
            "Disj" );
        ]
  in
  Rule.mk_infrule apply
```

### 4.5 First two-premise inference

```ocaml
let conj =
  let apply seq =
    match Seq.find_suchthat_opt Form.is_conj seq with
    | None -> []
    | Some principal ->
        let left, right = Option.get (Form.dest_conj principal) in
        let context = Seq.remove principal seq in
        let premise1 = Seq.add left context in
        let premise2 = Seq.add right context in
        [
          ( [
              (premise1, Tagpairs.empty, Tagpairs.empty);
              (premise2, Tagpairs.empty, Tagpairs.empty);
            ],
            "Conj" );
        ]
  in
  Rule.mk_infrule apply
```

This code contains one application with two obligations. Returning two
applications with one premise each would implement a different calculus.

### 4.6 Strategy

```ocaml
let axioms = ref identity

let rules =
  ref (Rule.first [ disj; conj ])
```

Begin with `Rule.first` only if the selected rules are invertible or the
priority is justified. If both rule families represent genuine alternatives,
use `Rule.choice`. Write a test where both apply so the intended commitment is
visible.

### 4.7 Direct search test before CLI work

```ocaml
open Generic
open Mylogic

module P = Prover.Make (Seq)
module F = Frontend.Make (P)

let prove seq = F.idfs !Rules.axioms !Rules.rules seq

let () =
  let goal = Seq.of_string "(p ∨ ¬p)" in
  match prove goal with
  | Some proof -> assert (P.Proof.is_closed proof)
  | None -> failwith "expected proof"
```

Add a negative case too. A test that only checks a positive result will not
catch a rule that unsoundly closes every goal.

## 5. Wire the Dune library

An initial [`src/mylogic/dune`](../src/ltl/dune)-style stanza is:

```lisp
(library
 (name mylogic)
 (public_name cyclist.mylogic)
 (libraries lib generic mparser-re cmdliner)
 (modules (:standard)))
```

Trim unused dependencies after the code compiles. If parsing uses only the
base `mparser` library, follow LTL's dependency choice instead.

Test stanza in `src/mylogic/test/dune`:

```lisp
(test
 (name test)
 (libraries mylogic generic)
 (modules test))
```

Run the library/test target early rather than waiting for the complete CLI:

```bash
opam exec -- dune build @src/mylogic/all
opam exec -- dune runtest src/mylogic/test
```

## 6. Wire a command

`prove.mli` can be as small as:

```ocaml
val cmd : unit Cmdliner.Cmd.t
```

`prove.ml` follows the standard pattern:

```ocaml
open Generic
module Prover = Prover.Make (Seq)
module F = Frontend.Make (Prover)

let run sequent () =
  let seq = Seq.of_string sequent in
  F.exit (F.prove_seq !Rules.axioms !Rules.rules seq)

let cmd =
  let open Cmdliner in
  let sequent =
    Arg.(
      required
      & opt (some string) None
      & info [ "S"; "sequent" ] ~docv:"SEQUENT"
          ~doc:"Prove the supplied sequent.")
  in
  Cmd.v
    (Cmd.info "prove" ~doc:"Prove a MyLogic sequent."
       ~exits:Frontend.exits)
    Term.(const run $ sequent $ F.common_term ())
```

Then make two integration edits:

1. Add `mylogic` to the executable libraries in
   [`src/cli/dune`](../src/cli/dune).
2. Add a command group in [`src/cli/cyclist.ml`](../src/cli/cyclist.ml):

```ocaml
group "mylogic" ~doc:"My logic." [ Mylogic.Prove.cmd ];
```

Finally add `mylogic --help` and `mylogic prove --help` to
[`tests/cli/dune`](../tests/cli/dune). Cmdliner constructs leaf parsers lazily;
the explicit help smoke tests catch malformed or colliding options.

## 7. Milestone B: add dynamic definitions or configuration

If rules depend on a definitions file, imitate `Firstorder.Rules.setup`:

```ocaml
let axioms = ref Rule.fail
let rules = ref Rule.fail

let setup defs =
  let unfold_left = make_left_rules defs in
  let unfold_right = make_right_rules defs in
  axioms := Rule.first [ identity; contradiction ];
  rules := Rule.first [ simplify; Rule.choice [ unfold_left; unfold_right ] ]
```

Command order must be:

```text
parse goal
parse/validate definitions
Rules.setup defs
run search
```

Preserve source definition order if it intentionally controls search order.
The first-order `Defs` module uses an association list for exactly that reason.

Validate definitions once in setup when possible:

- arities match;
- referenced symbols exist;
- variables obey binding/freshness rules;
- positivity or guardedness conditions hold;
- every rule body has the expected normal form.

Failing early produces better errors than discovering malformed definitions in
the middle of a search.

## 8. Milestone C: add substitutions and unification only if needed

There are two patterns in the repository:

1. the older first-order logic has direct term substitutions and domain-level
   unification functions;
2. separation logic uses generic continuation-passing-style unifiers with a
   state containing term substitutions and tag substitutions.

Read [`src/lib/unification.mli`](../src/lib/unification.mli) before the SL
unifiers. The central type is:

```ocaml
type ('state, 'result, 'term) cps_unifier =
  'term -> 'term ->
  ('state -> 'result option) ->
  ('state -> 'result option)
```

Conceptually, a unifier extends an input state and passes it to a continuation.
The continuation can reject that candidate, enabling controlled backtracking.

Do not adopt the CPS machinery for a domain where a simple deterministic
`term -> term -> substitution option` is sufficient. Complexity here should be
driven by multiple matches and compositional side checks, not architectural
imitation.

Substitution tests must cover:

- identity;
- composition/order;
- occurs or cyclic-substitution rejection if relevant;
- free versus existential variables;
- freshness after unfolding;
- agreement between substituted equality and hashing/ordering;
- tag substitution separately from term substitution.

## 9. Milestone D: design cyclic traces

Only start this phase after the acyclic prover, parser, CLI, and tests work.

### 9.1 Occurrence model

Choose what gets a tag. Typical choices are:

```text
formula occurrence    e.g. LTL □A
predicate occurrence  e.g. an inductive heap predicate
loop obligation       e.g. a termination trace
ordinal constraint    e.g. an explicit rank variable
```

Write the invariant next to the representation, as LTL does in `seq.ml`.

### 9.2 Edge worksheet

For each rule, draw occurrence flow:

```text
conclusion                         premise

context occurrence [a] ----------> context occurrence [a']  preserving
principal occurrence [b] --unfold-> recursive child [c]     progressing
principal occurrence [b] --unfold-> nonrecursive material   no trace
deleted occurrence [d]             (none)                    no pair
new unrelated occurrence           [e]                       no source pair
```

Then encode:

```ocaml
let valid = Tagpairs.of_list [ (a, a'); (b, c) ]
let progress = Tagpairs.singleton (b, c)
```

The exact constructor names available come from `Tagpairs`, an ordered
container; `singleton`, `add`, `union`, and `mk` are the common operations.

### 9.3 Backlink matcher

Start with exact equality modulo tags:

```ocaml
let backlink =
  let select idx proof = Rule.ancestor_nodes idx proof in
  let match_goal bud companion =
    if not (Seq.equal_upto_tags bud companion) then []
    else
      let relation = Seq.matching_tags ~from_:bud ~to_:companion in
      [ (relation, "Backlink") ]
  in
  Rule.mk_backrule false select match_goal
```

Prefer ancestors for the first implementation because the intended cycle is
easier to inspect. General-node backlinks can be added after tests establish
their necessity.

If your calculus permits backlinking only after substitution or weakening, do
what Firstorder and Seplog do: make those transformations explicit inference
nodes and end the sequence with an exact backlink. This keeps the proof graph
honest and gives the soundness checker transitions for every step.

### 9.4 Soundness test matrix

At minimum:

| Test | Expected |
|---|---|
| Acyclic theorem | proof |
| Valid one-cycle theorem | proof with at least one backlink |
| Same syntactic cycle with all progress pairs removed | no accepted backlink/proof |
| Progress pair not contained in valid relation | structural rejection/assertion in a direct checker test |
| Pair source tag absent from source node | structural rejection |
| Pair target tag absent from target node | structural rejection |
| Tag-renamed equal bud/companion | accepted or rejected according to your intended matcher |
| Non-equal bud/companion | no backlink application |

Use the abstract tests in [`tests/soundness`](../tests/soundness) as templates
for checker-level cases.

## 10. Strategy construction is part of the implementation

A correct rule set with a poor strategy may look broken. Document the strategy
as phases:

```text
Phase 1: local closure
  axioms / contradiction

Phase 2: deterministic normalization
  substitutions / remove trivial equations / normalize

Phase 3: cheap cycle closure
  exact backlink / guided transform + backlink

Phase 4: invertible decomposition
  logical rules with no loss of completeness

Phase 5: branching choices
  unfolds / cuts / instantiations / lemmas
```

Encode priority with `Rule.first` and genuine alternatives with `Rule.choice`.
Whenever you use `first`, write a negative regression test for a goal where the
earlier family applies but eventually fails; confirm that committing is
mathematically intended.

### 10.1 Axiom placement patterns

LTL passes a separate axiom rule to `Prover.idfs` and leaves it out of its main
strategy. Seplog's setup instead combines axioms into the main strategy:

```ocaml
rules := Rule.combine_axioms axioms !rules
```

`combine_axioms` tries an axiom first and attempts axioms on premises after an
inference. Choose one consistent pattern. Avoid accidentally duplicating
expensive axiom checks in both paths.

## 11. Parser and printer engineering

Implement and test these properties:

```text
parse (print x) = x             where the printer emits accepted syntax
print (parse input) is stable   after normalization
full input is consumed          trailing garbage is rejected
error locations are useful     especially for definition/program files
```

Repository helpers:

- `Lib.mk_to_string pp` derives `to_string`;
- `Lib.mk_of_string parse` or `handle_reply (MParser.parse_string ...)` handles
  parse results;
- `Lib.Symbols.Tokens` provides punctuation/token parsers;
- `attempt` is necessary for alternatives with overlapping prefixes;
- pretty-printers should use `Format` boxes rather than string concatenation
  for nested proof output.

Keep Unicode CLI syntax only if your users can enter it reliably. Providing an
ASCII alias in the parser can improve tests and scripts without changing the
printer.

## 12. Testing plan by layer

```text
Layer 1: data
  compare/equal/hash, freshness, substitution, normalization

Layer 2: parser
  valid inputs, invalid inputs, round trips

Layer 3: individual rules
  inapplicable case, each alternative, exact premises, exact trace pairs

Layer 4: proof graph
  expected node types/count, backlink count, closedness

Layer 5: search
  positive, negative, bound-sensitive and strategy-order examples

Layer 6: cyclic soundness
  accepted/rejected cycles and malformed abstract relations

Layer 7: CLI
  help, option parsing, result text, exit code

Layer 8: benchmarks
  representative correctness set and time/node-count regression
```

Test rule-producing functions directly before wrapping them in `Rule.mk_*`.
That makes premise and transition failures much easier to diagnose than a final
“not proved.”

## 13. Extending an existing logic instead

Use the smallest relevant change set:

| Desired change | Usually edit | Also audit |
|---|---|---|
| Add syntax constructor | `form`/`term` `.mli` and `.ml` | every pattern match, compare/hash/pp/parser, substitutions, vars/tags |
| Add an axiom | `rules.ml`, perhaps `rules.mli` | axiom ordering and whether strategy uses separate/combined axioms |
| Add inference rule | `rules.ml` and strategy assembly | tag flow, `first` versus `choice`, unit/search tests |
| Change backlink matching | `rules.ml` | equality semantics, explicit transforms, selection scope, soundness tests |
| Add definitions-file feature | definition AST/parser plus `Rules.setup` | validation, freshening, source order, CLI file option |
| Add command option | the logic's `prove.ml` | mutable ref reset, help smoke test, defaults shown in help |
| Add a new command | new command module and `.mli` | logic `dune`, CLI libraries, root command tree, CLI tests |
| Add program statement | `program` AST/parser/printer and `rules` | vars/modifies/dependencies, symbolic execution, procedures, examples |

Before editing, use `rg` to find every constructor use and every strategy
assembly site. OCaml exhaustiveness warnings help, but this project suppresses
warning 9 only; do not depend solely on the compiler to identify semantic
operations such as `vars`, `tags`, or normalization.

## 14. Common implementation mistakes

| Mistake | Symptom | Prevention |
|---|---|---|
| Confuse alternatives with premises | Unsound success or unnecessary failure | Draw OR/AND tree for each returned nested list |
| Return identity as a “successful simplification” under `repeat` | Nontermination | Return `[]` when no structural progress occurred |
| Use `Rule.first` for genuine alternatives | Valid proofs disappear | Use `choice`, or prove priority completeness |
| Mark every trace transition progressing | Cycles accepted for the wrong reason | Tie progress to the formal well-founded measure |
| Forget a context tag pair | Valid cyclic proof rejected | Compute occurrence correspondence explicitly |
| Reuse tags for duplicate occurrences | Ambiguous traces | State and enforce a uniqueness invariant |
| Make `equal` ignore tags | Proof replacement/backlink checks lose intended distinction | Keep exact and modulo-tag equality separate |
| Forget `Rules.setup` | Main rule is `Rule.fail`; every non-axiom fails | Make setup part of command/test fixture |
| Build formulas by raw representation | Freshness/normalization invariants break | Route changes through constructors |
| Ignore definition/rule order | Large performance regression | Preserve and test intended enumeration order |
| Test only “proved” cases | Unsound rules go unnoticed | Pair each positive family with negatives |
| Modify generic search for a domain heuristic | Other logics regress | Express policy in the concrete strategy first |

## 15. Definition of done for your first version

- [ ] Formula/term and sequent invariants are documented beside their types.
- [ ] `compare`, `equal`, `hash`, parsing, and printing agree.
- [ ] Every rule has direct tests of applications, premises, and trace pairs.
- [ ] Strategy use of `first`, `choice`, `compose`, and `repeat` is justified.
- [ ] Acyclic positive and negative examples pass.
- [ ] The CLI command, help leaves, output, and exit codes are tested.
- [ ] Every cyclic rule has a written occurrence-flow/progress argument.
- [ ] At least one valid cyclic proof has a backlink.
- [ ] Removing required progress causes that cyclic proof to be rejected.
- [ ] Malformed tag-relation tests exercise structural checks.
- [ ] Search bounds/timeouts fail cleanly.
- [ ] Representative benchmarks record proof size, backlink count, search depth,
      and time before and after the change.
- [ ] `dune build @all @runtest`, formatting, and documentation build pass in a
      fully provisioned environment.

The last two items matter: in a proof-search codebase, correctness and search
behavior are both part of the usable implementation.
