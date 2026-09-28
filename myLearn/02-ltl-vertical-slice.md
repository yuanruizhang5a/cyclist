# 02 — LTL vertical slice

The LTL prover is the best executable specification of how to build on the
generic engine. It has a real cyclic argument and tags, but only four source
modules and no term unification or external definitions.

## 1. Read the files in dependency order

```text
form.ml
  defines formula syntax, parser, equality, printer, and destructors
     |
     v
seq.ml
  stores tagged formulas and implements Generic.Sequent.S
     |
     v
rules.ml
  instantiates Proofrule.Make(Seq), defines calculus and strategy
     |
     v
prove.ml
  parses CLI input and invokes Generic.Frontend/Prover
     |
     v
src/cli/cyclist.ml
  places Ltl.Prove.cmd under the "ltl" command group
```

Keep [`src/ltl/test/test.ml`](../src/ltl/test/test.ml) open as the collection of
small executable examples.

## 2. `Form`: syntax is a closed, normalized language

[`src/ltl/form.ml`](../src/ltl/form.ml) defines:

```ocaml
type t =
  | Atom of string
  | NegAtom of string
  | Conj of t * t
  | Disj of t * t
  | Next of t
  | Always of t
  | Eventually of t
```

Negation is pushed to atoms. `Form.neg` implements the dualities rather than
adding a general `Neg of t` node:

```text
¬(A ∧ B) = ¬A ∨ ¬B
¬(A ∨ B) = ¬A ∧ ¬B
¬○A      = ○¬A
¬□A      = ◇¬A
¬◇A      = □¬A
```

This matters to rules: the axiom only needs to detect `Atom p` together with
`NegAtom p`; it never recursively normalizes arbitrary negation during proof
search.

### 2.1 `BasicType` is a recurring repository convention

`Form` implements `Lib.BasicType`, which requires comparison/equality,
hashing, and printing. The hand-written `compare` gives a total order over the
variant constructors. That makes formulas usable in `Treeset` and other
generic containers.

When adding a constructor:

1. extend `ord` with a distinct rank;
2. extend `compare` structurally;
3. extend `pp` and `parse`;
4. extend `neg` if the syntax is closed under negation;
5. add constructors/destructors/predicates used by rules;
6. add parser and round-trip tests.

Missing step 2 can silently corrupt set behavior: ordered containers assume
that `compare x y = 0` exactly when values should count as equal.

### 2.2 Parser structure

The parser uses `MParser` and `MParser_RE` combinators. Alternatives that share
prefixes are wrapped in `attempt`, because a failed branch may otherwise
consume input and prevent later alternatives.

The current grammar accepts:

```text
identifier
¬identifier
○ formula
□ formula
◇ formula
(formula ∧ formula)
(formula ∨ formula)
```

It is fully parenthesized for binary connectives. Do not assume conventional
operator precedence when creating CLI examples.

## 3. `Seq`: formulas plus hidden trace labels

The LTL sequent is a set of pairs:

```ocaml
type Formula.t = Tags.Elt.t * Form.t
type Seq.t = FormulaSet.t
```

This is a one-sided sequent. Semantically, its formulas form a disjunction.
That explains the proof rules later.

### 3.1 A subtle comparison design

`Formula.compare` and `Formula.equal` ignore the tag and compare only the
formula. Consequently:

- a `FormulaSet` cannot contain two tagged copies of the same formula;
- `FormulaSet.equal` is equality modulo tags;
- `Seq.equal_upto_tags` can be exactly `FormulaSet.equal`;
- exact sequent equality must explicitly compare both the stored tag and
  formula.

The current implementation of `Seq.equal` iterates over the first set and
looks for a formula with both matching tag and syntax in the second. It does
not compare cardinalities or perform the reverse containment check. Therefore,
as written, it can return true when its first argument is a strict subset of
its second. Treat this as a source-level audit point, not as a pattern to copy:
a new implementation should check equal cardinality (or both directions) in
addition to exact tagged membership.

This pattern is specific to the representation invariant. Do not copy it if
your calculus needs multiple occurrences of the same formula; use a multiset
or occurrences with explicit identities instead.

### 3.2 Which formulas are traceable?

`Form.is_traceable` returns true only for:

```ocaml
Always _ | Next (Always _)
```

Traceable formulas receive fresh free tags. Other formulas use the anonymous
tag, which `Seq.tags` removes before returning the node's tag set.

Maintained invariants from the source comment:

1. traceable formulas have free tags;
2. non-traceable formulas have the anonymous tag;
3. free tags are unique within one sequent.

`Seq.of_list`, `Seq.add`, and `Seq.add_all` are where those invariants are
enforced. Rules should use these constructors rather than assembling raw
`FormulaSet` values.

### 3.3 Set operations and tag provenance

Operations such as `inter` and `diff` need care because equal formulas can have
different tags. The source relies on the underlying set operation returning
elements from a predictable input set. When a rule needs to preserve trace
identity, check which operand contributes the retained element.

That issue is visible in the comments on LTL weakening and cut. It generalizes
to any representation where comparison deliberately ignores metadata.

## 4. Base rule contract in concrete form

At the top of [`src/ltl/rules.ml`](../src/ltl/rules.ml):

```ocaml
module Proof = Proof.Make (Seq)
module Rule = Proofrule.Make (Seq)
```

An LTL inference implementation has the shape:

```ocaml
let my_rule =
  let rl seq =
    match find_principal_formula seq with
    | None -> []
    | Some f ->
        let premise = transform seq f in
        let valid = ... in
        let progress = ... in
        [ ([ (premise, valid, progress) ], "My rule") ]
  in
  Rule.mk_infrule rl
```

The empty outer list means “not applicable.” The singleton outer list means
there is one possible application. Its inner singleton means that application
has one premise.

## 5. Each LTL rule, operationally

### 5.1 Axiom

```ocaml
let axiom =
  Rule.mk_axiom (fun s -> Option.mk (Seq.is_axiomatic s) "Axiom")
```

`Seq.is_axiomatic` looks for `p` and `¬p` in the one-sided sequent. `Some`
closes the node without premises; `None` makes the rule inapplicable.

### 5.2 Disjunction

```text
    Γ, A, B
--------------- Disj
  Γ, A ∨ B
```

There is one premise, because a one-sided sequent denotes the disjunction of
all its members. The rule removes the principal formula and adds both
components.

Only tags in the untouched context `Γ` are preserved:

```ocaml
let valid_tps = Tagpairs.mk (Seq.tags gamma)
let prog_tps = Tagpairs.empty
```

`Tagpairs.mk tags` is the identity relation `{(t,t) | t in tags}`.

### 5.3 Conjunction

```text
   Γ, A       Γ, B
------------------- Conj
      Γ, A ∧ B
```

This application has two premises and search must close both. Again, context
tags are preserved and no step is progressing.

### 5.4 Eventually

```text
  Γ, A, ○◇A
-------------- Eventually
      Γ, ◇A
```

It has one premise and no progressing pairs. The eventuality itself is not one
of this implementation's traceable formulas.

### 5.5 Always

```text
  Γ, A       Γ, ○□A
------------------- Always
       Γ, □A
```

This is the first rule where tracing matters.

Let tag `t` label the conclusion's `□A`; adding `○□A` to the right premise
allocates a fresh tag `t'`. Then:

```text
left premise:
  valid      = identity on tags of Γ
  progressing = empty

right premise:
  valid      = identity on tags of Γ plus (t,t')
  progressing = {(t,t')}
```

The strict progress is attached only to the temporal continuation branch. The
pair direction is conclusion tag `t` to premise tag `t'`.

### 5.6 Next

When the sequent contains at least one `Next`, this rule strips the outer
`Next` from every next-formula and discards formulas without it.

For each traceable `○□A` in the conclusion and corresponding `□A` in the
premise, it adds a tag pair. That relation is passed as both valid and
progressing, marking the actual temporal step.

Notice that the code folds over the **premise** with tags, reconstructs
`Form.next f'`, and looks that formula up in the conclusion. This is a common
way to compute occurrence correspondence when constructors generate fresh
tags.

## 6. Backlinks

The LTL matcher receives a bud and a potential companion:

```ocaml
let mk_backlink bud companion =
  if not (Seq.equal_upto_tags bud companion) then []
  else
    let tps = ... map each bud trace tag to companion trace tag ... in
    [ (tps, "Backlink") ]
```

Two nesting levels again matter:

- the selector supplies candidate target nodes;
- the matcher can supply zero or more ways to link to each candidate.

The backlink relation runs from tags at the bud to tags at the companion,
because that is the direction of the new graph edge.

The completed candidate is then checked globally by `Rule.mk_backrule`. A
formula match alone is not enough.

## 7. Proof-guided weakening

Unlike the base inference rules, `weaken` has type `Rule.t` directly rather
than being a pure `seq -> applications` function. It needs:

```ocaml
idx  : current proof-node index
prf  : whole proof graph
```

It gathers sequents at possible backlink targets and generates only weakenings
that move the current goal toward one of those targets. This is a search
heuristic embedded as a proof-level rule.

The sequence:

```ocaml
Rule.sequence [ weaken; backlink ]
```

means “perform a guided weakening, then immediately backlink every resulting
premise.” If the backlink cannot be formed, the composition yields no complete
application.

## 8. Strategy assembly

The strategy is:

```ocaml
let invertible_rules = [ disj; eventually; conj; always ]

let invertible_phase =
  let rules =
    Rule.conditional
      (fun seq -> not (Seq.is_axiomatic seq))
      (Rule.first invertible_rules)
  in
  Rule.compose rules (Rule.repeat rules)

let axioms = ref axiom

let rules =
  ref
    (Rule.first
       [
         backlink;
         Rule.sequence [ weaken; backlink ];
         invertible_phase;
         next;
       ])
```

Interpret it literally:

1. At a non-axiomatic goal, try a direct sound backlink.
2. If no backlink application exists, try guided weakening followed by a
   backlink.
3. Otherwise apply the first applicable invertible rule and keep applying
   invertible rules to all premises.
4. Use `next` only when no earlier family applies.

`Rule.first invertible_rules` processes the first principal formula found by
the first applicable rule family. Container ordering can therefore influence
which connective is decomposed first.

## 9. Worked proof: `(p ∨ ¬p)`

Input:

```text
(p ∨ ¬p)
```

### 9.1 Parse and sequent construction

```text
Form.parse
  -> Disj (Atom "p", NegAtom "p")

Seq.of_list [...]
  -> { (_, p ∨ ¬p) }
```

The formula is not traceable, so it has the anonymous tag and `Seq.tags` is
empty.

### 9.2 Search trace

```text
bound 1

node 0: Open {p ∨ ¬p}
  axiom? no
  backlink? no target
  weaken/backlink? no
  invertible_phase:
    Disj applies

node 0: Inf {p ∨ ¬p} (Disj)
  `-- node 1: Open {p, ¬p}

close node 1 with remaining bound 0
  axiom? yes

node 1: Axiom {p, ¬p}
proof returned
```

The inference edge has empty valid/progress relations because both node tag
sets are empty.

Printed shape:

```text
0: {(p ∨ ¬p)} (Disj) [1]
  1: {p, ¬p} (Axiom)
```

Exact punctuation depends on the pretty-printers, but the node states and
indices follow this structure.

## 10. Worked failure: `(p ∧ ¬p)`

Conjunction yields two obligations:

```text
             {p}        {¬p}
             open       open
             /             \
       no axiom/rule   no axiom/rule
                 \       /
                 application fails
```

Neither singleton is axiomatic and no logical rule decomposes an atom. The
search eventually exhausts its bounds and reports not proved. “Not proved” is
not in general a semantic countermodel; it only means this strategy found no
proof within its configured search.

## 11. A cyclic trace to inspect yourself

Use one of the modal theorems from [`benchmarks/ltl`](../benchmarks/ltl), for
example:

```text
(◇ p ∨ □ ¬p)
```

When the environment is built, run:

```bash
dune exec cyclist -- ltl prove \
  --sequent '(◇ p ∨ □ ¬p)' \
  --show-proof --debug --inf-desc ocaml
```

On paper, annotate every proof edge with:

```text
source sequent tags
valid pairs
progressing pairs
target sequent tags
```

Then check:

1. every pair source is present in the source node;
2. every pair target is present in the target node;
3. progress is a subset of valid;
4. a cycle accepted by the checker contains the required infinite progress.

This exercise is the bridge from “I understand rule code” to “I can implement
a sound cyclic calculus.”

## 12. How the command is exposed

[`src/ltl/prove.ml`](../src/ltl/prove.ml) does only four things:

1. instantiate `Prover.Make(Seq)`;
2. instantiate `Frontend.Make(Prover)`;
3. parse the sequent string with `Seq.of_string`;
4. invoke `F.prove_seq` with the strategy refs.

Its `cmd` value defines the leaf `prove` command. The root CLI later places it
under `ltl`:

```ocaml
group "ltl" ~doc:"Linear temporal logic." [ Ltl.Prove.cmd ]
```

The `ltl` library is also listed in `src/cli/dune`; both wiring steps are
required.

## 13. Exercises before using LTL as a template

Do these in order:

1. Add a parser round-trip test for a nested temporal formula without changing
   production code.
2. Manually compute the premise and tag pairs of `always` on
   `{r, □p}`.
3. Explain why `Rule.choice invertible_rules` would change search compared with
   `Rule.first invertible_rules`.
4. Add a temporary debug print in a local branch to list applications produced
   by `conj`, then remove it after checking your prediction.
5. Design a deliberately invalid backlink relation and predict which
   `Soundcheck.valid` condition it violates.

Once these are comfortable, continue to
[03 — Implementing a new logic](03-implementing-a-new-logic.md).
