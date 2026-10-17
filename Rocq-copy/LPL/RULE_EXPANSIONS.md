# Explicit sequent expansions of the double-line rules

This catalog fulfills D3 of [IMPLEMENTATION_PLAN.md](IMPLEMENTATION_PLAN.md):
expand every active double-line display before implementing rule constructors
or rule generation. It specifies inference shapes, not completed Rocq proofs.
D1 interprets label mappings by direct juxtaposition, retaining all states
of both operands. D4 requires asserted labels to have nonempty interpretations.
Both D2 restrictions apply throughout: quantifier bodies are pure FOL, with
no program modalities or temporal operators, and the eigenvariables of
universal-right/existential-left are also fresh for the principal label.

The source is [20260926-Types-by-AI.tex](Theory/20260926-Types-by-AI.tex), checked
against [the PDF](Theory/20260926-Types-by-AI.pdf). Line numbers identify the
current source. Commented-out displays and inactive alternatives are excluded.

## Reading and expansion conventions

Each block lists premises above the line and the conclusion below it. `Γ` and
`Δ` are arbitrary contexts; a comma on one side of a sequent joins formulas in
that context. Separately displayed premises must all be proved. `U` is a
first-order program update, `σ` is a label, and `◇` retains the manuscript's
label constructor, interpreted by direct juxtaposition under D1. `A` and `B`
denote formulas, `P` a predicate atom or equality, and `e` a first-order term.
All syntax must be well formed.

All schemes use D4's guarded sequent denotation. Formula satisfaction is used
only where the complete assertion label has a defined, nonempty interpretation;
empty components remain allowed by the unit laws. The ordinary semantic proof
must establish admissibility for its premise mappings. In particular, a
countermodel step must produce an admissible false premise from an admissible
false conclusion. Label evaluation is total and has no endpoint-matching
condition: juxtaposing labels denoting `s0` and `s1` gives `[s0; s1]`, even when
the states differ or are equal. Keep overlapping program-trace composition
separate. Empty complete labels cannot be handled by arbitrary default states
or by using inadmissible premises as vacuously valid proofs. These
admissibility obligations accompany every scheme below, including weakening,
cut when used to derive a scheme, and label substitution.

For the formula-only double-line shorthand with one or more replacements,
Section 4.2, source lines 1250–1286, prescribes one left and one right rule:

```text
Γ ⇒ F₁, Δ    ...    Γ ⇒ Fₙ, Δ
-----------------------------  R
Γ ⇒ F, Δ

Γ, F₁ ⇒ Δ    ...    Γ, Fₙ ⇒ Δ
-----------------------------  L
Γ, F ⇒ Δ
```

This convention does not automatically assert reverse inference directions.
Double-line displays that already contain whole sequents, such as the test
rules, are written out as their explicit named left/right sequents below;
they are not treated as formulas to which another sequent wrapper is added.

For weakening, removing the principal formula leaves the context-only sequent
`Γ ⇒ Δ`. Thus its expansion has one context-only premise on either side.
It is not a zero-premise axiom. This is the explicit weakening convention used
by this catalog, made visible before any rule is implemented.

## Inventory

| Active double-line display | Source line | Explicit schemes below | Premises per scheme |
| --- | --- | --- | --- |
| Box-test right | 1338 | B.Test.R | 1 |
| Box-test left | 1339 | B.Test.L | 1 |
| Box sequence | 1340 | B.Seq.R, B.Seq.L | 1, 1 |
| Box choice | 1341 | B.Choice.R, B.Choice.L | 2, 2 |
| Box star | 1342 | B.Star.R, B.Star.L | 2, 2 |
| Propositional atom at head `(p)` | 1358 | P.Head.R, P.Head.L | 1, 1; replaced by At.R/At.L in FOPL |
| First-state | 1359 | First.R, First.L | 1, 1 |
| Weakening | 1413 | Wk.R, Wk.L | 1, 1 |
| Diamond-test right | 1497 | D.Test.R | 1 |
| Diamond-test left | 1498 | D.Test.L | 1 |
| Diamond sequence | 1499 | D.Seq.R, D.Seq.L | 1, 1 |
| Box assignment | 2660 | B.Assign.R, B.Assign.L | 1, 1 |
| First-order atom at head `(at)` | 2661 | At.R, At.L | 1, 1 |
| Diamond assignment | 2694 | D.Assign.R, D.Assign.L | 1, 1 |

There are 14 active displays and 24 explicit schemes in this catalog. The
propositional `(p)` pair is documented for source coverage; its first-order
replacement is `(at)`, so it does not require a second, separate pair of FOPL
rule constructors. The box/diamond atomic-action rules with relational atoms
are replaced by assignment rules in FOPL and are not additional double-line
displays.

## Box tests

Specialize the manuscript's world variable to update `U`, as Section 7.2
requires. The test condition is evaluated on `U ◇ U`, and the postcondition
retains the entire prefix. These are the two already-sequent-shaped displays.

```text
Γ, U ◇ U:B ⇒ σ ◇ U ◇ U:A, Δ
--------------------------------  B.Test.R
Γ ⇒ σ ◇ U:[B?]A, Δ
```

```text
Γ, σ ◇ U ◇ U:A ⇒ Δ
---------------------------------------------  B.Test.L
Γ, σ ◇ U:[B?]A, U ◇ U:B ⇒ Δ
```

There is no fresh-world-variable side condition here. Prove D4's admissibility
transfer explicitly. Under D1, `U ◇ U` retains the two-state stutter `[s; s]`,
as required by test semantics.

## Box sequence

```text
Γ ⇒ σ:[α][β]A, Δ
-----------------------  B.Seq.R
Γ ⇒ σ:[α;β]A, Δ
```

```text
Γ, σ:[α][β]A ⇒ Δ
-----------------------  B.Seq.L
Γ, σ:[α;β]A ⇒ Δ
```

## Box choice

```text
Γ ⇒ σ:[α]A, Δ       Γ ⇒ σ:[β]A, Δ
------------------------------------  B.Choice.R
Γ ⇒ σ:[α ∪ β]A, Δ
```

```text
Γ, σ:[α]A ⇒ Δ       Γ, σ:[β]A ⇒ Δ
------------------------------------  B.Choice.L
Γ, σ:[α ∪ β]A ⇒ Δ
```

Both schemes have two premises under the manuscript's stated shorthand.
Do not silently replace B.Choice.L with the alternative one-premise rule
whose antecedent contains both boxes, or treat either displayed scheme as
an assertion that its premises follow from its conclusion.

## Box star

```text
Γ ⇒ σ:[true?]A, Δ       Γ ⇒ σ:[α][α*]A, Δ
---------------------------------------------  B.Star.R
Γ ⇒ σ:[α*]A, Δ
```

```text
Γ, σ:[true?]A ⇒ Δ       Γ, σ:[α][α*]A ⇒ Δ
---------------------------------------------  B.Star.L
Γ, σ:[α*]A ⇒ Δ
```

Retain two premises on each side and the explicit `[true?]` base case. The
manuscript defines zero iterations using the stuttering test, so it is not
silently replaced by the bare formula `A`. Star unfolding itself does not
constitute a progressing assignment/test trace step.

## Propositional atom at the head: inherited source counterpart

The original propositional display uses a world variable `x`:

```text
Γ ⇒ x:p, Δ
-----------------------  P.Head.R
Γ ⇒ x ◇ σ:p, Δ
```

```text
Γ, x:p ⇒ Δ
-----------------------  P.Head.L
Γ, x ◇ σ:p ⇒ Δ
```

In FOPL this role is filled by At.R and At.L below, with an explicit update
and a first-order atom. These two source expansions are not additional
propositional-logic implementation scope.

## First-state operator

`First` denotes the manuscript's primitive first-state operator.

```text
Γ ⇒ U:A, Δ
------------------------------  First.R
Γ ⇒ U ◇ σ:First(A), Δ
```

```text
Γ, U:A ⇒ Δ
------------------------------  First.L
Γ, U ◇ σ:First(A) ⇒ Δ
```

This restriction of the evaluated trace to its first state is separate from
the syntactic restriction on bodies of first-order quantifiers.

## Weakening

```text
Γ ⇒ Δ
-----------------------  Wk.R
Γ ⇒ σ:A, Δ
```

```text
Γ ⇒ Δ
-----------------------  Wk.L
Γ, σ:A ⇒ Δ
```

Each rule has exactly one premise. The removed formula supplies no trace
continuation; only surviving, proved context continuations may be advertised
on its edge. In particular, an empty context-only sequent `· ⇒ ·` is not
automatically valid and is not an axiom.

## Diamond tests

These are the explicit named test-right and test-left displays from the
derived-rule table. As with box tests, `x` is specialized to update `U`.

```text
Γ ⇒ σ ◇ U ◇ U:A, Δ
---------------------------------------------  D.Test.R
Γ, U ◇ U:B ⇒ σ ◇ U:⟨B?⟩A, Δ
```

```text
Γ, σ ◇ U ◇ U:A, U ◇ U:B ⇒ Δ
--------------------------------  D.Test.L
Γ, σ ◇ U:⟨B?⟩A ⇒ Δ
```

Preserve the placement of the test guard in each rule. Each displayed scheme
is a one-premise inference; additional reverse directions need their own
stated schemas and semantic proofs. Deriving these rules from primitive
rules requires D4's admissibility transfer and D1's retention of both states
in the test stutter.

## Diamond sequence

```text
Γ ⇒ σ:⟨α⟩⟨β⟩A, Δ
-------------------------  D.Seq.R
Γ ⇒ σ:⟨α;β⟩A, Δ
```

```text
Γ, σ:⟨α⟩⟨β⟩A ⇒ Δ
-------------------------  D.Seq.L
Γ, σ:⟨α;β⟩A ⇒ Δ
```

## Box assignment

```text
Γ ⇒ σ ◇ U ◇ {u:=e}U:A, Δ
--------------------------------  B.Assign.R
Γ ⇒ σ ◇ U:[u:=e]A, Δ
```

```text
Γ, σ ◇ U ◇ {u:=e}U:A ⇒ Δ
--------------------------------  B.Assign.L
Γ, σ ◇ U:[u:=e]A ⇒ Δ
```

The new update evaluates `e` in the state denoted by `U`, then writes `u`.
The formula `A` is not syntactically rewritten by this rule. Only a justified
right-hand trace continuation may claim assignment progress. Under D1 the
replacement retains the pre-state and post-state as successive states, with
no endpoint-equality condition between those label components.

## First-order atom at the head

For the manuscript's arithmetic atoms, `P` is `e₁ △ e₂`. For the requested
general signature, use arbitrary predicate applications and built-in equality,
with their ordinary first-order interpretations; prove this generalization.

```text
Γ ⇒ U:P, Δ
-----------------------  At.R
Γ ⇒ U ◇ σ:P, Δ
```

```text
Γ, U:P ⇒ Δ
-----------------------  At.L
Γ, U ◇ σ:P ⇒ Δ
```

No induction hypothesis or rank for `P` is assumed. Atom truth is interpreted
at the state denoted by `U`; this pair replaces P.Head.R/P.Head.L in FOPL.

## Diamond assignment

```text
Γ ⇒ σ ◇ U ◇ {u:=e}U:A, Δ
--------------------------------  D.Assign.R
Γ ⇒ σ ◇ U:⟨u:=e⟩A, Δ
```

```text
Γ, σ ◇ U ◇ {u:=e}U:A ⇒ Δ
--------------------------------  D.Assign.L
Γ, σ ◇ U:⟨u:=e⟩A ⇒ Δ
```

These are derived-rule schemas. Their construction must be justified from
the primitive rules/duality or by separate semantic theorems, including the
required countermodel and edge obligations. A diamond occurrence is not a
new trace-element family merely because its rule is derived from box rules.

## Implementation and verification gate

### Explicit label-algebra helper

The implementation additionally exposes a caller-selected reassociation at a
specified binary-label path. This is an ordinary one-premise structural
consequence of D1's list append associativity (no change to formula meaning):

```text
Gamma => Delta
-------------------------------- Label.Assoc
rotate_path(Gamma) => rotate_path(Delta)
```

At the selected path, a left rotation replaces `a ◇ (b ◇ c)` by
`(a ◇ b) ◇ c`; a right rotation performs the inverse. A nonmatching path
leaves that label unchanged. The caller supplies both the premise judgment
and the path/direction; no normalization search is performed. This helper
does not add a double-line display to the manuscript inventory above.

`Label.Unit` has the same one-premise context scheme and a caller-selected
path. It inserts or removes `epsilon ◇ a` or `a ◇ epsilon` at that path,
using the proved D1 unit laws. Removing a nonmatching unit leaves the label
unchanged. Complete-label admissibility is checked on both judgments.

Before implementing a covered rule family:

1. Match its explicit scheme to the inventory entry and intended FOPL
   specialization. Keep the exact ordered premise list and context placement.
2. State all syntactic side conditions and the agreed D2/D4 restrictions.
   Prove admissibility of the premise mappings used by soundness and
   countermodel steps; preserve empty-unit components and exclude empty
   complete assertion labels. Use D1's direct juxtaposition for labels and
   the separate overlapping operation for program-trace composition.
3. Prove ordinary soundness and the framework's stronger `rule_counter_step`,
   with every advertised tag/rank inequality. A textual expansion proves
   neither obligation by itself.
4. Give each supported left/right scheme its own named constructor and
   generator branch. Verify exact premise count, conclusions, contexts, and
   trace-edge metadata in generator regressions. Wk.R/Wk.L must never be
   generated as closing axioms.

Any new double-line rule introduced during implementation must first receive
the same explicit expansion and review in this catalog. Do not implement
commented-out contraction or alternative rules merely because they occur in
the manuscript source.

## Refinement ownership and relational G3PPL rules

The preceding expansions are preserved for the migrated FOPL image. In the
shared implementation, a displayed world/update position is a parameterized
world-denoting term `u`. The propositional `(p)` pair is restored as the generic
atom-head `At.L`/`At.R` pair; FOPL instantiates it with predicate/equality atoms.
Boolean, regular, temporal, label, and structural expansions are shared kernels;
assignment and quantifier kernels are first-order additions.

Relational assumptions are written separately as `R ; Gamma => Delta` and
receive no formula tags. `E(a,u,v)` abbreviates the distinguished action relation
with singleton endpoint labels. Four single-line schemes complement the
existing double-line catalog:

```text
R ; Gamma => sigma u : [a]A, Delta
    premise: R, E(a,u,y) ; Gamma => sigma u y : A, Delta       B.Atomic.R
    y is fresh for every label and relational argument in the conclusion.

R1, E(a,u,v), R2 ; Gamma, sigma u : [a]A => Delta
    premise: R1, R2 ; Gamma, sigma u v : A => Delta            B.Atomic.L

R1, E(a,u,v), R2 ; Gamma => sigma u : <a>A, Delta
    premise: R1, R2 ; Gamma => sigma u v : A, Delta            D.Atomic.R

R ; Gamma, sigma u : <a>A => Delta
    premise: R, E(a,u,y) ; Gamma, sigma u y : A => Delta       D.Atomic.L
    y is fresh for every label and relational argument in the conclusion.
```

The source/premise lists, context order, and selected relation occurrence are
literal. `AtomicUse` takes a relation index; a reconstructed mismatching action
or source fails the conclusion-equality check. A fresh-successor request scans
world-name support in both formula labels and relational arguments.
`B.Atomic.R` selects a minimum counterexample successor for its joint
counterstep. A principal pair is progressing only when a traceable replacement
actually carries the continuing tag. Other retained context pairs have proved
nonincrease at that same mapping.

The manuscript's cut with two complete contexts is `Cut.Relations`:

```text
R1, R2 ; Gamma, Sigma => Delta, Lambda
    premises: R1 ; Gamma => cut, Delta
              R2 ; Sigma, cut => Lambda
```

`CutRelations` explicitly supplies both relational and formula partitions.
The existing `Cut` request retains a common fixed relational context, preserving
the legacy empty-context instance. Relation weakening, exchange, and contraction
are separate proved structural requests; weakening a relation retains one
premise and never becomes an axiom.

`Benchmarks/PPL/RuleCoverage.v` checks the common expansions, the four relational
action schemes, relation structural operations, both cut forms, label algebra,
and concrete rejection cases. `FOPL/Benchmarks/RuleCoverage.v` retains the
original 50 premise-shape checks. T1 is resolved: all test guards in these
schemes are evaluated on the two-state stutter `[s; s]`.


## Primitive syntax and deterministic view order

The shared datatype contains `Truth`, `Atom`, `Neg`, `Conj`, `Extension`,
`First`, `Suffix`, and `Box`. The formula names used in the displays retain
their mathematical meaning through these definitions:

```coq
Falsity             := Neg Truth
Disj a b            := Neg (Conj (Neg a) (Neg b))
Impl a b            := Neg (Conj a (Neg b))
Coextension x a     := Neg (Extension x (Neg a))
DualSuffix a b      := Neg (Suffix (Neg a) (Neg b))
Diamond p a         := Neg (Box p (Neg a))
```

A local occurrence contributes candidates in order: `disj_view`, `impl_view`,
`diamond_view`, `dual_suffix_view`, then its primitive case. The lists append;
a successful disjunction view does not suppress implication or negation rules.
FOPL places quantifier/assignment candidates before primitive fallback. Each
view has a reconstruction theorem in `Syntax.v`. Named rule requests select
from these candidates and still validate the exact source and ordered premises.

`Atom` and `Atomic` take one opaque payload. `ActionRelation action source target`
and the common `action_relation action u v` have no separate argument/value
field. FOPL's `Pred`, `Equal`, and `Assign` construct its own structured payloads.
The 50 FOPL / 53 PPL premise-shape checks and the displayed rule names remain.
Expanded dual suffixes retain their right continuation and strict rank decrease;
other negations receive no additional progress edge.
