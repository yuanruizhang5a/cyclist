# First-order labelled process logic in Rocq: implementation plan

Status: implementation plan. The user decisions for D1–D4 are
recorded in Section 3, and the double-line rule expansions are documented in
`RULE_EXPANSIONS.md`. D1 uses the user's clarified direct-juxtaposition label
mapping. No Rocq implementation has been started.

## 1. Scope and controlling requirements

Implement the first-order labelled process logic G3FOPL described in
[the manuscript](Theory/20260926-Types-by-AI.tex), with its
[PDF](Theory/20260926-Types-by-AI.pdf) used to check the active definitions and
rule displays. Follow [plan-guide.md](plan-guide.md), together with the user's
subsequent decisions. The older [requirements.md](requirements.md) mentions
SMTCoq; that option is superseded by the guide's standard-library-only policy.

The implementation will provide:

- An independent, signature-parametric first-order language with arbitrary
  interpretations, explicit universal and existential quantifiers, equality,
  conjunction, disjunction, implication, and unrestricted negation. Bodies of
  both quantifiers must be pure FOL formulas: no program modalities or temporal
  operators may occur anywhere inside them.
- Regular programs, finite-trace semantics, program updates, labels, labelled
  formulas, two-sided sequents, and reified graph judgments.
- A separate shallow interpretation into Rocq propositions.
- Explicit admissibility conditions requiring asserted labels to have defined,
  nonempty trace interpretations; the empty label remains the juxtaposition unit.
- Ordinary semantic rule proofs and theorem-backed `rule_instance` or
  `axiom_instance` records, following the pattern in `FirstOrder/Rules.v`.
- Executable, syntax-directed generation of those records, following
  `FirstOrder/RuleGeneration.v`, with caller-supplied instantiations when a rule
  has infinitely many possible parameters.
- Manually constructed proofs and cyclic certificates, plus small and complex
  benchmarks with a hard ten-minute limit per benchmark.

`Cyclic/` must remain byte-for-byte unchanged. `FirstOrder/` and `LTL/` are
architectural references; LPL must not import their object theories or use
their proof-search implementations. Do not consult `FirstOrderNew/`.

Out of scope: completeness, proof search, custom proof-search tactics,
unification-based backlink discovery, automated witness selection, SMTCoq,
external solvers, nonstandard Rocq libraries, and changes to the OCaml prover.
Pure first-order obligations are proved manually in Rocq using its existing
tactics. If they cannot be discharged, simplify or omit the benchmark and
record that outcome.

This is a plan for the full requested language. A fragment whose unresolved
rules cannot yet be proved must be identified as a fragment, not reported as
a completed implementation of G3FOPL.

## 2. Source map and existing implementation constraints

### Manuscript material used

Line references below refer to `20260926-Types-by-AI.tex`; inactive `\ifx`
alternatives and commented revisions are not competing specifications.

| Source | Implementation responsibility |
| --- | --- |
| Section 2, lines 568–766 | Programs and formulas; finite nonempty traces; overlapping trace composition; stuttering tests; finite iteration; first-order quantification over all states of a trace. |
| Section 4.1, lines 1156–1223 | Label syntax, empty label, mappings, substitution, and labelled satisfaction. |
| Tables `giiippl-regular-rules`, `giiippl-trace-rules`, `giiippl-propositional-rules`, lines 1310–1423 | Inherited regular-program, temporal, propositional, and structural rules. |
| Table `giiippl-derived-propositional-rules`, lines 1480–1516 | Diamond, disjunction, implication, and dual-suffix rules. |
| Section 4.3, lines 1520–1713 | Right-hand trace elements, trace-pair routing, progressing steps, and backlinks. |
| Section 5, lines 1715–2039; Appendix A.1, lines 2882–3093 | Execution sequences, counterexample sequences, their natural-valued measure, and the local descent argument. |
| Section 7.1, lines 2570–2632 | Explicit updates and first-order label interpretations. |
| Section 7.2 and its two rule tables, lines 2634–2721 | Assignment, atom evaluation, terminal pure sequents, universal rules, derived existential rules, and inherited G3PPL rules. |
| Section 7.3, lines 2724–2740 | Intended first-order soundness argument; completeness material is outside this implementation. |

### Existing Rocq architecture

| Reference | Reuse in LPL |
| --- | --- |
| [Cyclic/Framework.v](../Cyclic/Framework.v), `THEORY` | Supply `World`, `Judgment`, exact and backlink equality, `denote`, `tags`, and `rank : Judgment -> World -> nat -> nat`. |
| Same file, `Make.rule_instance` | Supply both `rule_theorem` and a proof-producing `rule_counter_step`; ordinary local soundness alone does not construct a rule record. |
| Same file, graph builder | Reuse `begin_build`, `run_script`, `ApplyRule`, `CloseWith`, and `AddBacklink` for explicit benchmark scripts. |
| Same file, checks and certificates | Reuse structural checking, relational checking, finite `trace_witness`, `certificate`, and `certificate_sound`. |
| [Cyclic/Relations.v](../Cyclic/Relations.v) | Reuse the existing `Stay`/`Decrease` relation algebra without modification. |
| [FirstOrder/Syntax.v](../FirstOrder/Syntax.v) | Follow its reification, occurrence metadata, equality, and substitution organization; replace its restricted DNF language and variable conventions. |
| [FirstOrder/Semantics.v](../FirstOrder/Semantics.v) | Follow its `denote`/framework interface separation; replace free-constructor values and ranked inductive predicates with arbitrary first-order models. |
| [FirstOrder/Rules.v](../FirstOrder/Rules.v) | Follow theorem-backed record construction, dependent side-condition evidence, explicit weakening/substitution, and exact backlink proofs. |
| [FirstOrder/RuleGeneration.v](../FirstOrder/RuleGeneration.v) | Follow finite scans with context prefixes/suffixes and proof-carrying successful branches. Do not copy its search scheduling or import `Automation.v`. |
| [FirstOrder/Certification.v](../FirstOrder/Certification.v) | Adapt only the checker-to-certificate reflection argument into an LPL-local module. |
| [LTL/Syntax.v](../LTL/Syntax.v), [Rules.v](../LTL/Rules.v), [Examples.v](../LTL/Examples.v) | Follow shallow propositions, semantic ranks, explicit graphs, manual witnesses, and negative certificate checks. Do not reuse its infinite Boolean traces or NNF restriction. |

The surrounding `src/ltl` and `src/firstorder` code confirms the same broad
separation between syntax, rule generation, graph construction, and checking.
Its automated strategies are outside scope.

Two framework constraints affect the implementation order:

1. `rule_counter_step` chooses **one** false premise and successor world, and
   that choice must respect **every** valid/progress pair advertised on its
   selected edge. A lemma selecting a different premise for each followed tag
   is insufficient.
2. The supplied finite witness chooses at most one tag per graph node and
   imposes its transitions on every edge into a live region. This can be more
   restrictive than the manuscript's general pathwise trace condition. Prove
   soundness for certificates accepted by this framework; do not promise that
   it accepts every manuscript preproof or modify `Cyclic/` to achieve that.

## 3. Theory decisions and implementation gates

### D1. Label juxtaposition and program-trace composition

**User clarification: interpret the label mapping by direct juxtaposition:**

```text
m(sigma1 ◇ sigma2) = m(sigma1)m(sigma2).
```

There is no endpoint-merging `·` between the two label interpretations. Direct
juxtaposition retains every state from both sequences, including repeated
boundary states, and requires no equality of their endpoints. In Rocq, realize
this juxtaposition by list append. Keep it distinct from the overlapping
program-trace composition `·` in Section 2, which matches a common endpoint
and retains that endpoint once.

For updates denoting states `s0` and `s1`, the agreed interpretation gives:

```text
m(U ◇ V)           = [s0; s1]       when m(U) = [s0], m(V) = [s1]
m(U ◇ U)           = [s0; s0]
m(U ◇ {u:=e}U)     = [s0; s0[u := eval(s0,e)]]
m(epsilon ◇ sigma) = m(sigma) = m(sigma ◇ epsilon).
```

Thus assignment labels retain both the pre-state and post-state, and test
labels retain the two-state stutter. For a nonempty tail, the interpretation
of `U ◇ sigma` has one more state than that of `sigma`, as needed by the
suffix-rule length argument. These are required regression properties.

D1 is resolved under this clarification. The earlier counterexamples assumed
an overlapping operation between label interpretations and do not apply to
the agreed mapping. Ordinary rule soundness and the complete rank-decrease
proofs are still implementation obligations.

### D2. Quantifier substitution and freshness

**User decision: `forall` and `exists` apply only to pure FOL formulas.** Use
the following quantified-body grammar, over the given first-order signature:

```text
F ::= True | False | P(t1,...,tn) | t1 = t2
    | not F | F and F | F or F | F -> F
    | forall u. F | exists u. F.
```

Program modalities `[alpha]` and `diamond alpha`, tests/program constructs,
and all temporal operators are excluded from this grammar. The exclusion
applies recursively; nested first-order quantifiers and all Boolean
connectives remain permitted. Use the same pure-FOL classification for
quantified bodies and the pure-formula recognizer at the manual proof boundary.

Examples:

- `forall u. (P(u) -> exists v. Q(u,v))` is permitted.
- `forall u. [alpha]P(u)` is rejected, even if it has no temporal operator.
- `forall u. Next(P(u))` is rejected.
- `[alpha](forall u. P(u))` and `Next(forall u. P(u))` are permitted: the
  surrounding modality or temporal operator is outside the quantified body.

Retain the manuscript's uniform-value quantifier semantics. Prove that, for
these pure bodies, trace satisfaction depends only on the first state and
coincides with ordinary FOL evaluation there. Prove the usual capture-avoiding
substitution lemmas for arbitrary terms. No frozen-value term substitution
or change to quantifier semantics is selected. The temporal and modal body
counterexamples are negative well-formedness tests for this restricted grammar.

**User decision: in `forall R` and `exists L`, the eigenvariable `v` must also
be fresh for the principal label `sigma`.** Here freshness means that `v` must
not occur in `sigma`. Both rules require

```text
v not in Vars(Gamma) union Vars(Delta) union Vars(phi) union Vars(sigma).
```

Variable collection for labels must include assignment targets and all term
variables in nested updates. Freshness for the contexts includes their labels
as well as their formulas. Prove the corresponding semantic freshness lemma
and reflect the syntactic check into the side-condition proof used by each
rule constructor.

The earlier label `{v:=0}x` with pure body `u=0` demonstrates why the additional
condition is needed: its premise labelled `v=0` is valid while its conclusion
labelled `forall u. u=0` is false in a domain with two distinct elements. Under
the adopted condition this eigenvariable choice is rejected. Retain it as a
negative rule-generation regression, rather than an unresolved theory blocker.

D2's specification decisions are resolved. The implementation must still prove
the substitution, freshness, and countermodel obligations for these rules.

### D3. Expand every double-line rule before implementation

**User decision: expand all double-line rules before implementation.** Apply
this requirement to every active inherited or first-order-specific display,
including derived rules, not only weakening.

[RULE_EXPANSIONS.md](RULE_EXPANSIONS.md) records all 14 active double-line
displays as 24 explicit left/right sequent schemes, with contexts, ordered
premises, FOPL specializations, and implementation obligations. The inherited
propositional atom pair is documented for coverage and replaced by the
first-order `(at)` pair in the implementation.

The expansion of weakening explicitly retains the context-only premise:

```text
Gamma => Delta                   Gamma => Delta
--------------------- Wk.L       --------------------- Wk.R
Gamma, sigma:A => Delta           Gamma => sigma:A, Delta
```

An empty replacement at the principal-formula position leaves a premise
sequent containing the contexts; weakening is not a zero-premise axiom.
The catalog also preserves the manuscript's two-premise left box-choice and
box-star rules. Already-sequent-shaped test displays are written out directly,
without wrapping them as formulas or assuming reverse inference directions.

The expansion stage is complete for the current active double-line displays.
Implement each supported explicit scheme as its own named rule constructor
and generator case only after proving its semantic and trace obligations.
New shorthand rules must be expanded in the catalog before implementation.
The expanded schemes use the direct-juxtaposition label semantics agreed in D1.

### D4. Empty labels and assertion admissibility

**User decision: require every label used in an assertion to have a defined,
nonempty interpretation, with explicit admissibility conditions in the
semantics and rules.** The empty label remains available as the juxtaposition
unit, but does not by itself label a formula to be evaluated on an empty trace.

Under D1's clarified mapping, define total label evaluation `eval_label w sigma`
on well-formed syntax. The empty label denotes the empty sequence, updates
denote singleton traces, trace variables denote finite nonempty traces, and
`◇` directly juxtaposes its operands by list append. Prove the unit and length
laws. If a relational interface is useful, define `label_eval w sigma tr` as
`eval_label w sigma = tr`, with immediate totality and uniqueness lemmas.
There is no endpoint compatibility condition for label evaluation. Overlapping
program-trace composition remains a separate semantic operation.

Define `label_admissible w sigma` to mean that `sigma` evaluates to a nonempty
trace. Define `admissible j w` to require that property for every labelled
occurrence on both sides of `j`. Thus `epsilon ◇ U` and `U ◇ epsilon` can label
assertions, while `epsilon` alone cannot. Labels whose successive components
denote different states remain admissible whenever their complete interpretation
is nonempty.

Use the explicitly guarded denotation in Section 5. Validity asserts the
sequent implication only at admissible mappings. Do not supply a default state
for an empty interpretation. A theorem about a particular mapping must supply
admissibility; benchmark success must not rely solely on having no admissible
mappings. Definedness is automatic for well-formed labels under D1; the
remaining assertion-admissibility condition is nonemptiness.

For every rule, prove that the premise mappings used in its soundness proof
are admissible. In particular, `rule_counter_step` must construct an admissible
false premise from an admissible false conclusion, together with the required
rank inequalities. Rules introducing labels, including cut and substitution,
must prove the needed new-label admissibility instead of discharging a premise
through a false admissibility guard. Because updates and trace variables have
nonempty interpretations, prove that complete-label nonemptiness is checked
structurally: false for `epsilon`, true for an update or trace variable, and
the Boolean disjunction of the two checks for `◇`. No semantic-state equality
test is needed for labels.

D4 is resolved and retains the approved nonempty-assertion convention. D1's
clarification removes the earlier undefined-label-join concern.

### Implementation proof obligations

These are proof milestones, not assumed manuscript theorems:

- Prove the exact substitution/coincidence lemmas for assignments, tests,
  formulas, updates, and both sorts of label variables. Substitution must
  respect quantifier binding and variables modified inside programs.
- Keep the manuscript's stuttering test and star-zero conventions: a test
  produces `ss`, and `alpha^0` is `true?`. Do not import identity-trace or
  standard infinite-LTL laws that would erase those observations.
- Define the active manuscript's counterexample sets and its measure, the
  **sum of the lengths of component traces**, rather than a commented-out
  multiset alternative or merely the number of execution steps.
- Establish nonempty counterexample sets for false trace elements, well-defined
  minima, and each required nonincrease/decrease inequality. Do not assume
  there are finitely many program executions, or search for semantic minima.
- For the first suffix-right premise the recursive suffix formula is absent;
  no continuing principal tag exists on that edge. Advertise a progressing
  principal pair only on a premise containing its actual continuation.
- Follow the explicit schemas in `RULE_EXPANSIONS.md` before constructing rule
  records. Preserve their left/right contexts and branching; in particular,
  the two-premise left box-choice rule is not a one-premise antecedent rewrite.

If a proof fails, isolate the exact statement or give a counterexample and
interact with the user. Do not replace it with an axiom, an admitted lemma, a
zero rank, or an unannounced restriction and call the full theory implemented.

## 4. Proposed file and dependency structure

All new theory code lives in `LPL/`. Names below are planned deliverables, not
files already implemented.

| File | Responsibility and dependencies |
| --- | --- |
| `Signature.v` | Finitary single-sorted function/predicate symbols, arities, and decidable syntactic symbol equality. No semantic interpretation. |
| `Syntax.v` | Signature-parametric terms, pure-FOL grammar and recognition, LPL formulas/programs, pure-FOL-only quantified bodies, updates, labels, tagged occurrences, judgments, equality, variable collection, and capture-avoiding syntactic operations. Imports `Signature`. |
| `Semantics.v` | Arbitrary nonempty domains and models; term/update evaluation; finite traces; total label evaluation by direct juxtaposition; separate overlapping program-trace composition; program and formula semantics; label/judgment admissibility and guarded shallow denotation. Imports `Syntax`. |
| `Progress.v` | Counterexample witnesses and minima, occurrence ranks, semantic preservation/decrease lemmas, `LPLTheory <: Framework.THEORY`, and `Framework.Make LPLTheory`. Imports `Semantics` and unchanged `Cyclic/Framework`. |
| `Rules.v` | Ordinary semantic theorems and packaged axioms/rules with trace obligations, structural rules, pure terminal bridge, and exact/tag-renaming backlinks. Imports `Progress`. |
| `RuleGeneration.v` | Verified local generators and explicit requests for parameterized rules. Imports `Rules`; does not search graphs. |
| `Certification.v` | LPL-local checker reflection and final soundness wrapper. Imports `Rules`; no search or witness generation. |
| `Benchmarks/Support.v` | Small signature/model instances, notations, and reusable semantic lemmas proved with the standard library. |
| `Benchmarks/*.v` | Individually timed manual proof/certificate examples and rule/checker regressions. |
| `BENCHMARK_RESULTS.md` | Commands, timings, coverage, assumptions, timeouts, simplified cases, and omissions, generated during implementation. |

The existing [RULE_EXPANSIONS.md](RULE_EXPANSIONS.md) is the specification
prerequisite for the covered rule constructors and their generator branches.

Keep `Signature.v` and `Syntax.v` independent of meanings in `Prop`. Put all
semantic evaluation in `Semantics.v`; the fact that the existing LTL file
combines these responsibilities is not a reason to combine them here.

The implementation is parameterized by a signature and a model. For each model,
the framework world carries the world-variable mapping and trace-variable
mapping required to interpret labels. Rule and soundness theorems remain
parametric in the model. There is no need to compare semantic functions or
Rocq propositions when comparing judgments.

## 5. Syntax and semantic design

### General first-order layer

Use separate numeric namespaces for program/first-order variables,
world-label variables, trace-label variables, and proof-occurrence tags.
Bound and free first-order variables must be distinguished by binding and
capture-avoiding substitution, not by FirstOrder's free/existential variable
classes. Named binders with proved fresh renaming are a suitable initial
representation.

A signature supports arbitrary finitary function and predicate symbols with
their specified arities. Constants are zero-arity function symbols, not a
mandatory family of natural-number constructors. Enforce arities through an
arity-indexed argument representation or checked well-formedness; malformed
applications must never acquire a rule instance. Fix this routine
representation choice in the first implementation milestone.

A semantic model supplies an arbitrary nonempty carrier, function
interpretations, and predicate interpretations into `Prop`. Its carrier need
not have decidable equality, and predicates need not be decidable or
inductively defined. Built-in equality is semantic equality of evaluated
terms. In particular, do not assume function injectivity, disjoint constructor
ranges, integer arithmetic, or inductive predicate ranks.

### Programs, formulas, and labels

Represent assignments, tests, sequence, choice, and star. Define programs and
formulas mutually where test guards and modalities require this. Retain the
manuscript's test evaluation on `ss`; a test guard is not silently restricted
to an atomic or pure arithmetic formula.

Expose truth, falsehood, atoms/equality, all four Boolean connectives, `forall`,
`exists`, first-state, suffix, and box in the user-facing syntax. Disjunction,
implication, existential quantification, diamond, and dual suffix may be
definitions in terms of the primitive constructors, with unfolding lemmas and
their own public rule constructors. Preserve nesting subject to D2: the body
of each `forall` or `exists` must be pure FOL, with no program modality or
temporal operator anywhere inside it. Enforce this through the syntax types
or a proved well-formedness predicate with executable reflection. Substitution and derived
constructor expansion must preserve this invariant. Do not force formulas into
DNF or NNF.

Updates have the manuscript shape `Base x` and `AssignUpdate u e U`. The new
assignment evaluates `e` in the state already denoted by `U`, then changes `u`.
For example, two successive increments read the value after the first
increment. Updates describe states; storing only the final update does not
replace the trace of intermediate label components.

Labels contain empty, update, trace variable, and binary juxtaposition.
Interpretation follows D1 and D4. Preserve the distinction between a singleton
state trace, a stuttering two-state trace, and an empty label. Evaluate `◇`
by direct juxtaposition, retaining both boundary states. No endpoint equality
is required for labels; keep the shared-endpoint relation for composing program
execution traces separate.
The empty label may occur as a component using the unit laws; every complete
label used to assert a formula must evaluate to a nonempty trace. Prove the
structural nonemptiness check from D4 sound and complete.

Define temporal operators on finite traces. As useful abbreviations,
`Next A := false suffix A`, `Eventually A := A or (true suffix A)`, and
`Always A := not Eventually(not A)` follow the manuscript's suffix semantics.
Prove their boundary laws before using them in benchmarks. Existing LTL's
infinite-trace definitions do not apply.

### Judgments and denotation

A judgment contains finite antecedent and succedent lists of labelled
occurrences. Lists preserve exact graph labels; exchange/weakening handles
their set-like logical behavior. Tags are metadata and do not affect truth.

Under D4, interpret a labelled formula only through a defined nonempty trace
and guard the sequent implication by judgment admissibility:

```text
eval_label w epsilon := [].
eval_label w U := [eval_update w U].
eval_label w X := trace_mapping w X.
eval_label w (sigma1 ◇ sigma2) :=
  eval_label w sigma1 ++ eval_label w sigma2.

label_eval w sigma tr := eval_label w sigma = tr.

label_admissible w sigma :=
  exists tr, label_eval w sigma tr /\ tr <> [].

labelled_holds w (sigma:A) :=
  exists tr, label_eval w sigma tr /\ tr <> [] /\ formula_holds tr A.

admissible (Gamma => Delta) w :=
  every occurrence in Gamma and Delta has an admissible label at w.

denote (Gamma => Delta) w :=
  admissible (Gamma => Delta) w ->
  ((every labelled formula of Gamma holds at w) ->
   (some labelled formula of Delta holds at w)).
```

The empty antecedent denotes `True`, and the empty succedent denotes `False`.
`Cyclic.Valid j` therefore means the sequent implication holds at every
admissible mapping. This is validity relative to the stated domain of label
interpretation, not an assertion of formula truth at empty labels. Label
evaluation is total on well-formed syntax. Prove the equivalence between this
guarded definition and validity over admissible worlds. For a concrete benchmark
root, exhibit an admissible
mapping or another proved nonvacuity witness; inconsistent admissibility
assumptions do not count as a successful logical benchmark.

Keep admissibility explicit in ordinary rule theorems. From `~ denote j w`,
prove `admissible j w` and extract the ordinary false-sequent conditions;
construct the target admissibility required by each countermodel step.

Prove sound exact equality and equality ignoring only occurrence tags.
Backlink comparison must not silently identify different labels, update
histories, formulas, or program variables.

### Pure first-order boundary

Provide a syntactic pure-formula recognizer for D2's pure-FOL grammar, excluding
program modalities and temporal operators, and prove its connection to ordinary
first-order truth at a singleton update. Introduce a terminal constructor requiring both the
recognized pure shape and a caller-supplied Rocq proof of its shallow semantic
obligation. The manuscript's atom-only terminal rule is the required baseline;
any extension to compound pure leaves must be a separately proved consequence.

Typical leaf proofs use `intros`, `cbn`, `assumption`, `reflexivity`, `auto`,
`tauto`, `firstorder`, `congruence`, or standard-library arithmetic tactics
such as `lia` where appropriate. The standard `firstorder` tactic is distinct
from importing the project's `FirstOrder` theory. Generators must not decide
arbitrary predicate truth or synthesize these proof terms.

When a goal has reached the pure terminal shape, local generation stops and
returns control to this manual proof boundary. The presence of generic
Boolean/quantifier rule constructors must not become an automatic pure-FOL
derivation procedure.

## 6. Progress and rule-instance obligations

Tag traceable **succedent occurrences**, as the manuscript requires: box,
suffix, and dual-suffix formulas. Do not transfer FirstOrder's antecedent
inductive-predicate tagging or LTL's always/next-always whitelist.

Maintain unique tags within a judgment and map each tag unambiguously to its
occurrence. Prove the Boolean tag/well-formedness checks used by generators.
The framework checks endpoints and progress inclusion, but it does not supply
these object-logic invariants automatically.

For false trace elements, the intended rank is the manuscript's minimum
counterexample-sequence measure. Give the total `nat` rank a documented
fallback on true formulas, absent tags, or inadmissible mappings; prove that
fallback is irrelevant to countermodel obligations. The rank is a mathematical
function, possibly using standard classical choice, not an executable program
evaluator.

Before scaling up the rule library, prove:

1. Existence and specification of counterexample witnesses/minima.
2. Preservation under unchanged contexts, tag renaming, and label substitution.
3. Nonincrease for sequence, choice, and star unfolding on the selected false
   premise; premise selection must respect the entire advertised edge.
4. Strict decrease for continuing right-assignment, right-test, suffix-right,
   and dual-suffix-right trace pairs, only when actually justified by the
   chosen semantics. Use D1's retention of both assignment/test states and
   strict prefix-length increase under label juxtaposition.

Prove ordinary rule theorems first, then construct records with these fields:

```text
rule_name, rule_conclusion, rule_premises,
rule_theorem, rule_counter_step
```

Each premise stores its judgment and edge information. Preserved occurrences
receive rank-preserving pairs only when proved; transformed principal
occurrences receive the appropriate proved continuation. `edge_progress` is
a subset of `edge_valid`. Neither star unfolding nor a backlink is progress
merely because it participates in a loop.

### Required rule coverage

| Family | Planned public instances | Trace treatment |
| --- | --- | --- |
| Axioms | Identity; truth-right/false-left as standard consequences; singleton suffix-left falsity. | Terminal leaves; no fabricated successors. |
| Assignment | Box assignment on both sides; diamond assignment derived by duality. | Only proved right-box principal continuations may claim assignment progress. |
| Tests | Box-test right and left, and the manuscript's corresponding derived forms. | Preserve `ss`; prove guard obligations; progress only on justified right principal pairs. |
| Regular programs | Sequence, choice, star, on both sides; corresponding diamond rules. | Nonprogressing unfolding; retain exact premise lists of each public rule. |
| Trace formulas | Atom-at-head, first-state, suffix right/left, singleton suffix closure, dual-suffix right/left. | Only continuing right suffix/dual-suffix pairs may progress. |
| Boolean formulas | Negation, conjunction, disjunction, implication, both left and right. | Preserve unaffected succedent tags; do not route tags across a negation side change without a separate justification. |
| Quantifiers | Universal right/left and derived existential right/left, only for pure-FOL bodies; eigenvariables of universal-right/existential-left are fresh for the principal label as well as the contexts and body. | Enforce both D2 conditions and prove substitution, freshness, and context-rank preservation first. |
| Structural | Label substitution, one-premise Wk.L/Wk.R expanded under D3, exchange and any list-contraction helpers; the manuscript's cut rule with its two contexts. | Preserve only proved context continuations; newly introduced cut formulas do not inherit a principal trace. |
| Pure terminal | Evidence-backed atom-only pure sequent closure; optional proved compound-pure extension. | `axiom_instance`, supplied by a manual pure proof. |
| Backlinks | Exact repeated judgment, then exact logical content up to explicit tag renaming. | Nonprogressing pairs with a rank-preservation theorem. |

For label substitution, distinguish world-variable-to-update substitution
from trace-variable-to-label substitution and prove their mapping lemmas.
Do not substitute an arbitrary trace for the base world of an update.
The manuscript's inheritance of substitution must respect those sorts.

## 7. Rule generation without proof search

Expose a small interface, with exact names settled during implementation:

```text
generate_axiom     : judgment -> option axiom_instance
generate_rules     : judgment -> list rule_instance
generate_requested: judgment -> rule_request -> option rule_instance
close_pure        : pure-shape evidence -> pure-obligation proof -> axiom_instance
```

`generate_axiom` checks structural closing shapes. `generate_rules` enumerates
applicable local syntax-directed rules at all eligible positions, retaining
context order. Every returned value is built from an already-proved rule
constructor. Successful Boolean checks supply their reflected side-condition
proofs; failed checks return no candidate.

For every formerly double-line display, generate only the explicit schemes
listed in `RULE_EXPANSIONS.md`. Match their exact ordered premise lists and
contexts. In particular, Wk.L/Wk.R each produce one context-only premise and
must not appear in `generate_axiom`.

Reject quantifier-rule requests whose bodies violate D2: a program modality
or temporal operator anywhere inside the body is disallowed. Use the pure-FOL
recognizer for this check, including when no temporal operator is present.
Do not apply a quantifier rule to malformed syntax merely because its outer constructor has
the expected name. All successful requests preserve the quantified-body
well-formedness invariant.

Reject syntactically empty complete assertion labels under D4, allowing empty
components whose unit laws yield a nonempty complete label. Use the proved
structural nonemptiness check; do not impose endpoint matching on labels.
A generated rule must discharge the required admissibility-transfer proof
using proved constructors and justified side conditions; otherwise return no
candidate or leave the corresponding explicit constructor unavailable until
proved.

`generate_requested` handles user choices that cannot be completely enumerated:
quantifier terms, label substitutions, cut formulas/context partitions,
selected weakening occurrences, and a specified backlink source/target.
The generator checks a concrete request; it does not guess terms, cuts,
substitutions, or companion nodes. Fresh eigenvariables/tags can be selected
deterministically by a finite syntax scan. For `forall R` and `exists L`, scan
the principal label and its nested updates as well as the contexts and body;
reject an explicitly requested eigenvariable that violates D2's freshness
condition.

Prove that generated rule/axiom conclusions equal the input judgment, that
successful requests satisfy their side conditions, and that all returned
edges are well formed. Unsupported or inadmissible requests must fail
explicitly; failure means only that no requested verified instance was
generated, not that the goal is false.

Do not implement a driver repeatedly selecting candidates, graph search,
normalization search, unification, tactic dispatch, or witness search. Manual
benchmarks choose the instance and the next node explicitly. Rule-generation
coverage and search completeness are different requirements.

## 8. Certification and soundness

Adapt the model-independent structural reflection argument from
`FirstOrder/Certification.v` locally, using LPL's own equality lemmas and
`rule_counter_step` records. Avoid copying unrelated FO model reasoning.

The public endpoint is:

```text
raw_check graph witness = true -> Valid (graph_root graph)
```

Construct the framework's semantic `certificate`, including root consistency,
false-node liveness, countermodel advancement, and witness transitions, then
apply the unchanged `certificate_sound`. A successful relational check by
itself is not this theorem.

Benchmarks manually provide both the graph script and finite tag/potential
witness. Keep the witness restriction documented, and report any otherwise
plausible graph rejected by it. No completeness result or automatic
certificate/witness discovery is required.

Use only proved lemmas and explicitly reported standard-library classical
principles. `Print Assumptions` on representative rules and exported benchmark
theorems must reveal no project-defined soundness axioms or admitted proofs.

## 9. Implementation order and acceptance gates

| Stage | Work | Exit criterion |
| --- | --- | --- |
| 0. Agreed specification and baseline | Follow D1's direct-juxtaposition label mapping, both D2 restrictions, D3's explicit expansion catalog, and D4's nonempty-label admissibility convention; record compiler/build baseline and hashes of unchanged modules. | All planning decisions are recorded and the exact target is explicit. |
| 1. General syntax | Implement signature interface, terms, binders, pure-FOL grammar, LPL programs/formulas, updates, labels, sequents, equality, and well-formedness, including D2. | Two distinct signatures instantiate; all Boolean connectives and both quantifiers over pure FOL are representable; malformed arities and quantified bodies containing program modalities or temporal operators are rejected. |
| 2. Agreed semantics | Define arbitrary models, finite-trace relations, total label evaluation by juxtaposition, separate overlapping program-trace composition, D4 admissibility, guarded denotation, and pure-leaf correspondence. | Prove label unit/length laws, structural nonemptiness reflection, admissible-world validity equivalence, and false-sequent extraction. Check singleton/stuttering/empty cases, assignments, tests, finite star, and quantifier substitution against the manuscript and decisions. |
| 3. Progress feasibility | Define counterexample ranks and framework adapter; attempt the exact local descent obligations. | Proved interface for supported trace pairs, or an explicit blocker requiring user interaction. Do not proceed as though blocked cyclic rules were available. |
| 4. Rule kernels | Use D3's explicit schemas and D4's admissibility conditions, prove ordinary theorems, then construct records for every unblocked row in the rule matrix. | Every supported left/right scheme has the specified premises, admissibility transfer, and both framework proofs; missing families are identified. Full-theory completion requires all requested families. |
| 5. Local generation | Implement axiom scans, finite rule scans, explicit requests, and conclusion/side-condition guarantees against the expansion catalog. | Positive and negative requests cover each implemented rule family, exact premise counts/contexts, and arbitrary positions; weakening never becomes a zero-premise closure. |
| 6. Certification | Adapt checker reflection; build one manual acyclic certificate and one small genuinely cyclic certificate. | Their validity follows through `certificate_sound`; malformed and nonprogressing graphs are rejected. This stage depends on the proved local progress obligations. |
| 7. Benchmarks | Add the matrix below, one timed compilation unit per benchmark or equivalently isolated goal. | Coverage, pure-proof limitations, timings, assumptions, and any simplified/abandoned case are recorded. |
| 8. Integration | Add only required entries/dependencies in `_CoqProject` and `Makefile`, plus concise LPL usage/build documentation. | Available regression builds pass, `Cyclic/` hashes match, no forbidden dependencies or automation are introduced. |

Independent signature/syntax and source-audit work can proceed while a semantic
proof is being developed. Passing those stages does not replace the semantic
and trace proofs required by every rule record.

## 10. Benchmark and verification matrix

Each positive logical benchmark exports a semantic validity theorem. Include
end-to-end proofs through generated instances and manual graph certificates,
not only direct semantic proofs or kernel rule lemmas. Auxiliary semantic
examples verify that the definitions distinguish the relevant trace cases.

| Benchmark group | Examples and required evidence |
| --- | --- |
| Arbitrary signatures/models | A symbolic signature with noninductive predicates and a separate Boolean or integer instance; no constructor injectivity or decidable predicate truth is assumed. |
| Label admissibility | Empty-unit components and singleton labels; reject an empty complete assertion label. Juxtapose singleton labels denoting different states without requiring a shared endpoint, and retain two states when both singleton labels denote the same state. Check the separate endpoint condition for program-trace composition. Supply admissibility for concrete theorem applications and a nonvacuity witness for each positive benchmark root. |
| Booleans and quantifiers | Each Boolean connective on both sides in mixed LPL formulas; nested/shadowed quantifiers over pure FOL; capture avoidance; admissible and rejected instantiation/freshness cases under D2. Accept modalities/temporal operators outside a permitted quantified formula; reject either inside its body, including temporal-free modal bodies. Pure-only goals go through the manual terminal bridge. |
| Updates | Identity assignment, assignment changing a value, two dependent assignments, and assignments to different variables; verify update evaluation order and preservation of every intermediate label state under D1. |
| Tests | Successful and failed pure tests; a trace-sensitive test distinguishes `s` from `ss`. Verify guards at the manuscript's specified trace. |
| Sequence and choice | A two-assignment sequence; nondeterministic branches; nested sequence/choice; both antecedent and succedent rule forms. |
| Star | Zero-iteration stutter, one iteration, and nested iteration; distinguish finite star traces from infinite executions. |
| Temporal operators | First-state with a compound body; suffix immediate and postponed cases; singleton failure; dual suffix; next at the end of a finite trace. |
| Structural rules | Non-head rule positions, exchange, both one-premise weakening expansions, cut, sorted label substitutions, and tag-renaming backlinks with explicit mappings. Check every expanded double-line family's exact left/right premise shapes. |
| Cyclic proof | After the progress gates pass, manually build a star invariant proof with a real backlink and explicit tag/potential witness; an acyclic unrolling is not a substitute. |
| Complex programs | A guarded counter loop with invariant `counter >= 0` at every visited state, and a nested sequence/choice/star program preserving an uninterpreted predicate of an unchanged variable. Pure obligations must remain solvable by standard tactics. |
| Negative semantics | No unsound constructor injectivity; failed-test box vacuity versus failed-test diamond falsity; label juxtaposition must not collapse a two-state stutter or reject successive different states. D2's temporal-body and temporal-free modal-body examples are rejected syntax, and its `{v:=0}x` eigenvariable example is rejected by the adopted freshness condition. |
| Negative generators/checker | Generators reject wrong shapes/positions, empty complete assertion labels, inadmissible substitutions, stale eigenvariables, and duplicate/invalid occurrence tags. Nonempty labels are checked structurally; differing endpoint states are not grounds for rejecting a label. Graph checks reject mismatched rule conclusions, open/dangling nodes, wrong companions, malformed edge tags, and a closed nonprogressing cycle. Use structurally buildable negative graphs with proved local records; do not attribute object-level tag-uniqueness checking to the generic framework. |

The star/loop claims must account for arbitrary finite stopping points. Do not
claim every star execution reaches a loop exit, or use an initial-state atom
as a substitute for a property of all visited states.

Trace-dependent positive cases require the corresponding semantic and progress
proofs. If an unexpected proof obstruction appears, identify the exact rule
and obtain user direction before changing the agreed semantics. Do not silently
replace a required cyclic benchmark with an unrelated acyclic example.

### Ten-minute limit

Compile common dependencies first, then run each isolated benchmark from
`Rocq-copy/` with a hard limit, for example:

```sh
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/AssignmentChange.v
```

Record the actual command, elapsed time, exit status, rule coverage, graph
size/tags where applicable, and theorem assumptions. On timeout, simplify the
case or abandon it with a recorded reason. Do not increase the limit or retry
the same expensive obligation indefinitely. Keep checker examples small:
the unchanged framework's relation fuel grows as `3^(number_of_tags^2)`.

For an unsolved pure obligation, try only standard Rocq tactics, then simplify
or omit the benchmark. No solver integration or new first-order automation is
part of the fallback.

### Integration checks and current environment

- The installed compiler reports Rocq 9.1.0, matching the existing development.
- During planning, `git status --short` failed because object
  `44/76ef7404bc15d46e261deac6db61f533ce72c8` is empty and `HEAD` is unreadable.
  Do not repair or mutate `.git` as part of this work. Use file comparisons and
  checksums to verify scope until repository metadata is repaired separately.
- Initial SHA-256 values for the immutable framework sources are:

  ```text
  Cyclic/Framework.v  b9f93e89931a196bb1d2f7649f240cb65920ed972fa02a2ae4af46a2e7a3ce02
  Cyclic/Relations.v  85f1f25747e3eb661f24f50b6a9e6aae3cbcb173169bb7bfb6d06ac7addeb90f
  ```

- Add LPL build dependencies explicitly; the existing Makefile enumerates
  files and dependencies rather than discovering new `.v` files automatically.
- Compile existing LTL and FirstOrder regressions where feasible and report
  baseline failures separately. This planning task has not run those builds.
- Check imports, exported assumptions, generated instances, benchmark results,
  and framework hashes. Do not use deletion-based cleanup; preserve existing
  source and generated files in accordance with the workspace instructions.

## 11. Definition of completion

The requested implementation is complete only when the agreed semantics,
explicit label-admissibility conditions, and all requested rule families are
realized without admitted proofs; local generation returns verified instances;
manual cyclic certificates establish
nontrivial examples using the unchanged framework; the benchmark matrix and
time limits are satisfied; and all unresolved or omitted cases are accurately
reported.

If a required soundness proof cannot be completed, report the exact remaining
obligation and seek user direction before changing the agreed theory. A partial
formalization must not be reported as the completed implementation.
