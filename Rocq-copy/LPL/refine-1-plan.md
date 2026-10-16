# Refinement plan: general G3PPL with G3FOPL as an instance

Status: **planning only; implementation and new benchmark runs have not begun**.
Prepared on 2026-10-17 from [refine-1-draft.md](refine-1-draft.md).

The goal is to factor the existing first-order development into a reusable
G3PPL theory, then reconstruct the same G3FOPL theory through instantiation
and first-order extensions. Common syntax, semantics, progress arguments,
rules, generators, and certification must have one production implementation.
The first-order language and its existing results must retain their meaning.

## 1. Scope and controlling requirements

1. All changes, generated files, logs, and build artifacts belong under
   `Rocq-copy/LPL/`. Keep **every file outside that directory unchanged**,
   including `LPL-old/`, `Cyclic/`, the parent `Makefile`, `_CoqProject`,
   `FirstOrder/`, and `LTL/`. Do not repair or modify repository metadata.
2. Treat [LPL-old](../LPL-old/) as the immutable reference for G3FOPL.
   Put all migrated first-order implementation and benchmark `.v` files in
   `FOPL/`. Root theory files become the general implementation.
3. Follow the active definitions and rule displays in
   [the manuscript](Theory/20260926-Types-by-AI.tex), checking the
   [PDF](Theory/20260926-Types-by-AI.pdf) when a display is ambiguous.
   Inactive alternatives and comments are not replacement specifications.
4. Retain the approved D1–D4 decisions in
   [IMPLEMENTATION_PLAN.md](IMPLEMENTATION_PLAN.md): append-based labels,
   pure-FOL quantifier bodies and label-aware eigenvariable freshness,
   explicit double-line expansions, and nonempty asserted labels.
   Record any conflict with the literal manuscript; do not silently change
   either the approved FOPL semantics or a manuscript rule.
5. Keep reified syntax separate from shallow semantics in `Prop`. Continue
   using the unchanged cyclic framework and its proof-carrying rule records.
6. Implement local rule generation only. No proof search, solver integration,
   custom search tactics, automatic backlink/witness discovery, completeness
   proof, or imports of the FirstOrder/LTL object theories are required.
   Do not consult `FirstOrderNew/`.
7. Use Rocq's standard library. Retain manual proofs at the pure-FOL boundary.
   Preserve learner-oriented explanations when reorganizing the source.
8. Rerun all existing G3FOPL benchmarks and add G3PPL benchmarks. Every
   isolated benchmark compilation has a hard **600-second** limit.
9. Preserve files when reorganizing; do not use deletion-based cleanup.
   Do not overwrite colliding destination files without inspecting them.

This document supplements the original implementation plan. Its stricter
write scope supersedes the old plan's permission to edit parent build files.
The draft's implementation order is understood as general G3PPL first,
followed by the G3FOPL instance and both benchmark suites.

## 2. Inspected baseline and source map

The inspection found Rocq **9.1.0**, compiled with OCaml 4.14.1. The current
`LPL/` contains 230 files and `LPL-old/` contains 229: every corresponding
file is byte-identical; only `refine-1-draft.md` is additional in `LPL/`.
These counts precede the addition of this plan.

The seven current core sources total 5,492 lines. Despite its directory name,
the current implementation is G3FOPL: `MakeSyntax` directly contains terms,
predicate/equality formulas, quantifiers, assignments, and update labels.
Its judgment contains only two lists of labelled formulas; relational atoms
such as `x R_a y` are absent. Parameterizing only its existing first-order
signature will therefore not produce the requested general G3PPL theory.

The recorded run `20261016T172216122771Z` reports **15/15** passing benchmark
units, 50 exact rule/request premise-shape checks, an 11-node cyclic proof,
and a 12-node cyclic proof with tag renaming. These are historical results,
not fresh verification performed while preparing this plan. The two complex
all-visited-state invariants are direct semantic proofs; the cyclic proofs
preserve a first-state observation. Preserve this distinction.

| Source | Responsibility in the refinement |
| --- | --- |
| Manuscript §2.1, approximately lines 577–652 | Atomic actions/propositions, arbitrary frames, length-two atomic executions, regular programs, finite traces, and temporal meanings. |
| Manuscript §4.1, lines 1156–1223 | World/trace label sorts, label mappings, relations, and labelled satisfaction. |
| Tables `giiippl-regular-rules`, `giiippl-trace-rules`, `giiippl-propositional-rules`, `giiippl-derived-propositional-rules` | Primitive and derived G3PPL rule families, including the four atomic-action box/diamond rules currently missing. |
| Manuscript §4.3, §5, Appendix A.1 | Succedent trace elements, progress, execution histories, counterexample minima, and descent. |
| Manuscript §7.1–§7.3 | Update labels and the first-order specialization, assignment rules, pure terminals, and quantifiers. |
| `LPL-old/{Signature,Syntax,Semantics}.v` | Exact legacy first-order language, well-formedness, arbitrary-model semantics, and approved D1–D4 behavior. |
| `LPL-old/{Progress,Rules,RuleGeneration,Certification}.v` | Proven rank arguments, rule packaging, local generation, shared-kernel discipline, and checker reflection to preserve/factor. |
| [RULE_EXPANSIONS.md](RULE_EXPANSIONS.md) | Existing 14 double-line displays expanded into 24 schemes, including currently replaced propositional atom rules. |
| `LPL-old/Benchmarks/`, benchmark reports, and validation logs | Regression statements, scripts, witnesses, negative cases, assumptions, and historical timings. |
| `Cyclic/{Framework,Relations}.v` | Unchanged framework contracts and relation algebra. |

## 3. Architecture: shared theory and explicit extension points

### 3.1 Generic vocabulary

Replace the first-order-only root signature with interfaces for the following
independent syntactic components. Require decidable equality for reified
syntax, never for semantic states or predicate truth.

| Component | General G3PPL responsibility | G3FOPL instantiation |
| --- | --- | --- |
| Atomic programs | An arbitrary action type, equality, and any syntactic validity check. | Assignment payload `(program variable, term)`. |
| Atomic formulas | An arbitrary proposition payload type, equality, and validity check. | Predicate applications and term equality. |
| World-denoting label terms | A type of singleton-state expressions, world-name support, substitution, and equality. | Existing `Base`/`AssignUpdate` update syntax. |
| World and trace names | Separate name sorts, equality, finite support, and a fresh-name operation with its specification. Natural-number defaults suffice for the existing instance. | Existing natural-number names, kept distinct from program variables. |
| Label relations | A parameterized reified relation vocabulary, argument checks, support/substitution operations, and a distinguished action-relation view. | Assignment transition relations over states denoted by update labels. |
| Formula extensions | A strictly positive extension point for operators with recursive formula children. The plain PPL instance has no extra operators. | Universal/existential binder payloads, with the existing pure-body restriction. |

World labels cannot be restricted to bare names: inherited temporal and test
rules must also work with FOPL update expressions. Conversely, the core must
not require an arithmetic domain, terms, assignment, or quantifiers.

Use a small, checked extension mechanism. A concrete starting design is a
unary `Extension operator body` constructor with abstract operator payloads;
FOPL represents `All x body` and `Ex x body` using two binder payload forms.
Expose the old names as definitions/notations and adapt pattern matches in
the FOPL layer. Do not encode a quantified formula as an opaque atomic
proposition: its body must still admit substitution, freshness checks,
well-formedness reflection, and quantifier-rule generation.

The initial architecture milestone must check positivity, structural recursion,
computable equality, and module sharing in Rocq before porting large proofs.
If this proposed extension representation fails those checks, report the
obstruction and propose another representation that preserves the same
language. A change to mathematical meaning requires a user decision.

### 3.2 Shared syntax and relational judgments

The core owns the common Boolean and temporal constructors and the mutually
defined regular-program constructors:

```text
program = Atomic action | Test formula | Seq program program
        | Choice program program | Star program
formula = Truth | Falsity | Atom proposition
        | Neg formula | Conj formula formula | Disj formula formula
        | Impl formula formula | First formula
        | Suffix formula formula | DualSuffix formula formula
        | Box program formula | Diamond program formula
        | Extension operator formula
label   = Empty | StateLabel world_term | TraceLabel trace_name
        | Join label label
judgment = relation_context ; labelled_antecedent => labelled_succedent
```

Keep relation atoms explicit in the judgment rather than hiding them in
formula atoms. A separate antecedent relation list gives the manuscript's
relational assumptions a direct representation. Context-preserving rules
carry that list unchanged; atomic-action rules introduce or consume the
specified relation. Relations receive no cyclic occurrence tags.

The canonical action-relation view must express `x R_a y` and have a proved
semantic correspondence with the action interpretation. Permit custom
relation vocabulary through the interface, subject to explicit interpretation
and substitution laws. Do not assume arbitrary user relations describe
action execution merely because their constructors have matching names.

The manuscript also mentions trace-variable relation endpoints. Represent
those cases explicitly, or via a checked endpoint view, with their actual
trace interpretation. For length-two atomic executions, the two nonempty
endpoint traces must each be singletons. Do not silently use the head or
last state of a longer trace. Extend substitution to relational endpoints;
report any unresolved endpoint-sorting issue before claiming full coverage.

Preserve exact context order, occurrence tags, and explicit label algebra.
Generalize reflected well-formedness and backlink equality to include the
relation context. Backlinks may ignore justified tag changes only; differing
relations cannot be ignored. Use separate support collections for world
names, trace names, and FOPL program variables.

The common reified grammar can be more convenient than the manuscript's
separate state/trace grammar. Document the canonical PPL view and derived
operators, and preserve the legacy FOPL recognizers exactly. Any newly
proposed restriction on accepted FOPL syntax requires user approval.

### 3.3 Shared semantics

A generic frame supplies a nonempty state type, an arbitrary relation
`action_step a s t : Prop`, and `atom_holds p s : Prop`. Atomic program runs
are exactly `[s;t]` satisfying that relation. No determinism, finite state
space, decidable state equality, or decidable semantic relation is required.

A label interpretation supplies world/trace mappings and evaluates a
world-denoting term to one state. Trace names retain nonempty interpretations.
The generic label evaluator uses append, with the existing empty-unit laws.
Keep overlapping program-trace composition separate. Preserve stuttering
tests, the stuttering zero power of star, finite iteration, proper suffixes,
and evaluation of modalities over accumulated traces.

Formula-extension semantics receives the interpretation of its recursive
child over traces. The FOPL instance interprets its binder payloads by writing
one uniform value into every state of the trace, exactly as at present.
The core never assumes that an arbitrary extension is pure or has a
quantifier rule. An extension supplies/proves the relevant conditions locally.

Write the shallow judgment meaning explicitly:

```text
denote (R ; Gamma => Delta) w :=
  admissible (R ; Gamma => Delta) w ->
  relations_hold R w ->
  left_holds Gamma w -> right_holds Delta w.
```

Specify admissibility for all relevant label occurrences, including relation
arguments where applicable. Prove the false-sequent characterization gives
an admissible mapping with true relations/antecedent and false succedent.
Do not obtain rule soundness through an inadmissible premise.

World-term interpretation must satisfy support/coincidence and sorted
substitution laws. Fresh-world replacement changes only the selected world
mapping; the trace mapping remains fixed. FOPL proves these laws for updates.
There must be no fallback state for interpreting an empty assertion label.

## 4. Decisions and theory discrepancies

The following inherited decisions remain fixed for G3FOPL and are the proposed
shared conventions. The new abstraction must not reopen them implicitly.

| Decision | Required preservation |
| --- | --- |
| D1 | Label `Join` means append; `[s]` joined with `[t]` yields `[s;t]`, even when the states differ. A repeated state remains repeated. Program overlap merges a shared endpoint separately. The literal overlapping label clause in the manuscript is already superseded for the existing implementation. |
| D2 | Both quantifiers accept recursively pure FOL bodies only. Eigenvariable freshness includes labels, assignment targets, nested update terms, contexts, and bodies. Quantification changes all trace states uniformly. |
| D3 | Expand double-line displays before implementation. Preserve ordered premises, both left box-choice/star premises, and the context-only premise of weakening. |
| D4 | Every complete assertion label is nonempty. Empty components remain legal units. Admissibility is explicit in semantics and transferred by rules. |

**T1 — test-guard observation is a manuscript ambiguity requiring a decision
before declaring the generic PPL semantics settled.** The §2.1 clause writes
`I(phi?) = {ss | s in I(phi)}`, suggesting a singleton observation. The active
labelled test rules check `x Join x : phi`; under D1 this observes `[s;s]`.
The legacy code explicitly uses `formula_holds phi [s;s]`, and
`Benchmarks/Tests.v` includes a temporal guard that distinguishes the two.

Recommendation: retain the existing two-state guard interpretation in the
shared core, agreeing with the labelled rule displays and preserving FOPL.
Record the singleton-looking clause as a manuscript discrepancy. This is a
recommendation, **not a new user decision**. If the user instead requires
singleton guards for canonical PPL, present the necessary instance-specific
semantics/rule obligations and their effect on sharing; do not change FOPL
or reuse a test-rule proof with different semantics. Work independent of this
choice can continue, but the canonical PPL test semantics and its completion
claim remain gated on resolution.

For other newly encountered problems, record the exact definition/rule,
failed obligation or counterexample, recommended repair, alternatives, and
impact in `REFINEMENT_DECISIONS.md`; ask the user before applying a semantic
change. Unrelated milestones may continue. Do not edit `Theory/` to conceal
an inconsistency, add an axiom, or silently reduce the promised theory.

## 5. Progress, atomic rules, and certification

### 5.1 Factor the progress theory

Move the existing execution-history construction, counterexample relation,
minimum of the **sum of component-trace lengths**, rank lookup, and common
transport/descent lemmas into the generic `Progress.v`.

Prove generic counterparts of the existing `atomic_counterexample` and
`atomic_minimum` arguments for arbitrary length-two action relations.
For atomic box-right, choose a counterexample execution realizing the minimum
and assign its successor to the fresh world name. An arbitrary nondeterministic
successor need not justify the claimed minimum decrease.

Freshness must preserve every existing labelled formula and relation in the
contexts. The counterstep must choose **one false premise and one mapping**
satisfying **all advertised tag pairs on that edge**. Separate choices for
separate tags do not meet the framework contract.

Retain common sequence/choice/star nonincrease, test descent after T1 is
settled, and suffix/dual-suffix descent. Advertise a principal continuation
only where that traceable occurrence actually exists. In particular, the
first suffix-right premise has no recursive suffix continuation.

Keep FOPL state-switch/freshness arguments and assignment-specific
interpretation lemmas in `FOPL/Progress.v`, using the generic ranks and
transport theorems. Do not recreate the rank definition or framework instance
inside the first-order extension.

### 5.2 Rule inventory

Extend the expansion catalog with ownership and source references. Restore
the propositional atom schemes for general PPL; their legacy replacement by
FOPL atom rules does not justify omitting them.

| Rule family | Owner and required behavior |
| --- | --- |
| Atomic box-right | Core. Fresh successor world name; introduce `x R_a y` in the premise; extend `sigma Join x` to `sigma Join x Join y`. Prove countermodel mapping change and principal descent. |
| Atomic box-left | Core. Consume the selected matching relation assumption and box occurrence as in the displayed rule. No guessed successor or semantic relation decision. |
| Atomic diamond-right | Core. Use the selected relation assumption in the conclusion and the displayed successor-labelled premise. |
| Atomic diamond-left | Core. Introduce a fresh successor and its relation in the premise; prove eigenworld freshness. |
| Atom/first-state rules | Core. Atoms inspect the initial state; `First` evaluates its whole body on the singleton. FOPL's `(at)` is an instance of the generic atom-head rule. |
| Tests | Core once T1 is resolved. Preserve box/diamond left/right schemes and their exact guard placement. |
| Sequence, choice, star | Core. Preserve all primitive/derived left/right schemes, premise counts, and context order. Star zero remains a true-test stutter. |
| Suffix and dual suffix | Core. Both sides, singleton closure, and only justified continuing/progressing pairs. |
| Boolean and structural rules | Core. Identity, truth/falsity helpers, negation, conjunction, disjunction, implication, weakening, exchange, cut, sorted substitution, explicit label algebra, and exact/tag-renaming backlinks. Carry relations through each rule correctly. |
| Relation structural operations | Core. Proved context exchange/weakening/contraction as needed; substitution acts on relation arguments too. Do not invent tagged relation traces or arbitrary relation-closing axioms. |
| Assignment boxes/diamonds | FOPL. Preserve deterministic update-label schemes without requiring an extra relational hypothesis in the legacy statement. Derive them from common semantic/progress lemmas and the assignment interpretation. |
| Quantifiers | FOPL. Preserve universal/existential rules, capture avoidance, pure-body checks, and D2 freshness. |
| Manual terminals | FOPL. Preserve `close_atoms`, the separately documented compound-pure `close_pure`, and their caller-supplied proofs. No semantic truth oracle. |

Every rule must have its ordinary soundness theorem and a complete
`rule_counter_step`; axioms need their validity proof. Extending an interface
with a soundness obligation does not discharge that obligation: concrete
instances must prove it.

### 5.3 Generation and certification

Generalize `generate_axiom`, `generate_rules`, and `generate_requested`.
Keep position-sensitive context scans and conclusion/premise/edge checks.
Finite scans may enumerate existing matching relations. Concrete requests
choose successor names, relation occurrences, substitutions, cuts, positions,
and companions when the choice cannot be enumerated completely. Fresh world
names may be selected by a proved finite support scan, including relations.

FOPL generation adds assignment and quantifier requests/cases around the
shared verified constructors. Preserve its existing pure-terminal stopping
policy and negative-request behavior. The generic PPL instance must still
generate propositional rules; it must not accidentally inherit the FOPL
manual-terminal stop for all purely propositional sequents.

Prove successful generators return the requested conclusion, well-formed
premises, justified side conditions, and valid edge endpoints. Failure means
no verified requested instance was generated, not that a judgment is false.

Factor the existing checker-reflection proof into the core and retain the
endpoint `raw_check graph witness = true -> Valid (graph_root graph)` through
`certificate_sound`. Instantiate one shared kernel and pass its exact modules
to extension rules, generation, and certification. Avoid separately applying
generative functors and thereby obtaining incompatible judgment/graph types.

Keep the unchanged framework's conservative witness restriction documented:
at most one selected tag per node. Acceptance of every manuscript preproof
is not promised. Do not modify `Cyclic/` to remove that restriction.

## 6. Files and dependencies

Proposed final layout; entries below are deliverables, not files already made:

```text
LPL/
  Signature.v, Syntax.v, Semantics.v, Progress.v
  Rules.v, RuleGeneration.v, Certification.v       # generic production core
  PPL/Instance.v                                 # plain PPL vocabulary/frame adapters
  FOPL/
    Signature.v, Syntax.v, Semantics.v, Progress.v
    Rules.v, RuleGeneration.v, Certification.v     # specialization/thin adapters
    Compatibility.v
    LegacyReference/{Signature,Syntax,Semantics}.v # isolated preservation oracle
    Benchmarks/{Support,InvariantSupport,...}.v    # original benchmark suite
  Benchmarks/PPL/{Support,...}.v                   # new generic benchmarks
  Makefile, _CoqProject, build.py                  # local build only
  run_benchmarks.py
  refine-1-plan.md, REFINEMENT_DECISIONS.md
  RULE_EXPANSIONS.md, FOPL_COMPATIBILITY.md
  BENCHMARK_RESULTS.{md,json}, VALIDATION.md, README.md
  benchmark-logs/, validation-logs/, .build/
```

Dependency order is generic interfaces → generic syntax → generic semantics
→ generic progress → generic rules → generation/certification. FOPL syntax
defines its term/atom/update/binder payloads and instantiates generic syntax;
FOPL semantics interprets that same syntax. FOPL rule/generator extensions
reuse the single shared kernel. There must be no dependency from the generic
core to FOPL. Benchmark-specific integers and predicates stay in benchmarks.

`FOPL/Certification.v` should re-export an application of the shared checker
proof, not duplicate it. Likewise, other first-order files contain genuinely
first-order definitions/lemmas or adapters, not second copies of common rules.

The legacy reference is a **test-only** oracle for preservation. Stage only
the old signature, syntax, and semantics under its separate namespace, with
mechanical import-path changes audited against `LPL-old/`. Production theory
must not import it. This avoids treating a mutable newly written specification
as evidence that the old meaning was preserved. It does not create another
production calculus or require importing the hyphenated `LPL-old` directory.

Keep the original implementation plan and historical evidence distinguishable
from the new refinement results. Relocate old benchmark implementations into
`FOPL/Benchmarks/` and update local imports. The parent build configuration
enumerates the old paths and will not discover the new layout. The supported
refinement build command is the new local build; preserving the parent's old
`make lpl` entry point is not assumed under the strict scope constraint.

## 7. Demonstrate preservation of G3FOPL

Provide a requirement-by-requirement comparison with the immutable snapshot,
not merely a successful compilation report.

1. Define translations from legacy terms, formulas, programs, updates,
   labels, occurrences, and judgments to the FOPL instantiation. Relation-free
   old judgments translate to an empty relation context. Define inverse
   translations on the legacy image where useful.
2. Prove preservation/reflection of legacy well-formedness, arities,
   pure-body recognition, nonempty-label checks, and legal tags. Check that
   malformed legacy examples are still rejected.
3. Prove simultaneous formula/program semantic equivalence for arbitrary
   existing signatures/models, plus update/label evaluation equivalence.
   Deduce equivalence of admissibility, shallow denotation, and validity for
   translated relation-free judgments. Preserve empty-trace behavior too.
4. Show legacy counterexample histories and their measures correspond, and
   hence ranks agree for translated trace elements. Verify rule edges and
   tag-renaming maps retain their meaning.
5. Map every legacy rule/request to its shared or specialized counterpart;
   compare exact ordered premises and side conditions. Preserve the 50
   premise-shape checks and all existing negative checks. No additional
   transition premise may appear in a formerly relation-free assignment rule.
6. Port the same theorem statements, programs, invariants, graph scripts,
   and witnesses. Permit representation/import adaptations; record any
   unavoidable script change and prove it preserves the translated graph
   payload and trace relation. Do not weaken a theorem to make a test pass.

This is semantic and implementation preservation of the existing theory,
not a new completeness or arbitrary derivability-equivalence project. New
generic relational judgments are outside the legacy image; their presence
must not be mistaken for a changed meaning of the old FOPL fragment.

## 8. Implementation stages and acceptance gates

| Stage | Work | Required exit evidence |
| --- | --- | --- |
| 0. Freeze and decisions | Hash the entire outside-LPL tree and the legacy snapshot, record compiler versions and historical reports, establish a fresh pre-refactor benchmark baseline using LPL-local outputs, and document T1. | Immutable manifest; baseline commands/logs; accepted theory decisions clearly separated from recommendations. |
| 1. Interface feasibility | Compile the extension representation, relation syntax, world-term substitutions, and one shared-kernel skeleton. Instantiate plain PPL and a minimal FOPL binder/update example. | Both instances use the same common types/construction pattern; equality and reflected checks compute; no core import of FOPL. |
| 2. Generic syntax and semantics | Factor the common syntax/trace operations and implement relations, frame interpretation, admissibility, substitution/coincidence, and extension interpretation. | Core works for arbitrary states and nondeterministic action relations; semantic unit/stutter/overlap examples pass; T1 resolved before finalizing PPL test meanings. |
| 3. Progress feasibility | Generalize counterexample minima and prove atomic box-right descent with fresh-world transport, plus common regular/temporal obligations. | A single counterstep respects every advertised pair; arbitrary branching and context relations are handled. A genuine obstruction triggers the decision process. |
| 4. Generic rules | Implement all G3PPL primitive/derived families against the expansion catalog. | Every required scheme has ordinary soundness, admissibility transfer, and framework records; no admitted obligations. |
| 5. Generation/certification | Generalize scans/requests and checker reflection; build small acyclic and cyclic PPL certificates manually. | Successful-result guarantees; rejected malformed cases; validity follows through the unchanged `certificate_sound`. |
| 6. FOPL instantiation | Move first-order payloads/models/lemmas into FOPL; add assignment, quantifier, terminal, and generation extensions; prove compatibility. | Preservation theorems and rule map; generic rules are reused; all legacy statements remain available through the FOPL API. |
| 7. Full benchmarks | Run all 15 FOPL units and the PPL matrix below with hard timeouts, retain assumptions/logs, and compare baseline evidence. | Individual results, coverage, proof mode, nonvacuity, timings, and limitations are accurate and reproducible. |
| 8. Integration and audit | Finish local builds, documentation, kernel checking, dependency and immutable-scope audits. | Reproducible build; no outside-LPL differences; no missing theory families or undecided semantic changes concealed by the completion claim. |

Dependencies are sequential at the proof gates. FOPL compatibility scaffolding
and documentation can be prepared earlier, but the final specialization must
use the verified common core. A failed common proof cannot be bypassed by
keeping a duplicate first-order implementation and calling it an instance.

## 9. Benchmark plan

### 9.1 Preserve and rerun the same first-order suite

Retain all 15 units, now under `FOPL/Benchmarks/`:

| Units | Preservation target |
| --- | --- |
| `Labels`, `Signatures` | D1/D4, arbitrary models, independent Boolean/integer signatures, and nonvacuity. |
| `Updates`, `AssignmentChange` | Identity/changed/dependent updates, intermediate states, and the six-node assignment certificate. |
| `Tests`, `RegularPrograms` | Trace-sensitive guards, failed tests, sequence/choice, and zero/one/nested finite iteration. |
| `Booleans`, `Quantifiers`, `Temporal` | All connectives, binding/substitution/freshness, suffix/dual/first/next, and summed measures. |
| `RuleCoverage`, `CheckerNegative` | Existing exact premise lists, pure-terminal policy, negative syntax/generation cases, and malformed/nonprogressing graphs. |
| `Cyclic`, `CyclicTags` | Real backlinks, original star claims, explicit witnesses, and explicit tag renaming. Preserve 11/12-node graphs where representation adaptation permits; explain any proved equivalent reconstruction. |
| `CounterLoop`, `NestedProgram` | The original all-visited-state invariants for every finite stopping point, with no mandatory-exit claim. Keep their direct semantic proof classification. |

`Support.v` and `InvariantSupport.v` remain shared dependencies, not additional
logical benchmark successes. Never substitute new toy statements for an old
regression. A failed legacy theorem is a preservation failure to investigate.

### 9.2 New G3PPL suite

Use at least two independent DIY vocabularies and frames: a small finite
transition system with nondeterministic branches/dead ends, and an abstract
state/frame functor whose actions/propositions are arbitrary parameters.
Add a structured world-term/relation instance to exercise more than a simple
renaming of natural-number atoms. State/frame semantic predicates remain in
`Prop`; generators do not decide their truth.

| Proposed unit | Required examples and evidence |
| --- | --- |
| `Instances` | Two independent action/proposition types and an abstract frame; demonstrate no assignment, arithmetic, inductive predicate, deterministic-transition, or truth-decision dependency. Instantiate custom relation payloads and prove their interface laws. |
| `LabelsRelations` | Empty units, nonempty assertions, repeated/differing boundary states, sorted substitutions through relations, singleton endpoint meaning, and longer trace endpoints. Reject malformed relations and unsupported endpoint/request shapes. |
| `AtomicActions` | Exact premises of box/diamond left/right; fresh and explicitly supplied successor cases; wrong action/source/target and stale-eigenworld requests rejected. End-to-end generated certificates under the required relation assumptions. |
| `Nondeterminism` | One source with two possible successors; a box requiring both alternatives and a diamond witnessed by one. Add a countermodel to a deliberately false box and a no-successor case demonstrating box vacuity/diamond failure. Countermodels are semantic negative tests, not validity certificates. |
| `Booleans` | Each connective on both sides, atom-head and `First` with a compound body, mixed modal contexts, and non-head rule positions. Do not bypass ordinary PPL rules through the FOPL pure-terminal policy. |
| `Tests` | Successful/failed tests, stuttering output, guard observation under the resolved T1 decision, and exact box/diamond test schemes. |
| `RegularPrograms` | Sequence, choice, nested combinations, and zero/one/multiple/nested finite stars. Check actual traces, final stutters, branching, and accumulated-trace modality semantics. |
| `Temporal` | Immediate/postponed suffixes, dual suffix, singleton failure, next-at-end, and rank decrease where a continuation exists. Include a trace-sensitive body. |
| `RuleCoverage` | Every general primitive/derived scheme and explicit expansion; exact ordered premises, relation contexts, tags, substitutions, cut, exchange, weakening, and label algebra. Pair applicable requests with meaningful rejection cases. |
| `CheckerNegative` | Mismatched relations in a backlink, invalid endpoints/tags, missing/open/dangling nodes, wrong companions, and a closed nonprogressing cycle. Use buildable graphs with proved local records. |
| `Cyclic` | A genuine manually scripted star cycle using the new atomic box-right rule, explicit fresh-world/substitution steps, a real backlink, and a finite tag/potential witness. Show an accepted certificate and semantic validity. An acyclic unrolling is insufficient. |
| `CyclicTags` | A small genuinely cyclic example with explicit tag-renaming transport and full relation-context agreement. |
| `SafetySystem` | A finite nondeterministic resource/protocol system, e.g. idle → held → released with optional stuttering and dead ends. Prove a state safety predicate at every visited state of arbitrary finite iterations, including zero iterations and early stopping. |
| `NestedProgram` | Nested sequence/choice/star actions over an abstract protected component and an uninterpreted predicate. Prove preservation at every visited state using supplied action-preservation hypotheses. |

For cyclic examples, begin with a first-state observation invariant analogous
to the existing feasible cyclic benchmarks, while explicitly exercising the
generic atomic-action rule. Keep complex all-state invariants as separately
labelled semantic proofs unless a genuine certificate is also completed.
Do not describe a semantic induction proof as a cyclic proof.

Every positive logical benchmark exports validity or its precisely stated
conditional validity theorem. Give an admissible mapping for the root;
where relational/program hypotheses matter, also give a mapping satisfying
the antecedent and an example execution when the program should be live.
Failed-execution benchmarks deliberately document their vacuity. Syntax-only
and checker-rejection benchmarks report rejection evidence, not validity.

### 9.3 Timing and reporting

Compile common dependencies first using the local dependency graph. Time
each isolated benchmark with its dependencies already available. Dependencies
between benchmark files, such as `CyclicTags` depending on `Cyclic`, must be
explicit and compiled in order.

Examples from `Rocq-copy/`, using locally built compatible dependencies:

```sh
python3 LPL/build.py --common
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/FOPL/Benchmarks/AssignmentChange.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/PPL/AtomicActions.v
python3 LPL/run_benchmarks.py --suite fopl
python3 LPL/run_benchmarks.py --suite ppl
```

These are planned commands; the local builder and suite options do not exist
yet. Add explicit source/dependency manifests to the local build rather than
relying on the unchanged parent `make lpl-common` command.

The runner must record actual command/working directory, compiler version,
source and dependency hashes, elapsed time, exit status, timeout/failure
classification, theorem assumptions, rule coverage, graph size, distinct tag
count, proof mode, nonvacuity, and log paths. Generate report summaries from
actual records; remove the current runner's hard-coded success/coverage prose.
Keep historical logs and simplifications identifiable as historical evidence.

On a 600-second timeout, stop the process, record the incomplete case, and
simplify a new PPL example or its proof representation without weakening an
existing regression theorem. Do not raise the cap or repeatedly retry an
unchanged expensive obligation. If a required legacy case cannot be preserved
within the limit, report the conflict and obtain direction. A simplified new
benchmark does not erase an unresolved required rule or certificate gate.

For pure FOL obligations use standard Rocq tactics only; simplify/omit an
optional new benchmark if necessary and report it. Keep tag sets small:
framework relation fuel grows as `3^(number_of_tags^2)`. Avoid conversion tests
that compare entire proof-carrying rule records when checking their payloads
is the intended computational test.

## 10. Build and validation under the strict write scope

Create `LPL/Makefile`, `LPL/_CoqProject`, and/or `LPL/build.py` with explicit
dependency order. All report defaults and generated paths must remain inside
`LPL/`; the runner must reject outside output paths. Do not invoke parent
targets that could rebuild or create artifacts outside LPL.

Existing `Cyclic/Framework.vo` and `Relations.vo` were present at inspection.
Use them only after verifying compiler compatibility. If immutable dependencies
need rebuilding, stage their source copies and resulting artifacts under
`LPL/.build/` with the original logical namespaces mapped to that staged tree.
Do not compile their original physical files in place. Record actual mappings
in the build log. Apply the same approach to optional FirstOrder/LTL regression
builds, or report them unavailable; they do not import LPL and do not replace
the required FOPL regression suite.

Final verification includes:

- A dependency-ordered build of the generic core, both instances, compatibility
  oracle/theorems, and every benchmark, using fresh or hash-validated artifacts.
- Independent `rocq check` of representative generic syntax, a generic atomic
  cyclic certificate, FOPL compatibility/quantifier results, and FOPL cyclic
  and complex invariant results. Use bounded commands and retain logs.
- `Print Assumptions` for representative generic rules, atomic progress,
  certification, preservation theorems, and exported positive benchmark
  theorems. Report standard-library classical principles explicitly; permit
  explicit model/preservation parameters but no admitted soundness proofs.
- An import/source audit: no core-to-FOPL dependency, no copied common
  production calculus, no FirstOrder/LTL object-theory imports, no external
  solvers/libraries, and no proof-search implementation.
- Byte/hash and file-set comparison for **all** outside-LPL files, including
  generated artifacts and the complete `LPL-old/` snapshot. Detect newly
  created outside files as well as changed/deleted files. Read-only Git
  inspection may supplement this; do not rely solely on historical hashes.
- Documentation of supported local commands, instance construction, preserved
  conventions, resolved decisions, actual coverage, and remaining limitations.

## 11. Definition of completion

The refinement is complete only when the general G3PPL syntax, semantics,
relations, every requested primitive/derived rule family, local generation,
and cyclic certification are implemented with proved obligations; independent
DIY instances exercise the abstractions; and G3FOPL is an actual instance
with preserved meanings and reused common rule kernels.

All 15 original FOPL benchmark units must pass on their preserved claims,
the new PPL suite must provide the stated generic and cyclic evidence within
the 600-second limits, required theory decisions must be resolved, and the
outside-LPL scope audit must pass. An undecided semantics, failed preservation
proof, omitted required rule, or missing genuine cyclic benchmark is a named
remaining task, not a completed refinement.

For the present request, the deliverable is this plan only. No implementation,
fresh benchmark success, or theory decision is implied by its creation.
