# First-order compatibility and correction ledger

This document relates the current `FirstOrderNew` sources to the original
OCaml implementation and records the semantic, representation, and acceptance
boundaries. Original-source citations use repository-relative paths and
one-based line numbers; `.ml` citations without a directory prefix refer to
`src/firstorder/`. A correspondence identifies the operation being
reimplemented; it does not assert identical allocation, candidate enumeration,
proof graphs, or global-checker acceptance.

The reference input language is positive DNF: integer constants, variables,
function applications, equality, disequality, tagged predicates, conjunctions,
disjunctions, sequents, and ordered positive clauses. The source parser entry
points are `src/firstorder/term.ml:208–215`, `atom.ml:61–95`,
`prod.ml:24–28`, `form.ml:24–25`, `seq.ml:18–25`,
`case.ml:21–36`, and `defs.ml:34–56`.

## 1. Source-to-module correspondence

All `.v` paths below are relative to this directory.

| Original source and operation | Current module and contract |
| --- | --- |
| `src/firstorder/term.ml:5–18,25–35` — variable classification, constants, variables, function terms, comparison | `Syntax.v` — `Free`/`Exist`, `Const Z`, `Var`, `Fun`, decidable structural comparison; `Input.v` — deterministic name interning. |
| `src/firstorder/atom.ml:6–32,56–58,111–135` — equality/disequality/predicates, logical annotations, comparison, variables, substitution | `Syntax.v` — atoms, exact comparison, tag erasure, recursive variables; `Substitution.v` — recursive simultaneous substitution; `Input.v` — corrected parsing. |
| `src/firstorder/prod.ml:5–13,24–28,38–66`; `form.ml:5–8,24–38`; `seq.ml:6–35` — atom/product sets, DNF, sequents, inclusion and tag-sensitive operations | `Syntax.v` — list representation with set-like logical membership/inclusion; `Semantics.v` — conjunction/disjunction meaning; `Matching.v` — directional product matching and tracked-tag inclusion. Exact list equality remains a separate operation. |
| `src/firstorder/term.ml:91–148`; `prod.ml:77–99`; `form.ml:40–51`; `seq.ml:40–55` — substitution and directional matching/subsumption | `Substitution.v`, `Matching.v`, `RuleGeneration.v` — simultaneous substitution, bounded candidate matching, both orientations of equality matching, backlink planning. `LocalRules.v` supplies semantic substitution/weakening certificates. |
| `src/firstorder/term.ml:150–200`; `rules.ml:251–306` — repeated-head matching and optimized right unfolding | `Matching.v` — `head_match`/`head_match_terms`; `Unfolding.v` — checked arbitrary/matched clause instances retaining every head equation; `Compiler.v` — native descriptors and existential completion of unmatched clause locals. |
| `src/firstorder/case.ml:5–13,21–51`; `defs.ml:5–9,22–56` — clause bodies/heads, definition ordering, clause freshening | `Definitions.v` — flat ordered clauses, predicate arities and well-formedness; `Substitution.v` — generic freshening/universalizing; `Unfolding.v` — injective, proved left/right clause renaming; `Input.v` — header and signature diagnostics. |
| `examples/fo.defs:1–102` — supplied positive definitions | `SourceDefinitions.v` — literal AST transcript and an explicitly closed subset; `InputExamples.v` — textual transcript and comparison with the AST after tag erasure. |
| `src/firstorder/rules.ml:10–35,178–241` — contradiction/identity, left disjunction, right conjunction, existential instantiation | `Rules.v` — axiom checks and soundness; `LocalRules.v` — generic certified structural rules, guarded binary right splitting and product-local existential instantiation. |
| `src/firstorder/rules.ml:41–171` — six simplifications and repeated simplification | `Simplification.v` — pure bounded transformations; `LocalRules.v` — checked local evidence for the transformations; `Compiler.v` — certificate-derived bounded normalization programs. |
| `src/firstorder/rules.ml:251–348,427–473` — right unfolding, contraction left unfolding, folding | `Unfolding.v`, `LocalRules.v` — generic local certificates, clause/position checks, occurrence traces and scoped variables; `Compiler.v` — approved native descriptors and source-family menus. |
| `src/firstorder/rules.ml:350–425` — matching followed by explicit weakening/substitution and exact backlinking | `RuleGeneration.v` — candidate plans; `LocalRules.v` — free-only and scoped backwards-substitution certificates; `Search.v` — execute checked preparation before an exact backlink; `Adapter.v` — exact framework backlink instance. |
| `src/firstorder/rules.ml:477–506`; `prove.ml:1–10`; `src/generic/prover.ml:29–57` — rule-family setup, generic prover and iterative deepening | `RuleGeneration.v` — proof-free menus/programs; `Compiler.v` — recompilable native menus; `Search.v` — bounded, graph-abstract DFS/iterative deepening with an explicit final-acceptance contract. |
| `src/firstorder/rules.ml:3–5,316–339`; `src/generic/proof.ml:118–121`; `src/generic/soundcheck.ml:65–101` — abstract proof graphs and trace-pair annotations | `Rules.v`, `Rank.v`, `Adapter.v`, `Certification.v` — semantic countersteps, occurrence bounds, framework instances, and generic construction of graph certificates from checked graphs/witnesses. |

The explicit general-model/least-fixed-point semantics in `Semantics.v` is a
formalization of the intended positive calculus. It is not a transcription of
an OCaml semantic evaluator: the original FO entry point runs the generic
prover (`src/firstorder/prove.ml:7–10`).

## 2. Checked corrections and explicit policies

### C1. DNF identity: quantify over every antecedent disjunct

`src/firstorder/rules.ml:25–33` accepts a true right product, or checks **every
right product** against **some left product**. The latter reverses the coverage
needed for a DNF antecedent. In `Syntax.v:52–56`, `identityb` checks:

```text
for every left product p,
  there exists a right product q whose logical atoms are contained in p.
```

An empty right product is true and covers any left product; an empty antecedent
is false and is covered vacuously. For example, `(x=0) \/ (y=0) |- x=0`
must not pass identity merely because its first left disjunct matches.
`Syntax.v` contains that rejection regression. `Semantics.v:170–177`
proves `identity_sound`; `CompilerExamples.v` also checks the disjunctive case.

### C2. Disequality and function-headed equality parsing

* **Confirmed disequality defect:** `src/firstorder/atom.ml:87–91` parses `!=`
  but returns `mk_eq`. `Input.v` constructs `Deq`.
* **Confirmed parser-choice mismatch:** `atom.ml:61–76,94–95` tries a predicate
  application before equality. A function application on the left of an
  equality can therefore be consumed as a predicate prefix. `Input.v` first
  parses the term and checks the following `=`/`!=` before interpreting an
  unannotated application as `Pred`. Explicit bracket tags select predicates.

`InputExamples.v` checks `x!=w`, `s(x)=s(y)`, function-headed disequality,
equality in positive clause bodies, and that equalities allocate no predicate
tags. All public string entry points require end of input.

### C3. Recursive variables: repair the bypasses, not `Term.vars`

Original `Term.terms`/`Term.vars` already recurse through function arguments
(`src/firstorder/term.ml:77–83`). The incomplete paths are:

* predicate atoms: `atom.ml:117–121` takes a set of direct arguments and filters
  for variables without recursively collecting variables inside functions;
* clause heads: `case.ml:10–11` similarly starts with the direct head terms.

`Syntax.v:60–70` recursively collects terms, atoms, products, formulas and
sequents; `Definitions.v:10` uses it for both clause heads and bodies.
Consequently freshness, right-witness independence, and input scope checks see
variables at arbitrary nesting depth. The original right-conjunction guard
uses `Atom.vars` (`rules.ml:202–212`); the new guard uses recursive
`product_vars` (`LocalRules.v:728–759`). Nested-variable and nested-capture
regressions occur in `InputExamples.v` and `LocalRulesExamples.v`.

### C4. Tag-insensitive comparison: actually erase logical annotations

`src/firstorder/atom.ml:13–29` ignores its `match_tags` argument and still
compares predicate tags; thus `equal_upto_tags` is tag-sensitive. This does
**not** mean every original tag-insensitive operation is broken:
`atom.ml:111–115` implements an actual predicate comparison modulo tags, and
`prod.ml:48–63` strips untracked predicate tags during subsumption.

`Syntax.v:47–52` defines `atom_logical_eqb` by erasing predicate tags before
exact atom comparison. `Semantics.v:153–169` proves the semantic justification.
Exact atom/sequent comparisons retain tags. `Matching.v:56–59` preserves
specified tracked tags; the candidate backlink operations also retain tracked
logical annotations. Logical equality is not graph-label equality.

### C5. Headers, arities, and undefined predicates

Original `case.ml:21–26` returns the clause-head name. Although
`defs.ml:34–36` also parses the enclosing header, `defs.ml:52–55` discards that
header and adds clauses using their head names. `Input.v:403–414` rejects a
disagreement with `HeaderHeadMismatch`, including at the raw entry point.

Original matching already checks some arities: function argument lengths in
`term.ml:123–139,167–183`, predicate matching in `atom.ml:137–143`.
The new addition is **whole-input signature validation** rather than a claim
that the source has no arity checks. `Definitions.v:14–37` and
`Input.v:477–542` check:

* consistent head arity for every clause sharing a predicate name;
* defined predicate names and actual argument arities in clause bodies/goals;
* unary `s` and binary `cons`, recursively in all relevant terms;
* antecedent variable scope.

Forward/mutual references are checked against the complete parsed definition
list. Other function symbols are interpreted by symbol and argument list;
there is no additional globally fixed arity signature for arbitrary functions.
`parse_term`, `parse_atom`, `parse_product`, `parse_formula` and raw parsing
are syntactic interfaces, not substitutes for checked sequent validation.
`parse_definitions_sound` and `parse_sequent_sound` prove the existing
well-formedness checks on successful checked parsing.

### C6. Preserve and diagnose `ADD_2`

`examples/fo.defs:79–82` defines `MUL`; line 81 refers to `ADD_2`, while
lines 74–77 define `ADD`. The full supplied file does not define `ADD_2`.
`SourceDefinitions.v:54–56,76–83` preserves the reference and reports it.
There is no invented predicate or silent replacement by `ADD`.

`InputExamples.v` compares all 46 parsed clauses with `source_definitions`
after erasing only tags; checked parsing reports `UndefinedPredicate "ADD_2"`.
The explicitly selected 44-clause subset excludes the two `MUL` clauses and
matches `closed_source_definitions`. `COUNT` retains the source guard from
`examples/fo.defs:71` as `Deq`. Selecting that closed subset is an explicit
environment choice, not a repair to the literal transcript.

### C7. Free/existential scope is explicit

Source spelling classification is in `src/firstorder/term.ml:10–16`;
class-preserving clause freshening is in `case.ml:38–51`; left unfolding
subsequently universalizes clause variables in `rules.ml:329–335` using
`prod.ml:101–109`.

The current contract is:

* free goal variables are universal parameters;
* checked antecedents contain only `Free` variables;
* right existential witnesses are local to each right product, even when the
  same `Exist` identifier appears in different disjuncts;
* clause valuations are local witnesses in the inductive definition semantics;
* left-unfolded clause variables of **both** classes become fresh free
  eigenvariables.

`Semantics.v:43–47` implements right-product-local scope by choosing a product
and its own valuation agreeing on free variables. `Input.v:513–534` rejects
primed antecedent variables recursively. `Unfolding.v:39–95,306–318` proves
injectivity and freshness of its left/right renamings. In particular, the
left variable code distinguishes `Free n` from `Exist n` before universalizing.

Original `instantiate_ex` applies a substitution to the whole sequent
(`rules.ml:228–240`). Native right instantiation selects a right product and
substitutes that product (`LocalRules.v:471–487`,
`Compiler.v:67–75,165–172`). Right conjunction is a checked **binary** split
with disjoint existential scopes (`LocalRules.v:728–802`), rather than the
original flat atom split (`rules.ml:194–223`). Shared free variables are allowed.

### C8. Bounded simplification returns an unfinished obligation

Original `src/firstorder/rules.ml:165–171` repeats the first available
simplifier without an explicit step bound in this function. The six-family
priority is retained. `Simplification.v:61–72` distinguishes `Normal` from
`Exhausted`; `x=s(x)` is a regression for exhaustion rather than divergence.

These pure transformations are not certificates by themselves. Checked native
simplifications are in `LocalRules.v`; `Compiler.v:150–162,274–284` constructs
programs from their actual certificates. When a changed simplification remains
but its budget is zero, normalization returns `ProgramOpen`, not an axiom.
`Search.v:130–137,168–217` also bounds DFS, program execution and iterative
deepening. Exhaustion or no accepted candidate means **unknown**, not falsity.
Constructor laws do not justify rejecting `x=s(x)` by an occurs check.

## 3. Substitution, matching, folding, and right clause locals

### Simultaneous substitution and two matching contracts

Original `src/firstorder/term.ml:97–103` returns a mapped variable's image
directly; it does not recursively resubstitute that image. `Substitution.v:5–20`
preserves this simultaneous behavior. Its list lookup uses the first binding;
duplicate domains therefore have a defined first-binding interpretation,
unlike the source map representation. The example mapping `x -> y, y -> 0`
leaves the image of `x` as `y`. `Semantics.v:189–216` proves evaluation
transport through the substituted valuation.

Directional matching follows `term.ml:105–148` and
`prod.ml:77–98`: only pattern-side variables acquire bindings. Existential
pattern variables have restricted existential-variable images; free patterns
can match terms. This is not MGU unification. Both orientations of equality
and disequality are tried. `Matching.v:16–40` bounds the recursion and checks
the resulting simultaneous term instance with `match_term_correct`.

Repeated-head matching is a separate operation. Source `term.ml:156–200`
collects multiple target images of a head variable and creates equalities;
`Matching.v:61–87` creates constraints for repeated head occurrences, allowing
either class of head variable. Matching is a candidate generator. In the native
right schema, every argument/head equality is rebuilt after the **final**
substitution (`Unfolding.v:873–1000`), so a partial match or its returned
constraint list is never accepted as a soundness proof.

### Generically verified folding

Source folding uses the raw clause, skips empty bodies, matches its body into
the left product, removes body facts modulo predicate tags, and inserts a fresh
head (`src/firstorder/rules.ml:427–473`). `Rules.v:97–109` proves
`fold_instance` for an arbitrary simultaneous clause instance, without a
freshness premise: the substituted valuation supplies the clause witnesses.

`LocalRules.v:870–966` lifts that fact to a generic certified folding rule. It
checks clause membership, instantiated-body inclusion, a free source left
product, and a free instantiated head. It removes **all logical copies** of
consumed body atoms, retains unchanged remainder occurrences, and inserts a
new head occurrence with an independently chosen finite bound. There is no
incoming trace or progress claim for that new head. Clause-local `Exist`
domains may be instantiated with free goal terms when the checked head/body
conditions hold.

The low-level `checked_fold` also permits an empty-body clause; the native
compiler/menu deliberately skips such cases, matching the source search policy
(`Compiler.v:101–105,235–242`). The native menu uses raw clause substitution
domains and offers folding only with an immediate compilable backlink
(`Compiler.v:293–306`). `LocalRulesExamples.v` and `CompilerExamples.v`
cover repeated body facts, scope rejection, trace origins and raw clause domains.

### Scoped backwards substitution

The source makes weakening and substitution explicit before exact backlinking
(`src/firstorder/rules.ml:378–425`). `LocalRules.v:319–367` first supplies a
free-to-free-term checked backwards-substitution API. The broader
`checked_backward_substitution_scoped` (`LocalRules.v:968–1132`) permits:

* free variables to map only to terms whose recursively collected variables
  are free;
* existential variables to map only to existential variables;
* existential images to be injective over the **whole companion scope**,
  including identity images of existential variables absent from the explicit
  substitution domain.

An existential swap is admissible; renaming one variable onto a still-unmapped
existential is rejected. The whole-companion condition is conservative relative
to independently scoped right disjuncts. Generic witness reconstruction,
countersteps, target lemmas and `backlink_prefix_scoped_sound` establish the
semantic contract. `Compiler.v:76–83,244–272` uses these native certificates
and recertifies each preparatory step; matching alone cannot bypass them.

### Right matching plus existential local completion

Source right unfolding freshens classes and substitutes a selected head match
(`src/firstorder/rules.ml:263–303`, `case.ml:38–51`). Native
`Unfolding.right_clause` likewise preserves classes. Plain right unfolding with
fresh free clause locals is a sound sufficient-premise rule; it does not by
itself turn those locals into existential right witnesses.

`Compiler.v:185–234` completes the generated right scope: unmatched fresh free
clause variables receive fresh `Exist` images, avoiding the goal, fresh clause
and existing substitution ranges. Input prime locals remain prime and fresh.
The substitution applies **only to the fresh clause**, never to the goal or
its surrounding context. All instantiated head equations remain. The schema
`right_unfold_instance_evidence` proves soundness even for arbitrary or
nonmatching substitutions; matched candidates are its specialization.

When a constructor head cannot structurally match a symbolic goal argument,
the compiler may generate an equation-based fallback with completed local
witnesses. Such a fallback is rechecked by the same instance schema, not a
pretended successful match. `CompilerExamples.v:145–205,413–422` distinguishes
plain class-preserving instances, matched instances, repeated-head equations,
unmatched free locals, and the existential base-case fallback.

## 4. Logical sets, reified lists, and exact graph labels

Original products/formulas are sets (`src/firstorder/prod.ml:5–7`,
`form.ml:5`); the current AST is a list of atoms and a list of products
(`Syntax.v:13–15`). Its semantics still gives set-like conjunction/disjunction:
`Forall` for a product, existence of a satisfied formula member. Reordering or
repeating logically identical facts does not change that truth condition.
Different logical annotations on the same predicate do not change its truth.

Lists intentionally retain order and duplicate occurrences. Substitution may
make previously different atoms syntactically equal without merging their
positions. Occurrence transport prefers unused source occurrences and reuses
one only when needed for contraction (`LocalRules.v:89–198`). Explicit
`normalize_product`/`normalize_formula` remove exact duplicates; they do not
sort lists or produce a canonical representative of all logical equivalences.
`replace_product` inserts a changed product first and removes all exact copies
of the selected original product (`Syntax.v:97–98`). Native premise layouts
can thus differ from index-only replacement in raw proposals.

There are three distinct comparisons:

1. **Exact syntax:** tags, variable classes/IDs, operand orientation, order and
   multiplicity all matter (`Syntax.v:17–45`). Framework judgments and backlinks
   use this comparison (`Adapter.v:15–16`).
2. **Logical atom inclusion:** erases predicate tags but otherwise compares the
   reified atom exactly (`Syntax.v:47–56`).
3. **Candidate operation/matching comparison:** may also try swapped equality
   operands (`Matching.v:46–51`, `RuleGeneration.v:77–92`).

Original exact equality/disequality comparison is **ordered**, not an unordered
pair comparison (`src/firstorder/atom.ml:15–16`); source matching separately
tries both orientations (`term.ml:141–148`). A broader candidate comparison
must therefore not be presented as exact source set equality or as a native
graph-label check. `CompilerExamples.v:311–316` demonstrates a symmetric raw
weakening candidate rejected by the exact native check. Raw/native premise
mismatches for changed-product replacement and flat right splitting are also
explicit regressions there. The compiler derives proposals from certificates
instead of pretending those layouts agree.

Definition order is partly preserved and partly representation-dependent.
Original `defs.ml:22–30` groups repeated declarations under the first occurrence
of a predicate name and appends its cases. New parsing retains a flat textual
clause order; `clauses_for` preserves each predicate's case order. Interleaved
repeated declaration blocks can therefore have a different global enumeration
order. Source set traversal/choice (`prod.ml:82–96`, `form.ml:40–47`) is also
not reproduced identically by list traversal. Rule-family priorities are
retained (`rules.ml:477–506`, `Compiler.v:298–316`), but exact candidate order,
fresh names, graph shape and resource consumption are not promised identical.

Original variables are hash-consed and use physical equality/hash-cons tags
(`src/lib/varManager.ml:155–178`); source containers use tree sets/maps and
hash tables (`src/lib/containers.ml:29–36`). The current pure AST and natural
IDs do not reproduce these runtime identities, hashes, caches or sharing.

## 5. Logical annotations versus occurrence trace IDs

Source left unfolding assigns the selected atom's logical tag to body
predicates, retains a fresh-tagged contraction copy, and records trace pairs
between tags (`src/firstorder/rules.ml:316–339`). These grouped annotations
remain representable and preserved in current labels: repeated explicit input
tags remain repeated, and `Unfolding.v:406–415` retags children and the copy
according to that logical convention.

Internal trace IDs are different: `Syntax.v:99–104` takes predicate positions
in the flattened antecedent, counting equality/disequality positions too.
Thus two predicate occurrences sharing one logical tag have distinct trace IDs,
and IDs are local to each exact label. The adapter exports those occurrence IDs,
not `logical_tags` (`Adapter.v:18–19`).

Left unfolding proves strict descent from the selected principal occurrence to
its predicate children, nonincrease to its contraction copy, and occurrence
transport for untouched context. Other antecedent disjuncts receive pass-through
premises with rebased offsets (`Unfolding.v:406–444,707–871`). Base clauses
have no predicate-child progress edges. Administrative rules transport bounds
through checked occurrence maps; folding traces only its unchanged remainder.
Neither shared names nor logical-tag equality alone supplies rank evidence.

This avoids assigning an unproved maximum/sum measure to a source tag grouping.
`Rank.v:35–59` uses occurrence bounds as framework ranks and separately proves
minimum-stage unfolding descent. Duplicate occurrences, contraction and
substitution collapse remain explicit. It is not a free-standing claim that
every original source trace annotation is semantically justified.

## 6. Semantics: general models and least fixed points

`Semantics.v:9–19` quantifies over carriers equipped with interpretations of
all integer constants and function applications. The carrier is inhabited by
`constant_value 0`. Its **exact additional constructor laws** are:

* unary `s` is injective;
* binary `cons` is jointly injective in its two arguments;
* `0` is not a unary `s` value;
* `0` is not a binary `cons` value.

No distinctness of all integer constants, disjointness of `s` and `cons`,
injectivity of arbitrary functions, surjectivity, constructor generation of the
entire carrier, or acyclicity of constructors is assumed. Models are general
first-order structures, not only free syntax trees. These laws correspond to
the source's zero/constructor contradiction test and supported injectivity
simplifier (`src/firstorder/rules.ml:10–23,76–100`). The native constructor
rules additionally check supported arities (`Rules.v:35–67`,
`LocalRules.v:649–708`). Arbitrary-function congruence is proved without
assuming arbitrary-function injectivity.

Predicate meaning is the simultaneous positive least fixed point:
`stage 0` is empty, `stage (S n)` applies a clause with a locally chosen
valuation and bodies interpreted at stage `n`, and `inductive_relation` is the
union of finite stages (`Semantics.v:31–41`). `inductive_unfold` and
`inductive_least` (`Semantics.v:129–151`) prove closure and leastness, including
mutual recursion. Equality/disequality guards do not negate predicate relations.

Framework worlds additionally select an antecedent product and record a finite
stage bound for each antecedent occurrence (`Semantics.v:86–115`). The rank
used by the adapter is the recorded `world_bounds` value, not necessarily the
minimum derivation height (`Rank.v:35–36`). Crucially,
`valid_iff_worlds` (`Semantics.v:116–128`) proves:

```text
ordinary least-fixed-point sequent validity
  iff every bounded-occurrence world satisfies the sequent denotation.
```

Bounds are proof/countermodel bookkeeping, not a different bounded logic.
`Adapter.valid_bridge` uses this equivalence. Logical tags are semantically
irrelevant; occurrence bounds support the certified descent argument.

## 7. Approved compilation and graph acceptance

`Rules.v:15–33` packages generic local countersteps and rank obligations in
`local_evidence`; `certified_application` also fixes the exact conclusion.
`LocalRules.certified_local_sound` derives ordinary local soundness. These
schemas are parameterized by the definition environment and input labels;
their proof obligations are not supplied by benchmark-specific dispatch.

Raw `RuleGeneration.v` descriptors, anticipated premise lists, and menus are
proposals. `Compiler.compile_rule_descriptor` recognizes only its enumerated
approved schemas and validates their side conditions. `compiled_source_menu`
derives premise labels from the resulting certificates and recompiles all
application/preparation proposals. `compiled_source_menu_recompiles` and
`compiled_proposal_local_sound` state that boundary (`Compiler.v:328–379`).
`Search.checked_apply` additionally requires exact agreement with the compiled
conclusion and **ordered complete premise list** (`Search.v:45–71`).
An expected label or a successful matcher is never proof evidence.

The original FO rules also separate concrete judgments from an abstract graph:
`src/generic/proof.ml:118–121` projects to abstract nodes;
`src/generic/soundcheck.ml:65–101` represents node tags plus relational
valid/progress pairs.
Source backlink insertion calls `Proof.check`
(`src/generic/proofrule.ml:74–87`). Its global infinite-descent machinery
includes relation-composition checks and automata/external backends
(`src/generic/soundcheck.ml:716–754,1063–1125,1189–1221`); the default selected
backend is `ORTL_CPP` (`src/generic/soundcheck.ml:5–20`). These are not the new
framework's acceptance algorithm, nor a proved acceptance-equivalence theorem.

`Search.v` itself remains **graph-abstract**: a caller supplies immutable graph
operations, a compiler, partial checking and `final_accept`
(`Search.v:7–23`). `accepted_search_validity` requires the caller's proof that
final acceptance implies validity (`Search.v:276–285`). A raw completed
candidate or locally certified steps alone do not establish global cyclic
validity. DFS backtracks after final rejection; resource exhaustion remains
unknown. The graph APIs in `SearchExamples.v`/`CompilerExamples.v` are algorithm
regressions, not a replacement for the certified graph-acceptance contract.

`Certification.v` supplies the generic FO graph bridge: from structural checks
it derives countermodel advancement and false-node liveness, reflects witness
transitions, constructs a certificate, and proves `checked_graph_sound`
(`Certification.v:69–165`). This supplements the executable checks with kernel
checked semantic evidence.

The frozen framework uses a **conservative fixed per-node witness**: one
optional occurrence tag and one natural auxiliary potential at each node.
On every edge into a live region, a followed tag must continue along a valid
pair; it must either progress or the auxiliary potential must decrease. Before
tag selection the potential decreases, and once selected the witness cannot
return to no tag (`Rocq-copy/Cyclic/Framework.v:494–571`, read-only interface).
The source relational/global criterion permits trace choices along paths;
a single nodewise routing choice is an additional restriction. No claim is
made that every source-accepted graph admits this witness, or that witness
failure establishes semantic invalidity. `PLAN.md:112–115` records that scope
distinction. The FO certificate bridge does not modify that frozen criterion.

The local evidence uses the standard-library classical/description principles
identified in the module assumption audits (for example
`Unfolding.v:8–17`). Generic verification here means the stated Rocq theorems
under their actual library assumptions; it does not mean an axiom-free
constructive development of every countermodel selector.

## 8. Concrete input deviations and limits

* **Underscore:** the source classifies `_` as `ANONYMOUS`
  (`src/firstorder/term.ml:5–16`). Its variable manager interns a distinguished
  anonymous singleton, excluded from both free and existential classification
  (`src/lib/varManager.ml:161–192`); the FO variable constructor also asserts a
  nonzero manager ID (`term.ml:56–58`). The current two-class AST instead parses
  `_` as an ordinary stable `Free` name. It is not a fresh wildcard or an
  anonymous-variable compatibility emulation.
* **Name allocation:** current parsing starts first-seen variable IDs at zero
  for each complete input, preserves the complete spelling and final-apostrophe
  class, and shares the map across both goal sides or a definition transcript.
  Source hash-cons/fresh-name allocator IDs and runtime state are not retained.
* **Tags:** bracketed symbolic names are interned; nonnegative numeric bracket
  tags are an extension. All explicit tags are reserved before implicit
  allocation, including late annotations. Source parsing updates a mutable
  `used_tags` reference while parsing (`src/firstorder/atom.ml:59–75`). The new
  tag model stores only `nat`: apostrophes distinguish symbolic tag spellings
  but do not introduce a tag variable class.
* **Numbers and delimiters:** constants are arbitrary-precision `Z`, rather
  than OCaml `int` (`term.ml:18`); signed decimal constants are supported. A
  final definition semicolon is accepted. The source definition parser uses
  `sep_by1` followed by EOF (`defs.ml:48–56`); identical combinator behavior on
  every malformed/trailing delimiter is not assumed.
* **Source input versus printer dialect:** conjunction is `&`, disjunction is
  `\/`, truth is the whole empty product written `true`, and definitions use
  `=>`, `|`, braces and semicolons. Empty applications and definition blocks/files,
  false literals, grouping of formulas, explicit quantifiers, and predicate
  negation are rejected. Empty formulas can still be constructed directly in
  the AST and denote false. The OCaml display forms `T`, `F` and `name_tag(...)`
  (`prod.ml:21–36`, `form.ml:12–22`, `atom.ml:34–49`) are not advertised as
  parser round-trip input.
* **Diagnostics and totality:** input errors are structured values with syntax
  offsets or named validation payloads; fuel exhaustion is distinct. Default
  input fuel is `16 + 4 * String.length input`. That budget controls lexical
  steps/recursive parsing depth, not a wall-clock or memory limit. Raw parsing
  preserves undefined references for inspection while still checking syntax
  and header agreement.

## 9. Acceptance target and follow-up concerns

The source acceptance target is the nine active `.tst` files in
`benchmarks/fo`, each with its goal on line 1:

| File | Goal |
| --- | --- |
| `01-odd-even.tst` | `O(x) \|- N(x)` |
| `02-even-or-odd.tst` | `E(x) \/ O(x) \|- N(x)` |
| `04-n-is-even-or-odd.tst` | `N(x) \|- O(x) \/ E(x)` |
| `05-p-and-q.tst` | `N(x) & N(y) \|- Q(x,y)` |
| `07-a-plus-zero.tst` | `N(x) \|- ADD(x,0,x)` |
| `08-sum-is-nat.tst` | `N(x) & N(y) & ADD(x,y,z) \|- N(z)` |
| `09-a-plus-b-plus-one.tst` | `N(x) & N(y) & ADD(x,y,z) \|- ADD(x,s(y),s(z))` |
| `13-2-hydra.tst` | `N(y) & N(x) \|- H(x, y)` |
| `14-two-n-is-n2.tst` | `N(y) & N(x) \|- N2(x,y)` |

`PLAN.md:119–123` requires all nine through the same generic search path.
`InputExamples.v` checks their parsed ASTs and well-formedness; those are
**input regressions, not nine successful proof-search executions**. This
document reports no end-to-end benchmark search/certification run and makes
no all-nine-success claim. Benchmark outcomes, final build commands and any
scope decision belong to the integration report.

Concrete follow-up concerns are:

1. Connect the graph-abstract search contract to the concrete certified graph
   insertion, witness synthesis and root-validity result. Preserve the
   distinction between local compilation, a closed candidate and final global
   acceptance.
2. Run the nine-goal acceptance target with recorded definition environment,
   limits and certificate results; retain unknown/rejected outcomes explicitly.
   Discuss a scope change before relaxing that target, as the plan requires.
3. Measure the fixed per-node witness restriction against source-style trace
   routing on encountered graphs. Witness rejection is a conservative
   acceptance issue, not evidence that the goal is false.
4. Track candidate loss from ordered exact comparisons, singleton-left
   restrictions on native weakening and left-changing simplifications,
   changed-product duplicate removal, and bounded enumeration. Any
   exchange/orientation/normalization extension must be a
   checked derivation with remapped occurrence edges, not relabeling a graph.
5. Decide deliberately whether later compatibility work should emulate the
   source anonymous class, add a parser/printer round trip, or impose additional
   arbitrary-function signatures. Current behavior and limits above remain
   the explicit contract until such a change is implemented and verified.
