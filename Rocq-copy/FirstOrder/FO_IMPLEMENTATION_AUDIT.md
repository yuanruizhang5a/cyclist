# Audit of the Rocq first-order implementation

Date of audit: 2026-10-10

This document compares the implementation in this directory with the original
OCaml first-order prover in [`src/firstorder`](../../src/firstorder), the generic
OCaml search in [`src/generic/prover.ml`](../../src/generic/prover.ml), the
definition library in [`examples/fo.defs`](../../examples/fo.defs), and the
first-order benchmark suite in [`benchmarks/fo`](../../benchmarks/fo).

`Rocq-copy/FirstOrderNew` is a separate development and is intentionally not
part of this audit.

## Executive conclusion

The implementation is a substantial, proof-producing reimplementation of the
first-order theory, but it is not yet a complete operational port of the
original prover.

| Area | Assessment | Short reason |
| --- | --- | --- |
| Reified FO syntax | Largely implemented | Terms, two variable classes, atoms, DNF formulae, clauses, definitions, substitutions, tags, and decidable equality exist. |
| Mathematical semantics | Strongly implemented | The Rocq development adds an explicit free-constructor value model, ranked inductive predicates, existential RHS witnesses, and trace ranks. |
| Soundness infrastructure | Strongly implemented | Every exposed inference is theorem-backed; successful proof graphs are rechecked and reflected into a `Cyclic.certificate`. |
| Axioms and simplification | Substantial but partial | Most original simplifiers exist, including recent tag-insensitive identity, RHS discharge, and constructor equality decomposition. Several rules are deliberately more restrictive. |
| Unfolding | Substantial but not exact | Sound left and right unfolding exist, including arbitrary-position wrappers, but original right-unfold multi-unification is not reproduced exactly. |
| Backlinks | Partial | Exact backlinks and restricted explicit substitution/weakening preparation exist; full unification/subsumption and tag minimization do not. |
| Search | Sound but incomplete | Bounded certification-aware DFS and trace-witness search exist, but rule coverage, scheduling, and fuel semantics still differ from OCaml. |
| End-to-end benchmark API | Transitional | All nine positive goals return checked certificates, but exact benchmark theorems remain as a fallback dispatcher. |
| Parser and CLI | Not implemented | There is no Rocq parser for the original textual language, definition-file loader, printer, or `cyclist fo prove` command. |

The most important distinction is therefore:

- **Soundness is in good shape.** A successful general search result cannot
  bypass the semantic rule proofs or the graph checker.
- **Completeness and behavioral parity are not finished.** Failure to find a
  proof can still be caused by missing rules, narrow matching, ordering, or
  insufficient fuel.
- **The nine `true` benchmark results are not nine automatic graph-search
  results.** They currently include a theorem-backed benchmark dispatcher.

No source change to `Cyclic/` was needed for the implementation audited here.

## Status labels used below

- **Done**: the corresponding logical operation is implemented and connected.
- **Partial**: a sound subset or a behaviorally different version is present.
- **Missing**: no corresponding operational implementation is connected.
- **Rocq addition**: functionality needed for formal semantics or verified
  certification that has no direct first-order OCaml counterpart.

## Original modules and their Rocq correspondents

| Original code | Rocq correspondence | Status and important differences |
| --- | --- | --- |
| [`term.ml`](../../src/firstorder/term.ml) | [`Syntax.v`](Syntax.v): `var_kind`, `variable`, `term`, substitutions and shifting. [`Automation.v`](Automation.v): variable collection, fresh variables, matching and unification. [`Rules.v`](Rules.v): substitution semantics. | **Partial.** Core AST, equality, substitution, freshness, directional matching, occurs-checked symmetric unification, and soundness gates exist. Exact `multi_unify_args` behavior and pair unification are not integrated. Constants are `nat`, not OCaml `int`; variables use numeric IDs, not parsed names. No term parser/printer. |
| [`atom.ml`](../../src/firstorder/atom.ml) | [`Syntax.v`](Syntax.v): `Eq`, `Neq`, `Pred`, tag operations, substitution, exact and tag-insensitive equality. [`Automation.v`](Automation.v): variable extraction. | **Partial.** The data and tag behavior are present. Atom-level `unify_eqs`, `unify_deqs`, and `unify_ipreds` are not separately reproduced; parsing and printing are absent. |
| [`prod.ml`](../../src/firstorder/prod.ml) | [`Syntax.v`](Syntax.v): `product`, membership/subset checks and tags. [`Automation.v`](Automation.v): normalization and set-style equality helpers. [`Semantics.v`](Semantics.v): conjunction semantics. | **Partial.** Logical set behavior is proved for normalization, but the executable representation is a list. `nodup` removes duplicates without producing a canonical sorted order. Full `uni_subsumption`, arbitrary left subsumption, selected-tag subsumption, and `univ` are not implemented as general operations. |
| [`form.ml`](../../src/firstorder/form.ml) | [`Syntax.v`](Syntax.v): `formula`. [`Automation.v`](Automation.v): normalization and finite-set helpers. [`Semantics.v`](Semantics.v): disjunction semantics. | **Partial.** DNF formulae and semantic normalization are present. General left/right formula subsumption and canonical ordered-set behavior are missing. |
| [`seq.ml`](../../src/firstorder/seq.ml) | [`Syntax.v`](Syntax.v): `sequent`, equality, tag-insensitive backlink comparison, and substitution. [`Semantics.v`](Semantics.v): `sequent_holds`. | **Partial.** The reified object and semantics exist. Full `Seq.uni_subsumption` and `Seq.subsumed_wrt_tags` are only approximated by narrower backlink helpers. No textual parser or printer. |
| [`case.ml`](../../src/firstorder/case.ml) | [`Syntax.v`](Syntax.v): `clause`. Shifting/freshening functions in `Syntax.v`; unfolding constructions in [`Rules.v`](Rules.v). | **Largely done for rule use.** Clause body/head data and capture-avoiding numeric shifts exist. The exact OCaml `Case.freshen` API, parser, and printer do not. Right unfolding turns fresh clause variables into existential witnesses; left unfolding preserves kinds while shifting. |
| [`defs.ml`](../../src/firstorder/defs.ml) | [`Syntax.v`](Syntax.v): ordered `definitions` association list and `lookup_definition`. [`Definitions.v`](Definitions.v): the concrete library. | **Partial.** Ordered lookup and the supplied library exist. There is no `Defs.add`, parser, file loader, or dynamic CLI setup. Arbitrary reified definitions can still be carried in a judgment. |
| [`rules.ml`](../../src/firstorder/rules.ml) | Semantic kernels in [`Rules.v`](Rules.v), syntax-directed selection in [`RuleGeneration.v`](RuleGeneration.v), backlink preparation in [`GraphSearch.v`](GraphSearch.v). | **Substantial but incomplete.** See the rule-by-rule table below. |
| [`prove.ml`](../../src/firstorder/prove.ml) | [`Search.v`](Search.v), supported by [`GraphSearch.v`](GraphSearch.v) and [`Certification.v`](Certification.v). | **Partial.** There is a total proof-producing API and a soundness theorem, but no command-line frontend, file loading, timeout option, proof printing, or exit behavior. |
| Generic OCaml proof/search modules | [`GraphSearch.v`](GraphSearch.v), [`Certification.v`](Certification.v), and the unchanged [`../Cyclic`](../Cyclic) framework. | **Partial search, stronger checking.** DFS differs operationally, but every returned graph is checked by a formally justified certificate path. |
| [`examples/fo.defs`](../../examples/fo.defs) | [`Definitions.v`](Definitions.v). | **Done as an AST transcription.** All 19 named definitions are present in source order. The source's unresolved `ADD_2` reference in `MUL` is faithfully retained and remains unresolved. |
| Positive files under [`benchmarks/fo`](../../benchmarks/fo) | [`Benchmarks.v`](Benchmarks.v), [`Derived.v`](Derived.v), and [`Search.v`](Search.v). | **Validity done; automatic parity incomplete.** All nine enabled positive goals have semantic proofs. General search is not yet the sole source of those proofs. |

## Rocq files by responsibility

| Rocq file | Main responsibility |
| --- | --- |
| [`Syntax.v`](Syntax.v) | Reified syntax, equality, substitutions, variable shifting, tag collection/preparation, definition lookup, exact and tag-insensitive containment. |
| [`Semantics.v`](Semantics.v) | Free-constructor values, valuations, existential RHS witnesses, ranked inductive interpretations, judgment denotation, and trace ranks. |
| [`Automation.v`](Automation.v) | Semantics-preserving normalization, variable/freshness utilities, verified directional matching, substitution composition, and checked symmetric unification. |
| [`Rules.v`](Rules.v) | Theorem-backed axiom and rule instances, including countermodel and trace-edge obligations. |
| [`RuleGeneration.v`](RuleGeneration.v) | Executable scans that turn an input judgment into applicable verified axiom/rule records. |
| [`GraphSearch.v`](GraphSearch.v) | Graph expansion, exact and prepared backlinks, bounded DFS, trace-witness heuristics/enumeration, and certification-aware branch search. |
| [`Certification.v`](Certification.v) | Proof that a successful generic Boolean graph check supplies the semantic data required for a `Cyclic.certificate`. |
| [`Definitions.v`](Definitions.v) | Direct AST transcription of `examples/fo.defs`. |
| [`Derived.v`](Derived.v) | Hand-proved semantic consequences of the concrete definitions, including rank and well-founded induction arguments. |
| [`Benchmarks.v`](Benchmarks.v) | Reified positive benchmark goals, their direct validity proofs, and the exact benchmark dispatcher payloads. |
| [`Search.v`](Search.v) | Public `search`, `solvedb`, `verified_proof`, and `search_sound` interface; currently combines general search with transitional benchmark fallbacks. |

## Rule-by-rule correspondence

### Axioms

| Original rule | Rocq implementation | Status |
| --- | --- | --- |
| `ex_falso_axiom` | `disequality_axiom`, `constructor_clash_axiom_left/right`, and `generate_axiom` | **Partial operational parity.** Reflexive disequality and constructor clash are soundly recognized. The Rocq clash check is broader (`Const n` versus any `Fun`) than the OCaml zero-versus-`s`/`cons` test. Generation directly handles a singleton antecedent; a disjunctive antecedent must first be split by `L.Or`. |
| `id_axiom` and `product_subsumed_upto_tags` | `product_subsetb_upto_tags`, `identity_axiom_anywhere_upto_tags`, and `identity_candidate` | **Done for the logical purpose.** A selected RHS product may be a subset of the singleton LHS product, predicate tags are ignored, Eq/Neq remain structural, and any RHS product position is scanned. Choosing the base valuation itself as witness also permits existential atoms. The exact OCaml whole-formula test and ordered-set traversal are not copied literally. |

### Repeated simplification

| Original simplifier | Rocq implementation | Status |
| --- | --- | --- |
| `simplify_eqs` | `reflexive_equality_rule`, `right_reflexive_equality_rule`, and their scans | **Partial but adequate on many generated goals.** Rocq removes one selected equality per step; OCaml filters all reflexive equalities at once. LHS scanning is restricted to a singleton antecedent, while RHS scanning is arbitrary-position. Repetition obtains the same result after LHS disjunction splitting. |
| `eq_subst_rule` | `left_equality_substitution_rule` and `find_left_equality_substitution` | **Partial.** Rocq currently recognizes only `free-variable = free-term` with the variable syntactically on the left. OCaml accepts a variable on either side and is not limited to the Rocq free-term condition. Reverse orientation and broader safe cases remain missing. |
| `eq_ex_subst_rule` | `right_existential_substitution_rule`, arbitrary-position wrapper, and `right_equality_orientation_rule` | **Partial.** Rocq solves `?e = t` and `t = ?e` when `t` is free, substitutes the remaining selected product, and removes the solved equation. OCaml also considers existential-to-existential and other less restricted equations. Those cases need an occurs/capture-safe semantic proof before enabling them. |
| `simpl_rhs` | `right_discharge_rule` and `right_discharge_candidate` | **Implemented with a sound restriction.** Predicate tags are ignored, Eq/Neq are exact, singleton LHS is required, and all RHS positions are scanned. Rocq removes one atom per step rather than all at once and requires the removed atom to be free; this prevents unsound changes between base and RHS witness valuations. |
| `bij_eqs` with `bijections = {s, cons}` | `left_function_equality_rule`, complete LHS scans, and `injective_constructorb` | **Done.** `s` and `cons` equalities are decomposed at arbitrary LHS formula/product positions. Equal arity is checked safely; the original throws an exception on malformed unequal arity. |
| `func_eqs` | `right_function_equality_rule` and complete RHS scans | **Done.** Same-named, equal-arity function equalities are replaced by pointwise equations at arbitrary RHS positions. One equality is processed per step. |
| `simplify_seq` / `wrap` | `simplification_candidate` plus priority in `expand_graph` | **Behaviorally similar, not identical.** Each graph node first tries an axiom and one simplifier; the next graph node repeats. OCaml composes repeated simplification and a following axiom application inside a wrapped rule. This difference affects fuel and branch shape, not soundness. |

### Propositional and quantifier-style rules

| Original rule | Rocq implementation | Status |
| --- | --- | --- |
| `lhs_disj_to_products` (`L.Or`) | `left_disjunction_rule` and `left_disjunction_candidate` | **Done semantically.** Rocq makes a binary first-versus-rest split; repeated applications produce all OCaml premises. |
| `rhs_conj_to_atoms` (`R.And`) | `right_conjunction_rule` and `right_conjunction_candidate` | **Partial.** Rocq performs a binary split and currently requires the LHS and RHS pieces to be entirely free. OCaml only requires pairwise-disjoint existential-variable sets among the RHS atoms, so it accepts more goals. |
| `instantiate_ex` | No connected rule | **Missing.** There is no search rule that substitutes a sequent existential variable with each available universal variable. A direct port must be reconciled with the explicit base/witness semantics; unrestricted whole-sequent substitution is not automatically sound for arbitrary reified inputs. |

### Inductive definition rules

| Original rule | Rocq implementation | Status |
| --- | --- | --- |
| `gen_right_rules` / unified `R.Unf` | `matched_right_unfold_rule`, `matched_right_unfold_at_rule`, and generator scans | **Partial.** Directional clause-head matching is verified and efficient when it succeeds. The original uses freshened cases plus `multi_unify_args`, substitutes selected goal variables, and retains residual equalities for repeated occurrences. Rocq's standalone `unify_terms` is proved sound but is not integrated to reproduce that behavior. |
| Original standard equation-building helper (inactive in the final OCaml call) | `right_unfold_rule` and `standard_right_unfold_at_rule` | **Rocq fallback.** When directional matching fails, Rocq can freshen clause variables existentially and emit explicit head equations. This is sound, but it is lower priority than LUF and is not the exact active OCaml strategy. |
| `gen_left_rules` / `L.Unf` | `left_unfold_rule`, `left_unfold_at_rule`, and all-clause/all-atom generation | **Substantially done with restrictions.** All clauses become premises, recursive bodies carry progress edges, contraction is retained, and arbitrary tagged LHS predicates can be selected. Rocq additionally requires variable-bound checks, a free RHS, and no duplicate selected tag in a skipped prefix. Therefore LHS unfolding of goals containing RHS existential variables is not yet supported. |
| `clever = compose luf ruf` | No dedicated composed candidate | **Missing as a search primitive.** Separate LUF and RUF can occur on consecutive graph nodes, but the original composition and its priority are not reproduced. |
| `fold`, followed by `dobackl` | No folding rule/generator | **Missing.** This is one of the largest remaining rule-family gaps. |

### Backlinks, substitution, and weakening

| Original component | Rocq implementation | Status |
| --- | --- | --- |
| Exact backrule | `exact_backlink_rule` and `backlink_successors` | **Done for exact labels.** All earlier nodes are considered, and the generic graph operation checks bounds and label agreement. In practice the target must match exact list/tag syntax because the rule premise itself is exact. |
| `matches_fun` / `Seq.uni_subsumption` | `checked_judgment_match` | **Narrow partial substitute.** Rocq flattens terms, performs directional matching, and then rechecks the entire substituted judgment exactly. It does not implement set-based formula/product unification, equation orientation alternatives, or selected-tag minimization. |
| `subst_rule` | `general_free_substitution_rule` and `substitution_rule_to_ancestor` | **Partial.** Multiple free-variable bindings are supported and theorem-backed, but substitutions must satisfy `free_substitutionb`; broader original unifiers are not accepted. |
| `weaken` | `prefix_weakening_rule` and `weakening_rule_to_ancestor` | **Partial.** It only recognizes extra atoms as a suffix after an exactly sized prefix in a singleton LHS product, with the RHS otherwise matching. OCaml uses general set subsumption and can remove non-prefix extras. |
| `dobackl` | Exact plus prepared successor generation in `GraphSearch.v` | **Partial.** Explicit proof nodes are inserted before backlinking, which matches the original architecture, but discovery is much less complete. |

## Formal semantics and trusted boundary

The original implementation is an executable calculus. The Rocq port adds a
mathematical model that is not present as executable code in
`src/firstorder`:

1. `value` is a free algebra of constants and named function applications.
2. A valuation assigns values to both free and existential variables.
3. LHS atoms use the base valuation; a chosen RHS product shares one
   existential witness valuation.
4. `models` gives both clause introduction and ranked inversion of inductive
   predicates. Recursive body predicates must have smaller ranks.
5. Antecedent predicate tags select semantic ranks for cyclic traces; tags do
   not change atom truth.

This explicit semantics is a major strength: it reveals where some unrestricted
OCaml rewrites rely on input invariants that the parser/prover assumes but does
not express in types. The Rocq implementation often uses a stricter side
condition rather than formalizing an unsound rule over all reified judgments.

Every `Cyclic.rule_instance` contains both:

- a theorem from valid premises to a valid conclusion; and
- a countermodel step proving that a false conclusion yields a false premise
  connected by a rank-respecting trace edge.

[`Certification.v`](Certification.v) proves that a successful
`Cyclic.raw_check` supplies the structural, reachability, countermodel, and
trace-witness evidence used by the generic cyclic soundness theorem.

At the time of this audit:

- there are no `Admitted`, `admit`, `Abort`, or project-declared `Axiom`
  commands in `FirstOrder/*.v`;
- some rule proofs intentionally import standard classical choice,
  classical logic, and functional extensionality from Rocq's standard
  library;
- `search_sound` proves that every `solvedb = true` result denotes a valid
  input judgment, after transport across proved normalization equivalence.

Thus missing automation causes **false negatives**, not false proofs.

## Representation differences that affect search

The original `Prod` and `Form` modules use ordered finite sets. Rocq uses
lists and proves that `nodup` normalization preserves truth.

Consequences:

- duplicate atoms/products are removed, but input order is retained rather
  than sorted canonically;
- semantic rules often scan arbitrary positions, but exact judgment equality
  and prepared backlinks remain list-order sensitive;
- source-order clause/predicate traversal can differ from OCaml set-order
  traversal;
- a semantically identical permutation can therefore lead to a different
  search tree or prevent an exact backlink.

This is a completeness/performance issue, not a soundness issue.

## Search and certification status

Implemented search features:

- first-open-node graph expansion;
- axiom and repeated simplification priority;
- exact and restricted prepared backlinks;
- generation of all currently connected ordinary rule candidates;
- bounded depth-first exploration;
- a certification-aware DFS that continues to later branches when a
  syntactically closed graph fails the global cyclic check;
- a deterministic trace-witness heuristic;
- finite exhaustive fallback enumeration of node tags and bounded
  potentials;
- conversion of a successful raw check into a checked certificate.

Important differences from the OCaml `Prover.idfs`:

- Rocq fuel is consumed for each whole graph-state/open-node expansion. For a
  multi-premise rule, closing sibling premises consumes fuel sequentially.
  OCaml passes the same decreased depth budget independently to sibling
  subgoals, so its bound behaves more like proof height.
- The Rocq public default is depth/fuel 1 through 11. Some genuine graph
  certificates already require a larger bound.
- Missing rule families and narrower backlinks make search less complete.
- Trace-witness enumeration can be exponential.
- There is no wall-clock timeout inside Gallina; bounded `None` means only
  "not found within this bound."

## Benchmark status

The following enabled OCaml benchmarks are reified exactly in
[`Benchmarks.v`](Benchmarks.v):

| Benchmark | Goal | Direct Rocq validity theorem | General graph-search status |
| --- | --- | --- | --- |
| 01 | `O(x) |- N(x)` | `benchmark_01_valid` | During this audit, `certify_searched_graph 16` reduced to `Some`/`true` in about 3.4 seconds. This is not yet a committed regression theorem. |
| 02 | `E(x) \/ O(x) |- N(x)` | `benchmark_02_valid` | No persisted successful general-search test. An audit evaluation at fuel 18 did not finish within 60 seconds; this is not evidence of invalidity. |
| 04 | `N(x) |- O(x) \/ E(x)` | `benchmark_04_valid` | During this audit, `certify_searched_graph 18` reduced to `Some`/`true` in about 1.8 seconds. This is not yet a committed regression theorem. |
| 05 | `N(x) & N(y) |- Q(x,y)` | `benchmark_05_valid` | No persisted successful general-search test. |
| 07 | `N(x) |- ADD(x,0,x)` | `benchmark_07_valid` | No persisted successful certified-search test in the source. |
| 08 | `N(x) & N(y) & ADD(x,y,z) |- N(z)` | `benchmark_08_valid` | No persisted successful general-search test. |
| 09 | `N(x) & N(y) & ADD(x,y,z) |- ADD(x,s(y),s(z))` | `benchmark_09_valid` | No persisted successful general-search test. |
| 13 | `N(y) & N(x) |- H(x,y)` | `benchmark_13_valid` | No persisted successful general-search test. |
| 14 | `N(y) & N(x) |- N2(x,y)` | `benchmark_14_valid` | No persisted successful general-search test. |

The direct theorems use hand-proved semantic lemmas from [`Derived.v`](Derived.v),
including rank induction and a separate hydra measure. They establish that the
goals are mathematically valid, but they do not demonstrate that the generic
rule generator discovered cyclic proof graphs.

[`Search.v`](Search.v) tries general graph search before the exact benchmark
fallback at every depth. If general search does not return, `theorem_strategy`
recognizes one of the nine normalized benchmark judgments and packages its
already proved theorem as a one-node checked certificate. Therefore
`search_solves_all_positive_benchmarks` is valid and proof-producing, but is
currently a dispatcher-inclusive coverage test.

The disabled original cases 03, 06, 10, 11, 12, and 15 are not represented as
bounded non-success regressions in `FirstOrder/`.

Existing general-search regression coverage includes a non-benchmark `L.Or`
tree whose two branches close by generated identity. A malformed-certificate
rejection regression is still absent.

## What is complete enough to reuse now

The following parts are already good foundations for continued work:

1. The syntax and semantics modules.
2. Normalization with semantic preservation.
3. The rule-record design with local countermodel/trace proofs.
4. Identity, contradiction, propositional splitting, equality
   simplification, RHS discharge, constructor equality rules, substitution,
   and the existing unfolding kernels.
5. The FirstOrder-local reflection from `raw_check = true` to a semantic
   cyclic certificate.
6. The `verified_proof`/`search_sound` public safety contract.
7. The transcription of `fo.defs` and all nine positive validity proofs.

These should be extended rather than replaced.

## Work not yet done, in recommended order

1. **Remove dependence on the exact benchmark dispatcher.** Add persisted
   general-search certificate tests per benchmark, improve search until the
   supported goals are found, then delete the theorem table from
   `search_at_depth`.
2. **Implement full backlink companion discovery.** Port the behavior of
   `Prod/Form/Seq.uni_subsumption`, arbitrary set weakening, substitution,
   and trace-tag minimization. This is likely the most important cyclic-search
   completeness improvement.
3. **Reproduce right-unfold `multi_unify_args`.** A verified result should
   include both the chosen substitution and residual equalities for repeated
   variables, then apply it at every RHS position.
4. **Implement folding and fold-then-backlink.** This entire original search
   family is currently absent.
5. **Formalize a sound existential-instantiation rule** compatible with the
   explicit base/witness semantics, then connect it at the original priority.
6. **Generalize existing partial rules.** In particular: reverse-orientation
   LHS equality substitution, safe broader RHS existential equations,
   pairwise-disjoint-existential `R.And`, and LUF with safe RHS existential
   variables.
7. **Reproduce the composed LUF-then-RUF candidate and search scheduling.**
8. **Redesign fuel to approximate OCaml proof depth**, or clearly expose both
   a height bound and a total-expansion bound.
9. **Add the textual frontend** if command-line feature parity is a goal:
   parsers, named-variable handling, definition loading, pretty printing,
   timeout integration, and proof statistics.
10. **Expand regression coverage:** all positive goals through general
    search, disabled cases as bounded non-success only, malformed graph and
    trace-witness rejection, permutation invariance, and all safe variable
    side-condition boundaries.

## Note on the existing implementation plan

[`IMPLEMENTATION_PLAN.md`](IMPLEMENTATION_PLAN.md) is useful historical design
documentation, but some checklist entries are stale:

- checked symmetric `unify_terms` now exists, although it is not integrated
  into right unfolding;
- finite trace-witness construction and checking now exist;
- certification-aware DFS now continues after an invalid closed graph;
- several simplifiers listed as future work are now implemented;
- the actual current fallback rule order is matched RUF, LUF, then standard
  equation-producing RUF;
- nine benchmark `true` values still include the transitional dispatcher and
  should not be described as nine general-search successes.

This audit should be treated as the current status reference until that plan
is refreshed.

## Reproducible checks

From `Rocq-copy/`:

```sh
make -B -j2
rg -n '\b(Admitted|admit|Abort|Axiom)\b' FirstOrder --glob '*.v'
git diff -- Cyclic LTL
```

Useful Rocq queries are:

```coq
From CyclistRocq.FirstOrder Require Import Search GraphSearch Benchmarks.

Print Assumptions search_sound.
Eval vm_compute in map (solvedb default_config) positive_goals.

Eval vm_compute in
  match certify_searched_graph 16 (normalize_judgment benchmark_01) with
  | Some _ => true | None => false
  end.

Eval vm_compute in
  match certify_searched_graph 18 (normalize_judgment benchmark_04) with
  | Some _ => true | None => false
  end.
```

The last two computations exercise general graph search. The nine-element
`solvedb` computation exercises the public API, including its current
benchmark fallback.
