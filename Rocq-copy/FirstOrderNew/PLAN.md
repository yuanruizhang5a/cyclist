# First-order theory reimplementation

## Agreed scope

Derive this implementation from `src/firstorder`, the relevant original generic
proof operations, and `examples/fo.defs`. Use `Rocq-copy/LTL` as the certificate
integration example. The existing first-order implementation is not a reference.
Keep the contents of `Rocq-copy/Cyclic` and `Rocq-copy/LTL` unchanged.

The FO core is standalone; only adapter/certification modules import Cyclic.
Implement the intended sound calculus, document corrections to original defects,
and include generic proof-producing bounded search.

Semantics uses arbitrary nonempty first-order domains, the constructor laws
needed for `0`, `s`, and `cons`, and simultaneous least fixed points of positive
clauses. Free variables are universally quantified. Existential variables have
scope local to each right-hand product. Antecedents contain only free variables;
left unfolding freshens and universalizes clause-local variables.

Undefined predicates are errors. Preserve the literal `ADD_2` reference in the
source definition library and diagnose it; do not invent a definition.

## 1. Specification and source correspondence

The original syntax is positive DNF: integer constants, variables and function
applications; equality, disequality and tagged inductive atoms; finite conjunction
products and finite disjunction formulas; pairs of formulas as sequents; ordered
positive inductive clauses, including mutual recursion.

Map terms, atoms, products, formulas, sequents, clauses, definitions, matching,
rules and search to the original source files. Record original behavior, corrected
behavior, justification and regression examples for each deviation. Initial
entries are the reversed DNF identity check, disequality parsing as equality,
incomplete recursive variable collection, ineffective tag-insensitive equality,
missing signature/freshness validation, unbounded simplification, and unjustified
trace annotations.

## 2. Independent syntax and operations

- `Syntax.v`: variable classes, integer terms, tagged atoms, products, DNF,
  sequents, exact comparison, tag erasure and set-like normalization.
- `Substitution.v`: simultaneous substitution, recursive variable collection,
  freshness and renaming.
- `Definitions.v`: ordered clauses, signature and scope validation, freshening.
- `Matching.v`: directional matching, symmetric equality matching, repeated-head
  matching with equality constraints, tagged subsumption.
- `Input.v`: original input forms, pure fresh-name/tag generation, diagnostics.

Prove comparison reflection, freshness, substitution transport and normalization
properties. Preserve directional matching rather than replacing it with MGU
unification.

## 3. Semantics and inductive derivations

`Semantics.v` defines admissible models, valuations, satisfaction and sequent
validity independently of Cyclic. Prove the substitution/renaming lemmas and
least-fixed-point interpretation of finite positive derivations. Tags do not alter
logical truth. Connect ordinary DNF validity to the selected antecedent-product
countermodel representation needed for trace descent.

`SourceDefinitions.v` transcribes `examples/fo.defs`. The full library must report
undefined `ADD_2`; examples use explicitly validated closed subsets.

## 4. Rule schemas and local proofs

Implement `Rules.v`, `Simplification.v`, and `RuleGeneration.v` covering identity,
contradiction, all six simplifications, left disjunction, guarded right conjunction,
existential instantiation, right unfolding (including repeated head parameters),
contraction left unfolding, folding, weakening, substitution and exact backlinks.

For each rule establish ordinary soundness, scope/well-formedness preservation,
countermodel transport, and rank obligations for certified trace annotations.
Bound simplification and distinguish exhaustion from success. Generated
applications must instantiate approved rule schemas.

## 5. Early rank-proof gate

Implement `Rank.v` before automated cyclic search. The initial candidate is finite
derivation-tree size, aggregated for occurrences sharing a tag. Test and prove
its behavior for shared tags, contraction copies, branching clause bodies,
mutual recursion, DNF selection, duplicate collapse, backwards substitution,
weakening and folding. Introduce justified occurrence metadata or trace side
conditions if required, recording the reason in the compatibility ledger.

Do not assert nonincrease/progress merely from matching tag names. Only proved
tag pairs enter certified edges. Establish valid-pair nonincrease and
progressing-pair strict decrease before using them in search.

## 6. Adapter and reusable certification

- `Adapter.v` instantiates `Framework.THEORY` and `Framework.Make`.
- `Certification.v` translates native rules into framework instances and proves
  reusable graph certification lemmas.

Supply both ordinary rule soundness and the informative countermodel witnesses
required by `rule_counter_step`. Derive root bounds/equality, aligned node labels,
false-node advancement/liveness and witness-transition evidence. Assemble the
semantic certificate rather than treating raw Boolean acceptance as sufficient.

## 7. Generic search and routing witness synthesis

`Search.v` preserves the original priority: axioms, simplification, then backlink,
left disjunction, existential instantiation, right conjunction, right unfolding,
combined left/right unfolding, left unfolding, and fold-then-backlink.

Use iterative deepening, deterministic enumeration, explicit administrative
weakening/substitution steps, and resource limits. Keep FO search descriptions
separate from framework proof objects; the adapter supplies graph execution and
certification. `CertifiedSearch.v` returns success only with a checked certificate
for the requested root.

Synthesize optional tags per node, validate transitions, solve strict potential
constraints, and backtrack if a candidate graph is not certifiable. Exhaustion
means not proved, not false. The framework's fixed nodewise routing witness is
more restrictive than the original relational trace condition.

## 8. Examples, benchmarks and checks

Implement `Examples.v` and `Benchmarks.v`. Begin with acyclic and genuinely cyclic
certificates, then exercise mutual recursion, branching bodies, shared tags,
folding and substitution backlinks. Run all nine active `benchmarks/fo/*.tst`
goals through the same generic search implementation. Discuss any necessary
scope change before relaxing this acceptance target.

Add focused regressions for source defects, malformed inputs/graphs and flat
cycles. Completion requires:

1. Standalone core builds without Cyclic/LTL imports.
2. Integration compiles with Rocq 9.1.
3. Search success implies native semantic validity through a certificate.
4. No `Admitted` or new project-defined axioms; audit standard-library classical
   and choice assumptions using `Print Assumptions`.
5. Compiled results pass `rocq check`.
6. Cyclic and LTL baseline contents remain unchanged.

Provide a local `Makefile`, `_CoqProject`, and `README.md`. Prerequisite rebuilds
are staged outside the frozen directories. Execution order is specification,
core, semantics, local rules/ranks, certification, search, then benchmark checks.
