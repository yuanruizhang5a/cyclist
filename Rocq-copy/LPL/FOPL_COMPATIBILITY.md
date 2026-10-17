# Preservation of G3FOPL

The immutable reference is `../LPL-old/`. Production FOPL code now lives in
`FOPL/` and instantiates the shared G3PPL syntax, semantics, progress, rule,
and certification modules. Its original 15 benchmark units are retained in
`FOPL/Benchmarks/` with the same mathematical statements and proof modes.

## Mechanized preservation

[FOPL/Compatibility.v](FOPL/Compatibility.v) compares against the old syntax,
semantics and progress modules staged under `FOPL/LegacyReference/`.
The three reference implementations differ from the immutable snapshot only
in imports. They share `FOPL/Signature.v`, whose bytes are checked against the
frozen signature; a second identical signature file is unnecessary.
The extra progress reference permits checking the actual old counterexample
and minimum definitions, rather than a newly reconstructed specification.
Production modules do not depend on this reference or the compatibility module.

For arbitrary original signatures and models, the compiled proof provides:

| Property | Evidence |
| --- | --- |
| Terms, programs, formulas, updates, labels, occurrences, judgments | Structural translations, with an empty relation context for every legacy judgment |
| Formula/program well-formedness, pure recognition, arities and labels; forward tag/judgment admissibility | `translate_term_wfb`, `translate_pureb`, `translate_formula_program_wfb`, `translate_update_wfb`, `translate_label_wfb`, `translate_label_nonempty`, `translate_traceable`, `translate_tags`, `translate_judgment_wfb` |
| Term/update/label meanings | `translate_term_eval`, `translate_update_eval`, `translate_label_eval` |
| Full formula/program meanings, including empty traces and raw ill-formed syntax | `formula_program_semantics`, proved by simultaneous induction |
| Assertion and guarded sequent meanings | `labelled_semantics`, `admissibility_preserved`, `denotation_preserved` |
| Validity in both directions | `validity_preserved`, including a mapping back from every new world |
| Actual execution and counterexample histories | `execution_sequences_preserved`, `counterexamples_preserved` |
| Possible measures, attained minima and fallback | `measures_preserved`, `minima_preserved` |
| Occurrence and context rank lookup | `occurrence_ranks_preserved`, `context_ranks_preserved` |

These are checked theorems, not assumed interface facts or a test of equivalent
pretty-printing. New relational judgments are outside the translated legacy
image; the old image's denotation is unchanged.

## Ownership of the migrated rules

Common Boolean, test, sequence/choice/star, first-state/atom-head, temporal,
structural, and backlink kernels are defined once in `Rules.v`.
`FOPL/Rules.v` binds their relational context to the empty legacy context and
adds the assignment and quantifier rules. Assignment descent and reversible
FOPL state-switch arguments use the same core counterexample rank and graph
kernel. `FOPL/Certification.v` instantiates the shared reflection proof.

The first-order atom-head rule is the generic atom-head rule at the
predicate/equality payload instance. First-order assignment rules preserve their
update-label source and premise shape; they introduce no transition assumption.
The 50 original exact premise-shape checks and all original rejection checks
remain in `FOPL/Benchmarks/RuleCoverage.v`.

## Representation and proof-script adaptations

- `Pred p ts` builds `Atom (Predicate p ts)`; `Equal a b` builds
  `Atom (Equality a b)`; `Assign x t` builds `Atomic (Assignment x t)`.
  Payloads belong to FOPL and remain available to its structural traversals.
- `All` is `Extension` and `Ex x a` is `Neg (Extension x (Neg a))`.
  Capture-avoiding substitution descends through the primitive encoding.
- Derived Boolean, temporal and modal spellings are definitions over the eight
  primitives. Their expansions are now identical syntax. Therefore
  `translate_traceable`, occurrence/context well-formedness, and
  `translate_judgment_wfb` preserve successful legacy checks forward.
  Reflection is intentionally absent: an old ordinary negation can translate
  to the same expanded dual suffix as an old `DualSuffix`. Formula/program
  payload checks, purity, labels and meanings still have equality/equivalence
  theorems. No rejection benchmark was removed.
- A shared judgment contains a relation list; every old judgment uses `[]`.
  Direct semantic benchmark proofs explicitly discharge its trivial empty
  relational premise. This does not weaken any old sequent or invariant.
- The legacy `switch_denote` transport theorem is stated for that empty-relation
  image. Generic fresh-world transport handles relational contexts independently.
- Generic/FOPL proof modules pass the same progress instance through the rule
  kernel, generation, and certification. Reapplying the graph functor would
  create incompatible inductive record types.
- `Semantics.TraceAlgebra` owns polymorphic overlap, composition and finite
  powers. `TraceSafety.v` supplies invariant lemmas over those same operations;
  its compatibility names are thin aliases.
- FOPL generation and certification export the supplied kernel directly,
  avoiding another alias of its generative factory. Clients retain the
  original kernel module for qualified access to first-order rules; the
  adapters continue to export those rules for unqualified use.

The old 11-node/one-tag star proof, 12-node/two-tag renaming proof, six-node
assignment-change proof, and complex invariant statements are preserved.
The two complex invariants remain direct semantic proofs over every visited
state and arbitrary finite stopping points. The cyclic proofs retain their
first-state observation claims. Current timings and kernel checks are recorded
in [BENCHMARK_RESULTS.md](BENCHMARK_RESULTS.md) and [VALIDATION.md](VALIDATION.md).
