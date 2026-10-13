# Theory-to-Code Tutorial for `Rocq-copy/SP`

## Summary

Create a comprehensive, English-language tutorial for separation-logic researchers who already know Rocq. The document explains each mathematical construction before showing its Rocq realization, covers every `SP` module and the necessary `Cyclic` framework dependencies, and documents source commit `08f6cd8834a3fc22088a064025abb9ee65c7f545` without changing definitions, proofs, search behavior, or public interfaces.

## Deliverables and order

1. Create `Rocq-copy/SP/Learn/` and `Rocq-copy/SP/Learn/materials/`.
2. Save this plan as `Rocq-copy/SP/Learn/TUTORIAL_PLAN.md` before authoring the tutorial.
3. Create `rocq-sp-tutorial.tex`, `rocq-sp-tutorial.pdf`, `materials/references.bib`, `materials/README.md`, and `compile.log`.
4. Do not download paper PDFs. The materials directory contains an annotated index and complete BibTeX metadata only.

## Tutorial content

- Begin with a dependency map and the theorem-producing path
  `judgment -> generator -> proof graph -> checks -> certificate -> semantic validity`.
- Present the mathematics first: finite partial heaps, disjoint union, exact points-to ownership, separating conjunction, symbolic-heap disjunctions, existential witnesses, ranked inductive predicates, tag bounds, ordinal constraints, and entailment validity.
- Map those definitions directly to `Syntax.v` and `Semantics.v`, including
  `h |= P * Q` iff there are disjoint `h1,h2` with `h = h1 \uplus h2`, `h1 |= P`, and `h2 |= Q`, and explain the finite approximants behind `predicate_holds_rank`.
- Explain generic cyclic theory before the Rocq records: rule validity, countermodel propagation, non-increasing and progressing trace pairs, relational closure, global progress, trace witnesses, and the lexicographic infinite-descent proof in `certificate_sound`.
- State every implemented inference rule mathematically before its theorem and packaged rule/axiom: identity, tag erasure, ex falso, predicate introduction, left disjunction, right choice, and exact backlinks.
- Cover executable generation and search: ordered one-way unification, candidate priority, first-open-node DFS, backlinks, witness enumeration, iterative deepening, and the one-way meaning of `solvedb`.
- Explain the reflection bridge in `Certification.v`, distinguishing the additional relational acceptance check from the witness used to construct semantic certificate evidence.
- Give a vertical slice for `benchmark_base_19_1`, from
  `x != z /\ x |-> y * ls(y,z) |- ls(x,z)` through the recursive `ls` clause to a one-node certified proof and `benchmark_base_19_search_valid`.
- Cover `Definitions.v`, `Benchmarks.v`, `Examples.v`, `Tests.v`, and `Automation.v`, distinguishing the artificial cyclic teaching graph from genuine search successes.
- Include a limitations table covering identity normalization, ordered matching, a single right-disjunct choice, exact backlinks, unsupported generators returning `None`, and failure as bounded non-success rather than invalidity.
- Finish with a module/symbol index, a mathematical-to-Rocq correspondence table, a trust/assumption summary, and a theorem-first extension checklist.
- Use the recurring pattern “Mathematical intention” -> “Rocq realization” -> “Soundness and limitations.” No code excerpt appears without a theoretical interpretation.

The target length is approximately 35--50 pages, with no hard page limit.

## Typesetting and references

- Use `pdflatex` and available packages including `amsmath`, `amssymb`, `mathtools`, `proof`, `listings`, `xcolor`, `booktabs`, `longtable`, `hyperref`, `microtype`, and `tikz`.
- Define a Rocq-specific listings style and use `\infer` for proof rules; do not depend on `mathpartir` or `cleveref`.
- Include a table of contents, cross-references, source-symbol citations, proof-graph diagrams, and selected exact code excerpts.
- Curate four references: Reynolds on separation logic; Brotherston, Distefano, and Petersen on cyclic separation-logic entailments; Brotherston and Simpson on induction and infinite descent; and Brotherston, Gorogiannis, and Petersen on a generic cyclic prover.
- Explain the relevance of each source in `materials/README.md`; place complete metadata in `materials/references.bib`.

## Validation

- Confirm the baseline with `make -C Rocq-copy` before authoring.
- Compile with `latexmk -pdf -interaction=nonstopmode -halt-on-error`, allowing at most three diagnose-and-repair attempts and retaining `compile.log`.
- Do not run `latexmk -C` or permanently delete prior artifacts.
- Verify a nonempty PDF and plausible page count; full module-map coverage; resolved citations and cross-references; absence of `??`, `[?]`, `[VERIFY]`, missing-file errors, and severe overfull boxes; embedded fonts; expected major sections in extracted text; and visual quality of first, middle, cyclic-proof, and bibliography pages.
- Re-run the Rocq build after generation to confirm that implementation files remain unaffected.

## Assumptions

- Readers know Rocq and separation logic; basic Gallina syntax is not taught.
- The tutorial documents the current, deliberately incomplete implementation rather than the broader aspirations in `IMPLEMENTATION_PLAN.md`.
- Standard-library classical assumptions reported by `Print Assumptions` are stated and checked against compiled code.
- No parser, CLI, OCaml implementation tutorial, or new proof rule is added.
