# Theory-to-Code Tutorial for `Rocq-copy/FirstOrder`

## Summary

Create an English, advanced-Rocq tutorial that explains every `FirstOrder/*.v` module and the necessary `Cyclic` framework machinery. Each topic will follow:

**Mathematical intention → Rocq realization → soundness and limitations**

The tutorial will document source revision `08f6cd8834a3fc22088a064025abb9ee65c7f545`, target roughly 45–65 pages without a hard limit, and avoid modifying any Rocq implementation or public interface.

## Deliverables and Order

1. Create `Rocq-copy/FirstOrder/Learn/` and `Learn/materials/`.
2. Before authoring anything else, save this complete plan as `Learn/TUTORIAL_PLAN.md`.
3. Create:

   - `Learn/rocq-firstorder-tutorial.tex`
   - `Learn/rocq-firstorder-tutorial.pdf`
   - `Learn/materials/references.bib`
   - `Learn/materials/README.md`
   - `Learn/compile.log`

4. Do not download paper PDFs; `materials/` will contain an annotated reading list, stable links, and complete BibTeX metadata.
5. Leave `FirstOrder/*.v`, `Cyclic/*.v`, `_CoqProject`, and all public APIs unchanged.

## Tutorial Content

- Begin with the dependency map and theorem-producing path:
  \[
  \text{judgment}\to\text{rule generation}\to\text{proof graph}
  \to\text{checks}\to\text{certificate}\to\text{semantic validity}.
  \]
- Explain the mathematical object language before `Syntax.v`: two variable classes, free term algebra, tagged predicate atoms, conjunctions as products, DNF formulae, sequents, Horn-style inductive clauses, substitutions, freshness, and tag preparation.
- Explain `Semantics.v` from the mathematical model first: constructor-tree values, valuations, ranked predicate interpretations, clause introduction/inversion, existential witnesses shared by a selected right-hand product, judgment validity, and trace ranks.
- Cover the required `Cyclic/Relations.v` and `Cyclic/Framework.v` concepts: local rule soundness, countermodel propagation, non-increasing/progressing tag pairs, finite proof graphs, backlinks, relational closure, trace witnesses, and the lexicographic infinite-descent proof behind `certificate_sound`.
- Present every implemented rule family mathematically with `\infer` before showing its Rocq record:

  - identity modulo tags and ex-falso;
  - left disjunction and restricted right conjunction;
  - reflexive equality elimination;
  - left equality substitution and right existential solving;
  - right discharge and constructor-equality decomposition;
  - explicit weakening and free-variable substitution;
  - matched and equation-producing right unfolding;
  - ranked left unfolding and exact backlinks.

- Explain `Automation.v` as verified executable infrastructure: normalization, Boolean reflection lemmas, variable analysis, directional matching, substitution composition, occurs checking, and symmetric unification.
- Explain `RuleGeneration.v`, `GraphSearch.v`, and `Certification.v`: candidate ordering, first-open-node DFS, prepared backlinks, closed-graph versus certified-proof distinction, trace-witness heuristics/enumeration, Boolean reflection, and certificate construction.
- Explain `Definitions.v` and `Derived.v` mathematically: the 19 inductive definitions, introduction/inversion lemmas, rank induction, rank sums, value-depth measures, and the hydra-style argument.
- Explain `Benchmarks.v` and `Search.v`, including the precise one-way contract
  \[
  \mathsf{solvedb}(c,J)=\mathsf{true}\Longrightarrow\mathsf{Valid}(J),
  \]
  and clearly distinguish general graph search from the transitional theorem-backed benchmark dispatcher.
- Include a complete vertical slice for `benchmark_01`, \(O(x)\vdash N(x)\), using the verified 15-node graph:
  `L.Unfold → Eq subst/Simpl = → R.Unfold/match → Id/modulo-tags → Weaken → Subst → Backlink`.
  Relate this cyclic derivation to the direct rank-induction proof through `odd_natural`.
- Finish with implementation limitations, trusted assumptions, a mathematical-to-Rocq correspondence table, module/symbol index, and theorem-first extension checklist. Explicitly cover missing folding and existential instantiation, restricted matching/conjunction/backlinks, bounded non-success, missing parser/CLI, and incompleteness versus soundness.

## Typesetting and References

- Use `pdflatex` through `latexmk`, standard installed packages, `listings` for Rocq, `proof` for `\infer`, and TikZ for dependency/proof-graph diagrams.
- Include a table of contents, cross-references, exact module/symbol references, selected code excerpts, and readable mathematical derivations. No code excerpt will appear without its theoretical interpretation.
- Curate at least these references:

  - Brotherston, “Cyclic Proofs for First-Order Logic with Inductive Definitions” ([DOI](https://doi.org/10.1007/11554554_8)).
  - Brotherston and Simpson, “Sequent Calculi for Induction and Infinite Descent” ([DOI](https://doi.org/10.1093/logcom/exq052)).
  - Brotherston, Gorogiannis, and Petersen, “A Generic Cyclic Theorem Prover” ([DOI](https://doi.org/10.1007/978-3-642-35182-2_25)).
  - Lee, Jones, and Ben-Amram, “The Size-Change Principle for Program Termination” ([DOI](https://doi.org/10.1145/360204.360210)).
  - The official [Rocq 9.1 reference manual](https://rocq-prover.org/doc/v9.1/refman/index.html) as supporting documentation.

## Validation

- Record that the current baseline `make -C Rocq-copy -B -j2` succeeds and rerun it after document generation.
- Reproduce the nine public benchmark results, the 15-node `benchmark_01` certified graph, and `Print Assumptions` results used in the trust discussion.
- Compile with:
  `latexmk -pdf -interaction=nonstopmode -halt-on-error rocq-firstorder-tutorial.tex`
  with at most three diagnose-and-repair attempts. Do not run `latexmk -C` or permanently delete files.
- Verify:

  - the PDF exists, is nonempty, and has a plausible page count;
  - citations and cross-references are resolved;
  - no `??`, `[?]`, `[VERIFY]`, missing-file errors, or severe overfull boxes remain;
  - all fonts are embedded;
  - extracted PDF text contains every `FirstOrder` module and all major mathematical sections;
  - representative title, semantic, rule, cyclic-graph, benchmark, and bibliography pages render correctly.

## Assumptions

- Readers already know first-order logic and advanced Rocq; no general Gallina or tactic tutorial is included.
- All eleven `FirstOrder` modules receive coverage, while the generic `Cyclic` modules are explained only where required by the FirstOrder soundness path.
- The current checked source is authoritative; existing audit and implementation-plan documents are supporting context and may contain historical or stale descriptions.
- External references provide conceptual context, not claims that the local implementation has features absent from its source.
