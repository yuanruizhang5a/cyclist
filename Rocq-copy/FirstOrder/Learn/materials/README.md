# Reading material for the FirstOrder tutorial

This directory intentionally contains no downloaded papers.  The tutorial is
source-led: the checked Rocq files at revision
`08f6cd8834a3fc22088a064025abb9ee65c7f545` are authoritative, while the items
below supply conceptual and historical context.  Full citation metadata is in
[`references.bib`](references.bib).

## Annotated reading list

1. **James Brotherston, “Cyclic Proofs for First-Order Logic with Inductive
   Definitions” (TABLEAUX 2005).**  The closest proof-theoretic background for
   inductive predicates, finite regular derivations, traces, and the global
   progress condition.  The local implementation is not claimed to implement
   the paper's entire calculus.  Stable link:
   <https://doi.org/10.1007/11554554_8>.

2. **James Brotherston and Alex Simpson, “Sequent Calculi for Induction and
   Infinite Descent” (Journal of Logic and Computation 21(6), 2011).**  Places
   cyclic infinite descent beside ordinary induction and is useful for
   understanding why a locally sound finite graph needs a global trace
   condition.  Stable link: <https://doi.org/10.1093/logcom/exq052>.

3. **James Brotherston, Nikos Gorogiannis, and Rasmus Lerchedahl Petersen, “A
   Generic Cyclic Theorem Prover” (APLAS 2012).**  Describes the generic
   Cyclist architecture and the separation between object-logic rules, proof
   graphs, backlinking, and global validation.  The Rocq code documented here
   is a proof-producing reimplementation with its own precise interfaces.
   Stable link: <https://doi.org/10.1007/978-3-642-35182-2_25>.

4. **Chin Soon Lee, Neil D. Jones, and Amir M. Ben-Amram, “The Size-Change
   Principle for Program Termination” (POPL 2001).**  Background for composing
   local non-increase/decrease relations and rejecting loops without a strict
   descent.  It illuminates `Cyclic/Relations.v`; it is not an assertion that
   the file is a verbatim implementation of the POPL algorithm.  Stable link:
   <https://doi.org/10.1145/360204.360210>.

5. **The Rocq Prover Reference Manual, version 9.1.**  Supporting documentation
   for records, dependent sums, recursive definitions, Boolean computation,
   modules/functors, `vm_compute`, `Print Assumptions`, and the kernel trust
   model used throughout the tutorial.  Stable link:
   <https://rocq-prover.org/doc/v9.1/refman/index.html>.

## Source-reading order

For readers following the tutorial at the code level, the shortest coherent
path is:

`FirstOrder/Syntax.v` → `FirstOrder/Semantics.v` →
`Cyclic/Relations.v` → `Cyclic/Framework.v` → `FirstOrder/Rules.v` →
`FirstOrder/Automation.v` → `FirstOrder/RuleGeneration.v` →
`FirstOrder/GraphSearch.v` → `FirstOrder/Certification.v` →
`FirstOrder/Search.v`.

Read `FirstOrder/Definitions.v`, `FirstOrder/Derived.v`, and
`FirstOrder/Benchmarks.v` alongside the final four steps for concrete examples.
