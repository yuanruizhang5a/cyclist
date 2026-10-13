# Reading list for the `SP` theory-to-code tutorial

This directory intentionally contains no downloaded papers. The tutorial's
four references are listed here with stable access links and complete BibTeX
metadata in `references.bib`.

1. **John C. Reynolds, “Separation Logic: A Logic for Shared Mutable Data
   Structures” (LICS 2002).** [Author PDF](https://www.cs.cmu.edu/~jcr/seplogic.pdf)
   and [DOI](https://doi.org/10.1109/LICS.2002.1029817). This is the semantic
   reference for finite heaps, exact singleton points-to, `emp`, and separating
   conjunction. It provides the mathematical vocabulary used to read
   `SP/Semantics.v`.

2. **James Brotherston, Dino Distefano, and Rasmus Lerchedahl Petersen,
   “Automated Cyclic Entailment Proofs in Separation Logic” (CADE-23, 2011).**
   [Springer DOI](https://doi.org/10.1007/978-3-642-22438-6_12). This paper is
   the closest methodological reference for cyclic entailment proof search over
   inductive separation-logic predicates. It motivates the rules, backlinks,
   trace annotations, and benchmark lineage discussed in the tutorial.

3. **James Brotherston and Alex Simpson, “Sequent Calculi for Induction and
   Infinite Descent” (Journal of Logic and Computation 21(6), 2011).**
   [University of Edinburgh record](https://www.research.ed.ac.uk/en/publications/sequent-calculi-for-induction-and-infinite-descent)
   and [DOI](https://doi.org/10.1093/logcom/exq052). This supplies the proof-
   theoretic background for representing regular infinite derivations by finite
   cyclic graphs subject to a global progress condition.

4. **James Brotherston, Nikos Gorogiannis, and Rasmus Lerchedahl Petersen,
   “A Generic Cyclic Theorem Prover” (APLAS 2012).**
   [UCL record](https://discovery.ucl.ac.uk/id/eprint/10140071/) and
   [DOI](https://doi.org/10.1007/978-3-642-35182-2_25). This is the direct
   architectural context for the reusable `Cyclic` layer: object logics provide
   judgments, denotations, tags, ranks, and rule instances, while the framework
   provides graph checking and a generic soundness argument.

The local source revision documented by the tutorial is
`08f6cd8834a3fc22088a064025abb9ee65c7f545`.
