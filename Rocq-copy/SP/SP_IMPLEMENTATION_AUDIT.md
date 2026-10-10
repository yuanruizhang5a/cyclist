# Separation-Logic Implementation Audit

This audit describes the checked implementation in `Rocq-copy/SP`.  It is
intentionally stricter than a feature checklist: “implemented” means that a
successful executable path ends in a Rocq theorem and a certificate accepted
by the unchanged `Cyclic` framework.

## Semantic model and trusted assumptions

- Locations are natural numbers; `0` is `nil`.
- A concrete heap is a finite list of address/field-list cells.  A world
  carries `NoDup (map fst heap)`, so it denotes a finite partial map.
- Points-to owns exactly one non-null cell.  Separating conjunction uses
  disjoint subheaps whose append is a permutation of the whole heap.
- Free variables and free tags are supplied by the world.  Existential
  variables and tags receive witnesses local to one formula satisfaction.
- `predicate_holds_rank ds r P xs h` unfolds one definition clause at rank
  `S n`; every recursive predicate in the clause body has rank at most `n`.
  Rank zero is empty.  This is a direct finite unfolding semantics rather than
  an assumed predicate interpretation.
- A named predicate tag bounds its predicate rank.  Ordinal `<` and `<=`
  constraints are interpreted over the same natural-valued tag assignment.
- The cyclic framework sees free antecedent tags and reads their world ranks.
- There are no project axioms, admitted obligations, or aborted proofs.  The
  certification bridge uses standard-library classical principles to extract
  finite branch choices from countermodels.  `Print Assumptions` reports
  `Classical_Prop.classic` and
  `Description.constructive_definite_description`.

## Module map

| Rocq module | Main responsibility | OCaml source correspondence |
|---|---|---|
| `Syntax.v` | Variables, `nil`, three tag classes, constraints, pure/spatial syntax, substitutions, one-way unification, freshening, equality, side checks | `term`, `subst`, `unify`, `tpair`, `pto(s)`, `pred`, `tpred(s)`, `heap`, `form`, `seq`, `indrule`, `preddef`, `defs` |
| `Semantics.v` | Finite heaps, separation, local witnesses, ranked clause unfolding, ordinal interpretation, `Framework.THEORY` instance | Semantic counterpart of `heap`, `form`, `defs`, and trace ranks used by `rules` |
| `Rules.v` | Kernel proofs and packaged rule/axiom instances | Sound subset of `rules.ml` |
| `Automation.v` | Conservative normalization, fresh names, substitution checks, sound strict-self constraint rejection | Small parts of `heap.ml`, `form.ml`, and rule side conditions |
| `RuleGeneration.v` | Syntax-directed candidates and explicit no-candidate boundaries | Front portion of `rules.ml` priority setup |
| `Certification.v` | Reflection bridge from `raw_check = true` to `Cyclic.certificate` | Proof-producing replacement for OCaml graph acceptance |
| `GraphSearch.v` | DFS graph expansion, exact backlinks, witness heuristic and finite enumeration | Bounded counterpart of `prove.ml` plus graph operations in generic infrastructure |
| `Definitions.v` | All 38 entries of `examples/sl.defs`; selected ATVA/Songbird dependency closures | `defs.ml`, `indrule.ml`, definition files |
| `Benchmarks.v` | The nine selected inputs as syntax trees | Selected `benchmarks/sl` lines |
| `Examples.v` | Accepted acyclic/cyclic certificates and rejected graph tests | Teaching and checker regression coverage |
| `Tests.v` | Positive and rejected-side-condition generator/unit tests | Executable regression suite |
| `Search.v` | Iterative deepening, `verified_proof`, `search`, `solvedb`, `search_sound` | Public entailment-search interface |

## Fully realized

| Feature/rule | Executable entry | Checked result |
|---|---|---|
| Structural and tag-erasing equality | `judgment_eqb`, `backlink_eqb`, erasure functions | Exact equality reflects to Leibniz equality; tag erasure has a semantic theorem |
| Finite heap disjointness and exact points-to ownership | `heap_join`, `points_to_holds` | Unit lemmas prove symmetry, one-cell ownership, and rejection of `nil` ownership |
| Formula-local existential witnesses | `formula_holds` | Witness regression theorem in `Semantics.v` |
| Ranked predicate unfolding | `predicate_holds_rank` | `ranked_unfolding` exposes a clause and strictly smaller child bound |
| Identity | `exact_identity_candidate` | `identity_axiom` |
| Safe identity modulo tags | `tag_erasure_candidate` | Drops tag upper bounds only; it never strengthens them |
| Pure explicit inconsistency / ex-falso | `inconsistency_candidate` | Boolean `t != t` detection reflects to semantic impossibility |
| Left disjunction splitting | `left_disjunction_candidate` | Binary theorem-backed rule with countermodel routing |
| Right disjunction choice | `right_disjunction_candidate` | Unary theorem-backed first-branch choice |
| General clause/predicate introduction | `predicate_intro_candidate` | Matches a clause head and body by substitution and produces an axiom theorem for that instance |
| Exact backlinks | `exact_backlink_rule` | Unary identity rule; global progress remains mandatory |
| Certification | `certify_raw_check`, `raw_check_sound` | A successful executable graph check produces a kernel-checked certificate |
| Bounded search | `search`, `solvedb`, `search_sound` | Iterative depth bounds; failed closed graphs do not stop exploration |
| Witness selection | `witness_candidates` | Empty/heuristic candidates followed by bounded finite enumeration |
| Definition reification | `sl_definitions`, `atva_definitions`, `songbird_definitions` | 38 base definitions plus required selected closures |

## Partially realized

| Feature/rule | Implemented subset | Missing behavior |
|---|---|---|
| Unification | Ordered, unidirectional term/heap matching with consistency of repeated variables | Bidirectional, commutative/multiset, partial and classical unification |
| Normalization | Sound identity normal form and substitution primitives | Union-find representative rewriting, sorting, duplicate removal, existential elimination |
| Constraint simplification | Sound detection of an explicit strict self-cycle | General transitive closure, mixed `<`/`<=` cycle solving |
| Freshening | Existential variable/tag shifting | Whole-rule capture-avoidance integrated into unfolding generators |
| Disjunction | Binary left split and first-right-disjunct choice | Enumeration of every right choice and OCaml scheduling heuristics |
| Predicate introduction | Exact instantiated clause body and head | Framed/multiset matching and tag-aware introduction |
| Backlinks | Exact final backlink labels and verified tag erasure as a leaf theorem | Generated substitution/weakening/left/right transformation chains |
| Search | Finite DFS with iterative depth and finite witness enumeration | Memoization, invalidity pruning, OCaml selection functions and performance parity |

## Not realized

| OCaml rule/engine family | Status |
|---|---|
| Equality substitution and existential equality elimination | Generator returns no candidate |
| Equality/disequality discharge beyond exact identity and `t != t` | Generator returns no candidate |
| General bound introduction and constraint-driven tag instantiation | Generator returns no candidate |
| Points-to introduction/instantiation and spatial cancellation | Generator returns no candidate |
| Right inductive unfolding | Generator returns no candidate |
| Left inductive unfolding and strict child-tag generation | Generator returns no candidate |
| Explicit weakening and left/right transformation rules | Not connected |
| Lemma-style partial backlinks | Generator returns no candidate |
| `abduce`, `basepair`, invalidity/model construction | Out of sound-core search scope |
| `disprove`, `modelcheck`, `satcheck`, `satexpgen`, SMT, parser, CLI | Out of scope by plan |

## Search and certification differences

The OCaml prover treats symbolic components as ordered containers with several
specialized unifiers.  The Rocq generator currently matches ordered lists, so
logically commutative rearrangements are not discovered.  Normalization is
deliberately conservative.  Search can therefore return `None` for valid
goals; `None` carries no semantic claim.

Every success follows this path:

`general generator -> immutable graph -> structural/global/witness checks -> certificate -> certificate_sound`.

There is no benchmark-name lookup or benchmark theorem dispatcher.

## Benchmark outcomes

Each selected goal was evaluated in a separate Rocq process with a 15-minute
shell limit and `default_config` (depths 1 through 8).  These are general-search
results; the explicit graphs in `Examples.v` are not counted as benchmark
successes.

| Input | Result | Duration | Trials | Failure reason |
|---|---:|---:|---:|---|
| `base/01.tst`, case 1 | unsupported | 205 ms | 1 | Requires inductive concatenation/left unfolding |
| `base/01.tst`, case 2 | unsupported | 165 ms | Same, plus existential trace-bound instantiation |
| `base/02.tst`, case 1 | unsupported | 176 ms | Requires cyclic concatenation reasoning |
| `base/07.tst`, case 1 | unsupported | 166 ms | Requires mutually structural left/right unfolding |
| `base/19.tst`, case 1 | **proved** | 160 ms | General clause-introduction generator matches the recursive `ls` clause |
| `base/21.tst`, case 1 | unsupported | 187 ms | Left split is generated, but predicate simulation needs unfolding |
| `atva-2014/01.tst`, case 1 | unsupported | 149 ms | Requires cyclic DLL direction reversal |
| `songbird/ls2_entail_ls_01.tst` | unsupported | 149 ms | Requires recursive simulation across definitions |
| `songbird/lsevenodd_01.tst` | unsupported | 164 ms | Requires mutually recursive parity simulation |

No failed benchmark was retried without a material implementation change.
The successful `base/19` result followed the addition of whole-clause body
unification, which binds clause-local variables rather than matching only the
predicate head.

## Explicit certificate tests

- `teaching_acyclic_certificate`: a one-node identity certificate.
- `teaching_cyclic_certificate`: a two-node strict-trace cycle checked by the
  unchanged relational and witness checkers.
- `rejected_open_graph`: an open node is rejected.
- `rejected_malformed_backlink`: a reflexive/self backlink is rejected.
- `rejected_nonprogressing_cycle`: a stay-only exact-backlink cycle is rejected.

These examples test certification mechanics and are deliberately reported
separately from search-supported benchmarks.

## Recommended next work

1. Prove rank-monotonic spatial replacement lemmas and connect left/right
   unfolding with fresh variables and strict child-tag constraints.
2. Add proved multiset cancellation for points-to and predicate atoms.
3. Add verified equality rewriting and existential elimination.
4. Insert explicit weakening/substitution transformations before backlinks.
5. Extend right-disjunction generation to all branches, then add memoization
   and search-tree diagnostics before increasing depth limits.
