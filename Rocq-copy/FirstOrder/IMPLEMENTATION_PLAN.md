# Verified first-order prover implementation plan

This document records the design used to turn the first-order development
from a collection of benchmark proofs into a proof-producing cyclic prover.
It is intentionally kept next to the Rocq sources so that the implementation,
its trusted boundary, and the original OCaml design can be studied together.

## Goal and trusted boundary

The prover accepts a reified Rocq first-order judgment, applies the same broad
rule families and priority as `src/firstorder/rules.ml`, constructs a finite
proof graph, supplies the trace information required by the existing generic
framework, and returns a theorem only after the graph is accepted by the
kernel-checked soundness development.

`Cyclic/` and `LTL/` are not changed.  All first-order-specific reflection,
search, and certification code lives under `FirstOrder/`.

The following distinctions are important:

* A successful Boolean side-condition is useful only after a reflection lemma
  turns it into the proposition required by a theorem-backed rule.
* `None` from bounded search means "not found within this bound", not
  "invalid".
* A closed graph is not yet a proof.  Its labels, edges, global progress, and
  finite trace-routing witness must all pass the generic checker.

## Implementation stages

- [x] Reified syntax for variables, terms, atoms, products, formulae, clauses,
  definitions, sequents, substitutions, and tags.
- [x] Ranked semantics with universal antecedent variables and existential
  succedent witnesses.
- [x] Sound identity, contradiction, disjunction, conjunction, backlink, and
  left/right unfolding rule kernels.
- [x] Direct transcription of `examples/fo.defs` and independent semantic
  proofs of all positive examples.
- [x] Set-style normalization and permutation-independent matching.
- [x] Executable variable collection, fresh-name selection, and a verified
  directional first-order matcher.  Full symmetric unification and
  substitution composition remain part of the rule-generation stage below.
- [ ] Remaining simplification, instantiation, weakening, substitution, and
  fold rules from the OCaml prover.
- [x] First-order-local reflection from a checked graph to a
  `Cyclic.certificate`.
- [ ] Iterative-deepening graph search with the OCaml rule priority.
- [ ] Trace-witness constraint solving for closed cyclic graphs.
- [ ] Positive benchmarks proved through general search rather than a fixed
  theorem dispatcher.
- [ ] Bounded non-success and malformed-certificate regression tests.

The checklist is updated as each independently compiling stage lands.

## Intended public interface

```coq
Record search_config := {
  min_depth : nat;
  max_depth : nat
}.

Definition default_config : search_config.  (* depths 1 through 11 *)

Record verified_proof (goal : judgment) := {
  proof_certificate : Cyclic.certificate;
  proof_root_matches :
    Cyclic.graph_root proof_certificate.(Cyclic.cert_graph) =
      prepare_and_normalize goal;
  proof_check_passes :
    Cyclic.check_certificate proof_certificate = true
}.

Definition search :
  forall goal, search_config -> option (verified_proof goal).

Definition solvedb : search_config -> judgment -> bool.

Theorem search_sound :
  forall cfg goal,
    solvedb cfg goal = true -> Cyclic.Valid goal.
```

The exact projection syntax may vary slightly as Rocq elaboration requires,
but the semantic contract must remain this one.

## OCaml-to-Rocq feature map

| Original component | Rocq responsibility |
| --- | --- |
| `term.ml` | substitutions, fresh variables, ordered and multi-unification |
| `atom.ml`, `prod.ml`, `form.ml`, `seq.ml` | normalized reified syntax, set-style matching and subsumption |
| `case.ml`, `defs.ml` | ordered clauses and capture-avoiding clause freshening |
| `rules.ml` axioms | theorem-backed identity and ex-falso instances |
| `rules.ml` simplifiers | equality, injectivity, RHS discharge, and existential substitution instances |
| `gen_left_rules`, `gen_right_rules` | theorem-backed unfolding instances with trace edges |
| `fold`, `matches_fun`, `dobackl` | fold, unification/subsumption, explicit weakening/substitution, exact backlink |
| `generic/prover.ml` | total, fuel-bounded iterative-deepening search |
| `generic/soundcheck` | unchanged `Cyclic` graph checker plus FirstOrder-local certificate construction |

## Rule/search order

Each open goal is processed in the same high-level priority as the OCaml
implementation:

1. ex-falso and identity axioms;
2. repeated simplification;
3. backlink discovery;
4. left disjunction;
5. existential instantiation;
6. right conjunction;
7. right unfolding;
8. composed left then right unfolding;
9. left unfolding;
10. folding followed by backlink discovery.

Definition and clause lists retain source order.  Other finite collections are
normalized so their accidental list order does not affect logical matching.

## Verification commands

From `Rocq-copy/`:

```sh
make -B -j2
rg -n 'Admitted|admit\.|Abort\.|Axiom ' FirstOrder
git diff -- Cyclic LTL
```

Useful Rocq inspection commands are:

```coq
Print Assumptions search_sound.
Eval vm_compute in map (solvedb default_config) positive_goals.
```

The positive benchmark result must contain nine `true` values.  Disabled
benchmarks are bounded non-success tests only; they do not establish semantic
invalidity.

## Necessary differences from the executable OCaml frontend

The input is a Rocq AST rather than parser text.  Gallina search uses explicit
depth fuel rather than a wall-clock timeout, because every function must be
total.  The port follows the OCaml rule priority but does not depend on the
iteration order of OCaml set implementations.  Finally, the unchanged cyclic
framework requires an explicit finite trace-routing witness, so a graph is
accepted only when such a witness is constructed and checked.
