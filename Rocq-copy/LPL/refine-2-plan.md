# G3PPL refinement: opaque atoms and primitive formula syntax

## Objective and agreed decisions

Refine `Rocq-copy/LPL` so the shared G3PPL implementation operates on opaque
atom/action carriers and contains only primitive formula constructors. Preserve
the meanings of existing PPL/FOPL benchmarks and reuse one common rule,
generation, and certification implementation.

- Retain `Atom` alongside `Truth`, `Neg`, `Conj`, `Extension`, `First`, `Suffix`, and `Box`.
- Define `Coextension` by duality; migrate directly without a surface datatype.
- Retain decidable syntactic equality and Boolean well-formedness checks.
  Semantic truth and state equality need no decision procedures.
- Keep changes within LPL; preserve the cyclic framework, frozen legacy
  reference, manuscript, and unrelated workspace files.

## Syntax and public interfaces

Use `Atom : L.atom -> formula` and `Atomic : L.action -> program`, with carrier
equality and unary `atom_wfb` / `action_wfb`. Remove shared arguments,
action arguments, `BinaryAtom`, and their checks/interpretations. Keep abstract
extension tokens, world terms, and custom relations. Interpret opaque atoms
at states and opaque actions as executions and atomic traces. `ActionRelation`
carries one opaque action and source/target labels. Preserve the length-two
atomic-trace law.

The formula constructors are exactly `Truth`, `Atom`, `Neg`, `Conj`,
`Extension`, `First`, `Suffix`, and `Box`. Programs retain their constructors
with unary `Atomic`. Define:

| Operator | Primitive expansion |
| --- | --- |
| `Falsity` | `Neg Truth` |
| `Disj a b` | `Neg (Conj (Neg a) (Neg b))` |
| `Impl a b` | `Neg (Conj a (Neg b))` |
| `Coextension x a` | `Neg (Extension x (Neg a))` |
| `DualSuffix a b` | `Neg (Suffix (Neg a) (Neg b))` |
| `Diamond p a` | `Neg (Box p (Neg a))` |

Retain `Next`, `Eventually`, and `Always` as definitions. Rework induction,
equality, purity, well-formedness, and traversals over primitives. Keep the
outer empty-trace guard and prove derived laws for nonempty traces.

## Shared proofs, generation, and instances

Keep manuscript-level propositional, temporal, regular-program, relational,
and atomic-action rules shared and opaque to payloads. Preserve public derived
rule builders, soundness, ordered premises, and existing names. Recognize the
expanded `DualSuffix` for traceability and its right continuation / strict rank
progress; ordinary negations add no progress. Adapt atomic descent,
substitution, freshness, retained-edge, and safety proofs. Keep one shared
progress/graph/kernel instance and the framework's `raw_check_sound` endpoint.

Add computational derived views with reconstruction proofs. Generate every
applicable view plus the primitive candidate in a fixed documented order,
derived views first. Preserve named requests, exact conclusions, premise/tag/
freshness validation, and finite local generation without search or oracles.

PPL uses proposition/action carriers directly. FOPL owns predicate/equality
payloads and variable/term assignments, preserving `Pred`, `Equal`, and
`Assign`. `All` uses `Extension`, `Ex` its dual. Migrate substitution, variable
collection, freshness, pure-terminal checks, quantifier semantics, and
instance-specific rules while reusing common generation/certification and
semantic/progress helpers.

## Implementation order

1. Save this plan, compiler/source inventories, benchmark claims, outside-LPL
   hashes, and separately retained baseline suite results before theory edits.
2. Refactor syntax/semantics and both adapters; compile these layers.
3. Restore progress, rules, derived views, generation, certification, and safety
   in dependency order.
4. Restore FOPL and compatibility: semantics, labels, validity, counterexample
   histories, minima, and ranks against the unchanged legacy oracle.
5. Migrate existing benchmarks and documentation, retaining names and claims.

Compatibility preserves meanings and well-formed legacy inputs. Replace
impossible constructor-sensitive reflection by forward preservation, and
explicitly document that derived syntax equals its expansion. Do not weaken
benchmark claims or silently remove rejection checks.

## Validation and acceptance

Use only the existing 29 benchmark units (15 FOPL, 14 PPL), with no new cases.
Preserve 50 FOPL / 53 PPL premise-shape checks. Verify Boolean/modal/temporal/
quantifier meanings including empty and singleton traces; assignments,
capture avoidance and freshness; atomic/custom relations and nondeterminism;
cyclic certificates, tags, malformed/nonprogressing rejection; and all-state
invariants for complex programs. Labels append, program traces overlap,
assertion labels are nonempty, tests observe `[s; s]`, and FOPL quantifier
bodies stay pure.

Run from LPL, retaining the 600-second command limit and actual timings/failures:

```sh
python3 -B build.py --common
python3 -B run_benchmarks.py --suite all
python3 -B check_integrity.py --kernel --scope --log-dir <fresh-validation-directory>
```

Create the matching fresh `OutsideBaseline.json` before implementation so
scope checks compare real hashes. Audit constructor/interface shapes,
dependencies, shared reuse, assumptions, inventories, and justified statement
representation changes. Remove obsolete plumbing and redundant definitions;
consolidate safety trace combinators into shared polymorphic helpers. Update
API/rule/compatibility/validation documentation. Move obsolete files to
`~/Garbage` with collision-safe numeric suffixes, never permanently delete;
if unwritable, retain and report pending cleanup. Completion requires all
benchmarks and independent kernel checking to pass, no admitted obligations,
and no changes outside LPL.
