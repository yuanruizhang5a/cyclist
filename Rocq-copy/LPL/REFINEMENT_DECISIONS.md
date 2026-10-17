# Refinement decisions

## T1: resolved

User selected item 1: evaluate test guards on `[s; s]`. Both general G3PPL and FOPL retain the two-state stuttering guard observation. This agrees with the labelled test-rule displays and the existing FOPL code. The singleton-looking clause in manuscript section 2.1 remains a documented discrepancy.

D1–D4 remain controlling as recorded in IMPLEMENTATION_PLAN.md.

## Representation and module-sharing choices

The common implementation lives directly in the eight root theory files.
FOPL payloads and adapters live in `FOPL/`.
Two parameterized atomic/extension slots preserve the legacy constructor
organization and induction structure. Their meanings remain supplied by the
instance; plain PPL has no extension tokens. This is a representation choice,
with full legacy semantic and rank-preservation theorems.

The first-order atomic-trace interpretation keeps its original definitional
shape. Every frame proves an `atomic_trace_law` equating that interpretation
with exactly the length-two traces of its action relation. This preserves old
proof scripts while supporting arbitrary nondeterministic G3PPL frames.

A shared progress module is passed into FOPL-specific lemmas and rule kernels.
Reapplying the graph functor produced incompatible inductive record types;
the final code constructs one kernel and passes its exact modules to generation
and certification. A fully bundled plain-PPL helper also triggered a Rocq 9.1
module-substitution assertion during development. Its semantic instance helper
and explicit subsequent kernel construction compile and are exercised by both
independent vocabularies. No mathematical restriction or new axiom was introduced.

The independent checker also exposed an alias-sharing failure in the
compatibility functor: the rank functor received the syntax alias `N`, while
its semantic argument referred to `New.Syn.Shared`. Compilation accepted this,
but independent module checking rejected the `eval_label` field. Passing the
canonical `New.Syn.Shared` path resolves the mismatch. The abstract PPL nested
invariant's safety-functor application needed the same treatment, passing
`Instance.Syn` and `Instance.Sem` directly. No definition, semantic statement,
or proof obligation changes. The failed checks and successful canonical-path
retests are preserved with the archived development records listed in
`CLEANUP.json`.

The generic kernel signature now includes the model's rules directly through
`MakeRulesForModel`, instead of requiring a second, unused unapplied rule
factory as a field. The public `MakeRules ... .ForModel` construction remains
available and delegates to that same implementation. This keeps the single
progress/graph instance explicit without forcing the independent checker to
compare another generative factory inside every FOPL adapter.
FOPL generation/certification export their supplied kernel directly rather
than making another alias of that factory. The caller's original kernel keeps
qualified first-order access; adapter-level `K` belongs to the shared generic
kernel. All first-order rule names remain exported for unqualified use. The
original abstract nested benchmark's generator application is retained.

## Build and cleanup

Compiler commands run from `LPL/`, keeping tactic caches local. The builder
validates compiler, source, dependency and artifact hashes. Failed dependency
builds clear their active traversal state, and a failed common build replaces
any previous benchmark success report with an explicit failure record.

The eight generic implementations live directly in the LPL root. FOPL's
invariant benchmarks import `TraceSafety.v` directly. The preservation oracle
shares the unchanged first-order signature interface; the integrity audit
requires it to match the immutable reference exactly. Legacy syntax, semantics
and progress remain separate test-only implementations.

Obsolete snapshots, diagnostic executables, old logs, generated debris and the
completed progress summary were moved out of the project without permanent
deletion. [CLEANUP.json](CLEANUP.json) records their recoverable archive location.
[VALIDATION.md](VALIDATION.md) contains the current verification evidence.
