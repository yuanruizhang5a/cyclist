# 04 — Existing logic map

This chapter maps the concrete libraries after you understand LTL and the
generic engine. It tells you what each representation means, which files form
the critical path, and where extension points live.

## 1. Repository-level map

| Directory/library | Primary job | Uses generic cyclic prover? | Additional engine |
|---|---|---:|---|
| `src/ltl` / `Ltl` | Propositional linear temporal logic | yes | none |
| `src/firstorder` / `Fol` | First-order inductive definitions | yes | custom term unification |
| `src/seplog` / `Seplog` | Separation-logic entailment and related procedures | entailment: yes | model checker, invalidity, satisfiability, SMT-LIB parser, abduction helpers |
| `src/while` / `While` | Safety/termination of a heap while language | yes | generic abductive BFS for inference mode |
| `src/asl` / `Asl` | Array separation-logic assertion theory | supporting library | Z3-based arithmetic satisfiability |
| `src/asl_while` / `Asl_while` | Safety of array programs | yes | ASL/Z3 operations |
| `src/procedure` / `Procedure` | Compositional while programs with procedures | yes | dependency graph, nested SL proof search, proof cache |
| `src/generic` / `Generic` | Logic-independent proof/search/soundness | framework | C/C++ checker backends |
| `src/lib` / `Lib` | Containers, parsers, variables, unification | no | reusable support |

## 2. First-order logic: the next-smallest symbolic domain

Use Firstorder after LTL when your new logic has terms, variables,
substitutions, or inductive definitions but not heap semantics.

### 2.1 Representation stack

```text
Term
  zero | universal/free variable | existential variable | function(args)
    |
    v
Atom
  equality | disequality | tagged inductive predicate(args)
    |
    v
Prod
  set/conjunction of atoms
    |
    v
Form
  set/disjunction of products
    |
    v
Seq
  (left formula, right formula)
```

The exact logical interpretation of left/right operations is encoded by the
subsumption directions in `Seq.subsumed_wrt_tags` and by the rules. Do not
infer it only from the container names.

### 2.2 Inductive definitions

```text
Case = product body + formal argument list
Defs = ordered association list: predicate name -> cases
```

[`defs.ml`](../src/firstorder/defs.ml) deliberately uses association lists so
source order controls rule enumeration and performance. A map refactor would
be a semantic search-order change even if lookup results were identical.

Example syntax from [`examples/fo.defs`](../examples/fo.defs):

```text
N {
  true => N(0) |
  N(x) => N(s(x))
};
```

### 2.3 Reading order

Read every `.mli` before its `.ml`:

1. `term`: constructors, variable classes, substitutions, unification;
2. `atom`: pure atoms and tagged inductive predicates;
3. `prod`: conjunction-level operations and subsumption;
4. `form`: disjunction-level operations and tag handling;
5. `seq`: the concrete `Sequent.S` implementation;
6. `case` and `defs`: definition parsing/freshening/order;
7. `rules`: simplification first, then generated unfolding/folding, then
   backlink transformation and `setup`;
8. `prove`: input/setup/search order.

### 2.4 Rule phases worth studying

[`firstorder/rules.ml`](../src/firstorder/rules.ml) contains reusable patterns:

| Pattern | Function(s) | Lesson |
|---|---|---|
| Sequent simplification pipeline | `simplify_rules`, `simplify_seq` | Compose pure transformations with `Seqtactics.repeat/first` |
| Definition-derived rules | `gen_right_rules`, `gen_left_rules` | Compile runtime definitions into rule closures |
| Freshening before unfolding | generated unfold rules | Avoid variable capture across proof nodes |
| Transform-to-backlink | `matches_fun`, `subst_rule`, `weaken`, `dobackl` | Make substitution/weakening explicit, then exact-link |
| Folding guided toward closure | `fold` plus `dobackl` | Search heuristic that immediately tests the purpose of a fold |
| Runtime strategy assembly | `setup` | Definitions and order determine the final rule value |

The final strategy uses `Rule.first` for prioritized phases and `Rule.choice`
inside the genuinely exploratory phase. Read it bottom-up after understanding
each component.

## 3. Separation logic: data representation first, rules last

Seplog is the central and richest assertion library. Read its representation
from atoms upward before opening the 1000-line `rules.ml`.

### 3.1 Representation figure

```text
Term: variable or nil
  |
  +--> Tpair --------------------+
  |                              |
  +--> Pto: address -> fields    | pure components
  |      |                       +--> Uf: equalities
  |      v                       +--> Deqs: disequalities
  |    Ptos: multiset            |
  |                              |
  +--> Pred: symbol(args)        |
         |                       |
         v                       |
       Tpred: tag * Pred         |
         |                       |
         v                       |
       Tpreds: multiset          |
         |                       |
         +-----------+-----------+
                     v
        Heap = { eqs; deqs; ptos; inds; caches }
                     |
                     v
        Form = ordinal constraints * Heap list
                     ^                 ^
                     |                 |
                 trace order       disjunction
                     |
                     v
        Seq = (left Form, right Form)
```

The mutable fields in `Heap.symheap` are caches for derived terms/variables/
tags, not permission to mutate logical heap contents arbitrarily. Constructors
and `with_*`/`add_*` functions preserve the representation.

### 3.2 Atomic layer

Read in this order:

1. [`term.mli`](../src/seplog/term.mli): free/existential variables, `nil`,
   freshening, substitutions, term unification;
2. `tpair`: ordered term pairs and pair unification;
3. `uf`: union-find equality representation and equality-based rewriting;
4. `deqs`: disequality set, normalization, partial unification;
5. `pto` and `ptos`: points-to atoms and their multiset;
6. `predsym`, `pred`, `tpred`, `tpreds`: predicate symbols/occurrences and
   trace tags;
7. `unify.mli`: the combined term/tag unifier states and update checks.

Distinctions to keep visible:

```text
subsumed              includes tags
subsumed_upto_tags    ignores assignment of trace tags
total=true            spatial components must match fully
total=false           permits subset/partial matching
unify                  transforms one side
biunify                can transform both sides
```

Read each function's direction in its `.mli`; “subsumes” argument order is not
uniformly guessable from English.

### 3.3 Heap and formula layer

[`heap.mli`](../src/seplog/heap.mli) is the best contract document in this
layer. Learn these groups separately:

- construction/access: `mk`, `dest`, `with_*`, `add_*`, `del_*`;
- derived sets: `terms`, `vars`, `tags`, `tag_pairs`;
- semantic checks: `equates`, `disequates`, `inconsistent`, `subsumed`;
- spatial operations: `star`, `diff`, projection/frame operations;
- substitution/freshening/normalization;
- unification;
- fragment properties such as memory consumption and constructive valuation.

`Form.t` is:

```ocaml
Ord_constraints.t * Heap.t list
```

The list represents disjunction; the constraint set captures ordinal/tag
relationships used in cyclic reasoning. `Form.dest` succeeds only for a single
symbolic heap and otherwise raises `Not_symheap`. Many rules explicitly split
disjunctions before using it.

`Seq.t` is a pair of formulas and implements exact/modulo-tag equality,
subsumption, substitutions, normalization, and trace-pair extraction.

### 3.4 Inductive definitions

```text
Indrule = body Heap + head Pred
Preddef = predicate symbol + list of Indrules
Defs    = collection of Preddefs
```

Critical operations:

- `Indrule.freshen`: avoid variables in the current goal;
- `Indrule.unfold`: bind formals to occurrence arguments, freshen other
  variables, and optionally generate tags;
- `Indrule.fold`: match a body as a subformula of a heap;
- `Defs.unfold`: enumerate all cases for a tagged predicate;
- `Defs.check_*`: definition/formula well-formedness and consistency;
- property checks used by specialized decision procedures.

Example syntax is in [`examples/sl.defs`](../examples/sl.defs).

### 3.5 Rules and strategy

Read [`rules.mli`](../src/seplog/rules.mli) as an index, then read `rules.ml` in
these blocks:

1. exact identity and ex-falso axioms;
2. disjunction splitting and existential/tag instantiation;
3. equality/disequality/constraint normalization;
4. points-to and predicate matching;
5. right and left unfold rules;
6. matching, substitution, weakening, and transformations;
7. lemma/backlink construction;
8. `dobackl` candidate ranking;
9. final `setup`.

The assembled strategy is approximately:

```text
first applicable of
  split left disjunction
  split right disjunction
  instantiate left existentials/tags
  simplify
  introduce bounds
  instantiate constraint-related tags
  choose among
    transformed backlink / lemma
    points-to introduction
    predicate introduction
    points-to instantiation
    right unfold (under a constraint condition)
    left unfold
```

`setup` then combines axioms into the main rule and optionally guards every
application with the invalidity heuristic. The separate `axioms` reference is
left as `Rule.fail` in this module, so do not assume every logic uses the LTL
pattern of a separate axiom phase.

### 3.6 Specialized SL commands are different algorithms

The command group contains:

| Command | Main implementation | Meaning of success |
|---|---|---|
| `sl prove` | `Rules` + generic IDFS | entailment proof found |
| `sl disprove` | `Invalid.invalidity_witness` | invalidity witness found |
| `sl modelcheck` | `Mc_core` or `Mc_cvdet` | concrete model satisfies symbolic heap |
| `sl satcheck` | `Basepair` | inductive definitions/formula satisfy the implemented satisfiability check |
| `sl satexpgen` | generated SAT experiment encodings | experiment generation, not proof search |

Only `sl prove` is the clean generic prover path. Do not expect changes to
`Rules.rules` to affect all other commands.

## 4. While: symbolic execution as cyclic proof rules

The While library reuses Seplog assertions and changes the sequent to a program
state.

### 4.1 Program representation

[`while/program.mli`](../src/while/program.mli) defines:

```text
Cond
  equality | disequality | nondeterministic

Cmd.cmd_t
  Stop | Return | Skip | Assign | Load | Store | New | Free
  | If | IfElse | While | ProcCall | Assert

Cmd.t
  list of labelled basic commands

Program.Seq.t
  Seplog.Form.t * Cmd.t
```

Although the base While prover rejects commands outside its language subset,
the shared AST includes procedure-oriented constructors reused by
`src/procedure`.

Before adding a command, identify every operation over `cmd_t`:

- constructor/destructor and `is_*` predicate;
- parser and printer;
- `cmd_terms`, variables, locals;
- modified-variable analysis;
- equality and substitution;
- numbering/labels;
- dependency analysis and language-subset checks;
- symbolic execution rules in both While and Procedure if shared.

### 4.2 Rule families

[`while/rules.ml`](../src/while/rules.ml) includes:

```text
assertion normalization / disjunction split / predicate unfold
symbolic execution for each atomic and branching command
loop generalization
substitution + frame transformations for backlinks
folding toward backlinks
optional nested SL entailment for backlink cuts
```

`mk_symex` adapts a heap-transforming symbolic-execution function into a proof
rule. Study one simple command (`skip` or assignment) before allocation or
loops.

The final strategy prioritizes normalization, then chooses among backlinking,
fold+backlink, symbolic execution, loop generalization, and left unfolding.

### 4.3 Termination mode

`Program.termination` is a global flag. Some rules use the distinguished
program trace tag/pair to add progress information when termination is being
proved. When changing loop or branching rules, test both safety-only and
termination modes.

## 5. Generic and While abduction

Abduction carries an additional evolving definitions state through search.

```text
ordinary rule:
  node + proof -> alternatives of (open nodes + proof)

abductive rule:
  node + proof + definitions
    -> alternatives of ((open nodes + proof) + new definitions)
```

Read:

1. [`generic/abdrule.mli`](../src/generic/abdrule.mli);
2. [`generic/abducer.ml`](../src/generic/abducer.ml);
3. [`while/abdrules.mli`](../src/while/abdrules.mli) as an index;
4. `while/abdrules.ml` by rule family;
5. [`while/abduce.ml`](../src/while/abduce.ml) for BFS invocation and result
   filtering/simplification.

Unlike the ordinary prover's IDFS, `Abducer.bfs` stores proof, goal depths, and
definitions in each application state. A completed proof is returned only if
the caller's definition check accepts the synthesized definitions.

## 6. Array separation logic

ASL is a separate assertion theory, not a small extension of `Seplog.Heap`.

### 6.1 Assertion stack

```text
Asl_term
  variables, natural constants, addition, constant multiplication
     |
     +--> equality union-find
     +--> !=, <=, < constraint sets
     +--> Asl_array / Asl_arrays
               |
               v
            Asl_heap
               |
               v
            Asl_form (disjunction)
```

`Asl_sat` invokes the Z3 executable and tracks calls/time. Changes to term
printing or constraints must be tested both as internal operations and as
solver input.

### 6.2 Program layer

`asl_while` mirrors the While architecture with:

- `asl_while_program.ml`: commands, conditions, parser, and sequent;
- `asl_while_rules.ml`: simplification, symbolic execution, backlinking, and
  loop generalization;
- `prove.ml`: configures Z3 and runs the generic prover.

This branch is useful when your logic needs an external theory solver. Keep the
solver boundary explicit and make timeout/unknown behavior part of tests.

## 7. Procedures: compositional verification and nested proving

Procedure is the most integrated concrete prover. Read it only after While and
Seplog.

### 7.1 Program structure

`Procedure.Program` reuses `While.Program.Field`, `Cond`, and `Cmd`, then adds:

```text
Proc
  name + parameters + list of pre/post specs + body

dependency graph
  vertices are procedures; edges are calls

Procedure.Seq.t
  precondition * command sequence * postcondition
```

The driver computes reachable procedures, strongly connected components, and
proves procedure/spec sequents in dependency order.

### 7.2 Rules combine several engines

[`procedure/rules.ml`](../src/procedure/rules.ml) contains:

- symbolic execution;
- procedure unfolding and call-by-spec rules;
- assertion and sequence rules;
- frame inference and abduced precondition transforms;
- left/right cuts and schema introduction;
- cyclic backlinks;
- nested Seplog entailment proving with memoization;
- reuse of already extracted procedure proofs.

The setup receives:

```ocaml
defs * procedures * procedure_proof_cache
```

and initializes Seplog rules, abduction definitions, invalidity checks, and the
final procedure strategy.

### 7.3 Driver behavior

[`procedure/prove.ml`](../src/procedure/prove.ml):

1. parses and numbers procedures;
2. builds dependency/reachability graphs;
3. decomposes them into strongly connected components;
4. proves each relevant specification;
5. extracts subproofs rooted at procedure-unfold nodes;
6. caches proofs by procedure signature and pre/post pair;
7. decides success for selected entry points.

A change to proof extraction, procedure-node descriptions, or sequent equality
can therefore affect cache hits and compositional reuse.

## 8. The utility library: read on demand

Useful interfaces by problem:

| Need | Read |
|---|---|
| Type accepted by all containers | `lib/utilsigs.mli`, especially `BasicType` |
| Ordered set/map/multiset behavior | `containers.mli`, `treeset.mli`, `treemap.mli`, `multiset.mli` |
| Search/list combinators | `blist.mli` |
| Variables and freshening | `varManager.mli` |
| CPS unifier composition | `unification.mli` |
| Parser helpers/tokens | `parsers.mli`, `symbols.mli` |
| Debug, timeout, printer helpers | `misc.mli` |

Because many concrete modules `open Lib`, unqualified names such as `Option`,
`Int`, and `Blist` may refer to repository wrappers/extensions rather than only
the standard library. Check the corresponding interface when behavior is not
obvious.

## 9. Which modules to modify for common jobs

```text
New logical connective
  syntax/parser/printer
    -> vars/terms/tags/substitution/normalization
      -> rule(s)
        -> strategy
          -> unit + search + CLI tests

New inductive-definition feature
  definition AST/parser/validation
    -> freshening/unfold/fold
      -> setup-generated rules
        -> definition examples + search-order tests

New while command
  shared Program.Cmd operations
    -> symbolic execution in each applicable program prover
      -> modifies/dependency analysis
        -> parsing/printing/program proof tests

New backlink policy
  exact/modulo equality or matching
    -> explicit transforms
      -> tag correspondence
        -> selector and greedy/backtracking choice
          -> accepted/rejected global soundness tests
```

Use this impact chain before editing. Most regressions in a theorem prover come
from updating the obvious rule while missing a representation invariant,
search policy, or trace transition.
