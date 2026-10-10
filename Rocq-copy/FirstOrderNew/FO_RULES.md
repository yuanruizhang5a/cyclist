# First-order rules implemented in FirstOrderNew

`FirstOrderNew` implements a positive first-order calculus with inductively defined predicates and cyclic proofs. Premises appear **above** each inference line and the conclusion **below** it; proof search reads these rules upwards.

This document uses Markdown math: `$...$` for inline formulas and `$$...$$` for display formulas. Open it in a Markdown viewer with math support.

## Notation

- $\Gamma,\Pi,B$ denote **products**, meaning conjunctions of atoms.
- $F,G,\Delta$ denote **formulas**, meaning disjunctions of products.
- The empty product is $\top$; the empty formula is $\bot$.
- Free variables are universal parameters. Existential variables on the right are witnesses scoped independently to each right-hand product.
- $P^\tau(\vec t)$ is a predicate with logical tag $\tau$. Tags do not affect truth, but predicate **occurrences** matter for cyclic traces.
- Substitution $A\theta$ is simultaneous.

These conventions are defined in [Syntax.v](Syntax.v#L15), [Substitution.v](Substitution.v#L5), and [Semantics.v](Semantics.v#L101).

## 1. Identity — `Id`

The familiar instance is

$$
\frac{\ }{\Gamma,A\vdash A\lor\Delta}.
$$

The implemented check is more general. For $F=\bigvee_i\Gamma_i$ and $G=\bigvee_j\Pi_j$,

$$
\frac{\ }{F\vdash G}
\quad\text{if}\quad
\forall i\;\exists j:\ \Pi_j\subseteq\Gamma_i.
$$

Inclusion compares atoms syntactically while ignoring predicate tags. Thus every left-hand disjunct must imply some right-hand disjunct by inclusion. This also handles $\bot\vdash G$ and $F\vdash\top$.

Implementation: [`identityb`, Syntax.v](Syntax.v#L73); certified constructor: [`checked_identity`, Compiler.v](Compiler.v#L29).

## 2. Contradiction — `Ex Falso`

The directly recognized contradictory atoms are

$$
t\ne t,\qquad
0=s(t),\qquad
0=\operatorname{cons}(t,u),
$$

including the reversed orientations of the equalities. For a single product,

$$
\frac{\ }{\Gamma,C\vdash G}
\qquad(C\text{ is one of those contradictory atoms}).
$$

For a disjunctive antecedent, **every** product must contain a recognized contradiction.

The model assumes that zero is outside the images of unary `s` and binary `cons`. This check does not implement general inconsistency detection.

Implementation: [`contradictory_atom` and `contradictionb`, Rules.v](Rules.v#L39); certified constructor: [`checked_ex_falso`, Compiler.v](Compiler.v#L23).

## 3. Left disjunction — `OrL`

$$
\frac{
 \Gamma_1\vdash G\quad\cdots\quad\Gamma_n\vdash G
}{
 \Gamma_1\lor\cdots\lor\Gamma_n\vdash G
}.
$$

There is one premise for each antecedent product. Predicate occurrences are carried into their corresponding branch without strict trace progress.

Implementation: [`left_disjunction`, LocalRules.v](LocalRules.v#L381). The underlying label transformation is [`lhs_split`, Rules.v](Rules.v#L81).

## 4. Right conjunction — `AndR`

$$
\frac{F\vdash\Pi\qquad F\vdash\Sigma}
     {F\vdash\Pi\land\Sigma}.
$$

Its essential side condition is

$$
\operatorname{EV}(\Pi)\cap\operatorname{EV}(\Sigma)=\varnothing,
$$

where $\operatorname{EV}$ collects existential variables, including variables nested inside terms. Shared free variables are allowed.

The two premises may choose different existential witnesses; independence lets the implementation combine them. The checked API requires a **single right-hand product**, split at an interior list position into two nonempty parts.

Implementation: [`guarded_right_conjunction`, LocalRules.v](LocalRules.v#L766); executable constructor: [`checked_right_split`](LocalRules.v#L793); independence test: [`existential_independentb`](LocalRules.v#L730).

## 5. Right existential instantiation — `ExR`

For a substitution $\theta$ whose domain contains only existential variables,

$$
\frac{F\vdash\Pi\theta\lor\Delta}
     {F\vdash\Pi\lor\Delta}.
$$

This selects one right-hand product and instantiates it. It leaves the antecedent and other right-hand products unchanged. Substitution images may be arbitrary terms.

With the existential quantification made explicit, the familiar reading is

$$
\frac{F\vdash\Pi[t/e]\lor\Delta}
     {F\vdash(\exists e.\Pi)\lor\Delta}.
$$

Implementation: [`rhs_existential_instantiation` and `checked_rhs_instantiation`, LocalRules.v](LocalRules.v#L480). Indexed descriptor handling is [`checked_instantiation_at`, Compiler.v](Compiler.v#L67).

## 6. Weakening and exchange — `Weak/Exchange`

The basic forms are

$$
\frac{\Gamma\vdash G}{\Gamma,A\vdash G},
\qquad
\frac{\Gamma\vdash G}{\Gamma\vdash G\lor\Pi}.
$$

The actual constructor combines them:

$$
\frac{\Sigma\vdash H}{\Gamma\vdash G}
$$

provided

$$
\Sigma\subseteq\Gamma,
\qquad
\forall\Pi\in H\;\exists\Lambda\in G:\ \Lambda\subseteq\Pi.
$$

Both antecedents must be single products. Inclusion ignores predicate tags. Because membership ignores order and permits reuse, this constructor also supports exchange and duplicate manipulation when its occurrence mapping succeeds.

Implementation: [`checked_weakening`, LocalRules.v](LocalRules.v#L305). Predicate trace transport uses [`occurrence_map`](LocalRules.v#L135).

## 7. Substitution — `Subst` and `SubstScoped`

The mathematical direction is

$$
\frac{F\vdash G}{F\theta\vdash G\theta}.
$$

In backwards search, the substituted goal is reduced to its uninstantiated companion.

There are two certified variants:

- **`Subst`:** every explicit binding maps a free variable to a term containing only free variables. Existential variables remain unchanged.
- **`SubstScoped`:** additionally permits existential-to-existential renaming. That renaming must be injective over **all existential variables occurring in the companion**, including unmapped variables whose images remain themselves.

The second condition prevents witness variables from being merged accidentally.

Implementation: [`backward_substitution` and `checked_backward_substitution`, LocalRules.v](LocalRules.v#L322); scope test: [`scoped_substitutionb`](LocalRules.v#L980); extended constructor: [`backward_substitution_scoped`](LocalRules.v#L1070).

The next six rules are the implemented simplification families.

## 8. Remove reflexive equalities — `simplAllTaut`

Let $T(\Pi)$ remove every atom of the form $t=t$, and extend $T$ productwise to formulas. Then

$$
\frac{T(\Gamma)\vdash T(G)}{\Gamma\vdash G}.
$$

The certified constructor currently requires a single antecedent product. It removes reflexive equalities on both sides.

Implementation: [`trivial_equality_rule`, LocalRules.v](LocalRules.v#L462); transformation: [`without_trivial`, Simplification.v](Simplification.v#L14).

## 9. Left equality substitution — `simplEq`

Suppose $\Gamma$ contains $v=t$, or $t=v$, and let $\theta=[v\mapsto t]$. Then

$$
\frac{\Gamma\theta\vdash G\theta}{\Gamma\vdash G}.
$$

The antecedent must be a single product, and all variables in $t$ must be free. For well-formed input, $v$ is also free because antecedent variables are free.

The equality atom remains in the substituted product; a later reflexive-equality simplification may remove it. There is **no occurs-check restriction**: an equality such as $x=s(x)$ may cause repeated rewriting until the simplification budget is exhausted.

Implementation: [`left_equality_substitution` and `left_equality_rule`, LocalRules.v](LocalRules.v#L555); binding selection: [`eq_binding`, Simplification.v](Simplification.v#L15).

## 10. Right equality instantiation — `simplEx` family

If a selected right product contains $e=t$, or $t=e$, with $e$ existential, set $\theta=[e\mapsto t]$:

$$
\frac{F\vdash\Pi\theta\lor\Delta}
     {F\vdash\Pi\lor\Delta}.
$$

This is equality-directed `ExR`. Only the selected right product is substituted. The implementation does not require $e\notin\operatorname{vars}(t)$; without that condition, the resulting equality need not become reflexive.

Implementation: [`right_equality_rule`, LocalRules.v](LocalRules.v#L494); existential binding selection: [`ex_binding`, Simplification.v](Simplification.v#L19).

## 11. Discharge right-hand atoms already on the left — `simplRHS`

For a product $\Gamma$, define

$$
D_\Gamma(\Pi)=
\{A\in\Pi\mid A\text{ does not occur logically in }\Gamma\}.
$$

Then

$$
\frac{\Gamma\vdash\bigvee_i D_\Gamma(\Pi_i)}
     {\Gamma\vdash\bigvee_i\Pi_i}.
$$

The antecedent must be a single product containing only free variables. Matching is syntactic modulo predicate tags. This removes conjuncts already guaranteed by the antecedent.

Implementation: [`right_discharge_rule`, LocalRules.v](LocalRules.v#L619); transformation: [`simplify_right_atoms`, Simplification.v](Simplification.v#L48).

## 12. Left constructor injectivity — `simplLHSInj`

$$
\frac{\Gamma,t=u\vdash G}
     {\Gamma,s(t)=s(u)\vdash G},
$$

and

$$
\frac{\Gamma,t_1=u_1,t_2=u_2\vdash G}
     {\Gamma,\operatorname{cons}(t_1,t_2)
              =\operatorname{cons}(u_1,u_2)\vdash G}.
$$

This replaces one constructor equality by equalities between its arguments. The antecedent must be a single product. The constructor terms must satisfy the well-formedness guard, which enforces the supported arities.

Only `s` and `cons` have assumed injectivity.

Implementation: [`left_injectivity_rule`, LocalRules.v](LocalRules.v#L700); guard: [`injectivity_guard`](LocalRules.v#L649).

## 13. Right function congruence — `simplRHSInj`

Despite its internal name, this rule uses **congruence**:

$$
\frac{
 F\vdash
 \left(\Pi\land\bigwedge_{i=1}^{n}t_i=u_i\right)\lor\Delta
}{
 F\vdash
 \left(\Pi\land f(t_1,\ldots,t_n)=f(u_1,\ldots,u_n)\right)\lor\Delta
}.
$$

It applies to any function symbol when both applications have the same symbol and argument count. It does not require injectivity.

Implementation: [`right_congruence_rule`, LocalRules.v](LocalRules.v#L717); argument expansion: [`constructor_eqs`, Simplification.v](Simplification.v#L25).

For the remaining inductive rules, write a defining clause as

$$
c:\quad B_c(\vec z)\Longrightarrow P(\vec h_c(\vec z)).
$$

Predicates receive their least-fixed-point interpretation from these positive clauses.

## 14. Left unfolding with a retained copy — `left_unfold_contract`

For every clause $c$ defining $P$, freshen **all** its variables into free eigenvariables $\vec a_c$. The rule is

$$
\frac{
 \left\{
 B_c(\vec a_c),\quad
 \vec t=\vec h_c(\vec a_c),\quad
 P(\vec t),\quad
 \Gamma
 \vdash G
 \right\}_{c\text{ defining }P}
}{
 \Gamma,P(\vec t)\vdash G
}.
$$

Here $\vec t=\vec h$ abbreviates the conjunction of componentwise equalities. **Every defining clause contributes a premise**, including base clauses.

The retained $P(\vec t)$ is explicit in the implementation. If the principal occurrence has tag $\tau$, body predicates receive tag $\tau$, and the retained copy receives a fresh logical tag.

For traces:

- Principal-to-body-predicate edges are progressing: the body predicates have smaller stage bounds.
- Principal-to-retained-copy and context edges are nonprogressing continuations.

The checked rule requires a free-only antecedent and matching head arities. Its indexed variant handles a disjunctive antecedent by adding unchanged, single-product premises for the other disjuncts.

Implementation: [`left_unfold_product` and `left_unfold_trace`, Unfolding.v](Unfolding.v#L412); basic application: [`left_unfold_application`](Unfolding.v#L432); disjunctive variant: [`left_unfold_at_application`](Unfolding.v#L735).

## 15. Right unfolding — `right_unfold` and its instance variants

Choose **one** clause $c$ defining $P$, freshly renamed while preserving variable classes:

$$
\frac{
 F\vdash
 \left(\Pi\land\vec t=\vec h_c(\vec z)\land B_c(\vec z)\right)\lor\Delta
}{
 F\vdash
 \left(\Pi\land P(\vec t)\right)\lor\Delta
}.
$$

Unlike left unfolding, this makes a clause choice rather than branching over all clauses. It leaves antecedent traces unchanged.

The instantiated variant permits a substitution $\theta$ on the fresh clause:

$$
\frac{
 F\vdash
 \left(\Pi\land\vec t=\vec h_c\theta\land B_c\theta\right)\lor\Delta
}{
 F\vdash
 \left(\Pi\land P(\vec t)\right)\lor\Delta
}.
$$

The matched variant computes $\theta$ by head matching. **Head equations remain in the premise**, including constraints from repeated head variables.

Checks require clause membership, the correct predicate symbol and arity, freshness, and a free-only antecedent.

Implementation: [`right_unfold_application` and `right_unfold_check`, Unfolding.v](Unfolding.v#L326); instantiated variant: [`right_unfold_instance_application`](Unfolding.v#L887); matched variant: [`checked_right_unfold_matched`](Unfolding.v#L995).

## 16. Left folding — `Fold`

Suppose $B_c\theta\subseteq\Gamma$, and let $R$ be the product obtained by removing from $\Gamma$ every atom logically present in $B_c\theta$. Then

$$
\frac{P(\vec h_c\theta),R\vdash G}
     {\Gamma\vdash G}.
$$

The reason is that $\Gamma$ supplies the clause body, which implies its head. Proof search therefore replaces the available body atoms by the head.

The checked constructor requires a single antecedent product, a clause in the definition environment, and free-only variables in both the source product and instantiated head. The compiler additionally requires a nonempty clause body and a fresh head tag.

Remaining context predicates retain their traces. The new head receives no progressing edge.

Implementation: [`fold_application`, LocalRules.v](LocalRules.v#L901); checks: [`checked_fold`](LocalRules.v#L942); compiler restrictions: [`compile_fold`, Compiler.v](Compiler.v#L101).

## 17. Cyclic backlink

An exact backlink has the local shape

$$
\frac{J\quad\text{(an existing graph node)}}{J}.
$$

A backlink modulo substitution and weakening is assembled as

$$
J\ \longrightarrow\ K\theta\ \longrightarrow\ K,
$$

where $K$ is the companion node. The two steps use checked weakening and checked backwards substitution.

A backlink alone does not establish validity. The completed graph must pass the global checker. Local trace evidence guarantees

$$
r_{\text{premise}}\le r_{\text{conclusion}}
$$

along continuation edges and

$$
r_{\text{premise}}<r_{\text{conclusion}}
$$

along progressing edges; global acceptance supplies the obligations that make cyclic reasoning sound.

Implementation: [`exact_backlink`, Adapter.v](Adapter.v#L126); composed prefixes: [`backlink_prefix`, LocalRules.v](LocalRules.v#L360) and [`backlink_prefix_scoped`](LocalRules.v#L1114); rank conditions: [`respects`, Rules.v](Rules.v#L12); graph soundness: [`checked_graph_sound`, Certification.v](Certification.v#L162).

## Executable rule vocabulary

The complete executable rule vocabulary is [`rule_descriptor`, RuleGeneration.v](RuleGeneration.v#L11). Its correspondence to the certified constructors above is explicit in [`compile_rule_descriptor`, Compiler.v](Compiler.v#L107).
