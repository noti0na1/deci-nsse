# Decidability of non-structural subtype entailment

**Non-structural subtype entailment is decidable for bottom, top, and one
constructor of arbitrary finite arity and arbitrary variance in each argument.**
This repository gives a self-contained proof in [Lean 4](https://lean-lang.org/)
with [Mathlib](https://github.com/leanprover-community/mathlib4), and computable
decision procedures over **arbitrary, regular and finite trees, including arity
zero**.

The input specifies an arity `n`, a variance map `c : Fin n → Bool`, a finite
constraint system, and a queried variable inequality. Here `false` means
covariant and `true` means contravariant. Binary covariant products and arrows
are named special cases in [Instances.lean](DeciNSSE/Instances.lean).

Entailment asks whether the query holds in every solution. It arises when
simplifying inferred types; the binary problem appears as
[Problem 16 of the TLCA open problem list](https://tlca.di.unito.it/opltlca/opltlcasu23.html).
The proof works directly over paths in `Fin n`. Its finite search bounds are
non-elementary, so it establishes decidability in principle rather than a
practical type inference algorithm.

## The problem

### Why entailment matters

Constraint-based type inference records requirements on unknown types. A
constraint `x ≤ y` is redundant when the remaining constraints already force
it in every solution. Deciding entailment therefore supports simplification
without changing the set of possible types. This motivation is developed in
[Niehren and Priesnitz (1999)](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf).

**Satisfiability** asks whether there is at least one solution. **Entailment**
asks whether every solution satisfies a proposed relation. Finding a solution
does not by itself answer the entailment question.

### Trees and non-structural subtyping

The signature is `{⊥, f, ⊤}`, with one constructor `f` of arity `n`. Bottom and
top are leaves; each constructor node has children indexed by `Fin n`. Trees
may be finite or infinite. The order satisfies

```text
⊥ ≤ t ≤ ⊤                         for every tree t
f(a) ≤ f(b)                       iff, for every i,
                                    a(i) ≤ b(i) when c(i) = false,
                                    b(i) ≤ a(i) when c(i) = true.
```

For infinite trees, these rules are read coinductively: the order is their
**greatest fixed point**. Concretely, labels are ordered `⊥ < f < ⊤` at every
finite path present in both trees, reversing the comparison when the path
contains an odd number of contravariant positions. Accumulated polarity is
`polarity c`; the explicit variance relation is `Tree.Le c`. The notation `≤`
on `Tree n` denotes the covariant order used internally.

The order is *non-structural* because comparable trees may have different
shapes: `⊥ ≤ f(a) ≤ ⊤` even though the extreme trees have only a root.
For `n = 0`, the only trees are `⊥`, `f()` and `⊤`, ordered as a three-element
chain. The uniform decision procedures cover this case as well.

### Constraints, solutions, and the decision question

A flat constraint system `ϕ` is a finite list of literals of four forms:

```text
x = ⊥     x = ⊤     x ≤ f(a)     f(a) ≤ x
```

Here `a : Fin n → V k` selects the child variables from the `k` variables.
A solution `ρ : V k → Tree n` satisfies every literal using `Tree.Le c`.
The queried inequality `x ≤ y` is not an additional primitive literal.

The judgment `ϕ ⊨ x ≤ y` means that every solution `ρ` has
`Tree.Le c (ρ x) (ρ y)`. The input is finite even when its solutions contain
infinite trees. If the system has no solution, every query holds vacuously.

For example, `x ≤ f(a)` and `f(a) ≤ y` entail `x ≤ y` by transitivity for every
arity and variance. They do not entail `y ≤ x`: assign `x = ⊥`, `y = ⊤`, and
all child variables to bottom, using distinct variables for this example.

At positive arity, a variable inequality can itself be expressed by two flat
constructor literals and two existential auxiliary variables. The first
coordinate carries the compared variables, exchanged if that coordinate is
contravariant; all other coordinates use a common filler. At arity zero, no
flat system with existential auxiliaries defines order between distinct
variables. Both assertions are proved in
[Semantics/Characterisation.lean](DeciNSSE/Semantics/Characterisation.lean), as
`Characterisation.le_definable_iff` and `Characterisation.nullary_not_definable`.
The decision interface accepts the queried inequality directly at every arity.

### Which trees are allowed as solutions?

| Domain | Meaning | Lean representation |
| --- | --- | --- |
| Arbitrary trees | All finite and infinite trees | `Tree n` |
| Regular trees | Trees with finitely many distinct rooted subtrees | Unfoldings of `RGraph n` |
| Finite trees | Trees with finitely many nodes | Images of `FTree n` |

The representation claims are proved by `Characterisation.unfold_range_iff`
and `Characterisation.toTree_range_iff`. The order characterisation is
`Characterisation.treeLe_eq_gfp`; `Characterisation.lfp_ne_treeLe` shows that
the least fixed point differs whenever there is at least one child position.

A regular tree can be infinite. With a binary covariant constructor, the two
constraints `f(x, x) ≤ x` and `x ≤ f(x, x)` have the full infinite constructor
tree but no finite solution. This distinction explains why finite entailment
includes a separate vacuity case.

## Formal statements and decision procedures

Import `DeciNSSE` to use the public API. Arity and variable count are inferred
from the inputs. All names in the following table are in namespace `DeciNSSE`.

| Procedure | Result | Domain of solutions |
| --- | --- | --- |
| `decideEntails c ϕ x y` | `Decidable (Entails c ϕ x y)` | Arbitrary trees |
| `decideEntailsReg c ϕ x y` | `Decidable (EntailsReg c ϕ x y)` | Regular trees |
| `decideEntailsFin c ϕ x y` | `Decidable (EntailsFin c ϕ x y)` | Finite trees |

The signature of the first procedure is

```lean
def decideEntails {n k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) : Decidable (Entails c ϕ x y)
```

The other two have the same arguments. None requires satisfiability, positive
arity, a supplied monitor family, or an inhabited path alphabet. Each has a
correctness lemma; for example,

```lean
theorem decideEntails_correct {n k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) :
    @decide _ (decideEntails c ϕ x y) = true ↔ Entails c ϕ x y
```

The semantic definitions distinguish satisfaction by a given valuation from
existence of a solution:

```lean
Sat c ρ ϕ                 -- ρ satisfies every literal of ϕ
Satisfiable c ϕ           -- ∃ ρ, Sat c ρ ϕ
SatisfiableFin c ϕ        -- ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ
Entails c ϕ x y           -- ∀ ρ, Sat c ρ ϕ → Tree.Le c (ρ x) (ρ y)
```

The exact transfer theorems are

```lean
theorem entailsReg_iff_entails {n k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) :
    EntailsReg c ϕ x y ↔ Entails c ϕ x y

theorem entailsFin_iff {n k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) :
    EntailsFin c ϕ x y ↔ ¬ SatisfiableFin c ϕ ∨ Entails c ϕ x y
```

See [Main.lean](DeciNSSE/Main.lean),
[Transfer/Regular.lean](DeciNSSE/Transfer/Regular.lean), and
[Transfer/Finite.lean](DeciNSSE/Transfer/Finite.lean).
For binary products use `productVariance`; for arrows use `arrowVariance`,
whose domain is contravariant and codomain covariant. Both use the same three
procedures.

## Proof overview

The proof reduces a countermodel to a finite word called a *hole* in one of
two finite monitors, then bounds the length of a hole witness. All reductions,
bounds and transfer arguments are proved in Lean.

### 1. Normalise variance and translate to signed variables

Normalisation exchanges bottom and top according to path polarity and leaves
tree domains unchanged. Each variable receives positive and negative copies,
turning the system into a covariant constraint system on `2*k` variables.
An assignment fixed by sign duality decodes to a variance solution.
See [Constraints/Signed.lean](DeciNSSE/Constraints/Signed.lean).

### 2. Recover variance models by median symmetrisation

The median of three trees is obtained from the pointwise median of their
extended labels, pruning below bottom or top. It is monotone and preserves
covariant solutions. Median of a signed solution, its sign dual and the full
constructor tree is fixed by sign duality. Three suitable prefix conditions
ensure that an unsafe word survives this operation.
See [Semantics/Median.lean](DeciNSSE/Semantics/Median.lean) and
[Transfer/ThreeSpine.lean](DeciNSSE/Transfer/ThreeSpine.lean).

### 3. Express unsafety by a finite spine extension

Closure derives variable inequalities by reflexivity, transitivity and
constructor decomposition. Upper and lower path judgements describe the
bounds at a tree path. A label clash is exactly the obstruction to a
covariant solution; without one, a least solution has a finite graph
representation.

Three fresh constraint spines enforce the prefix conditions for an unsafe
word. Their source and sink variables remain separated, and ranks strictly
increase along new nonempty paths. At cut zero the roots are old variables
and may coincide. The closure formulas cover this case without a distinctness
assumption. See [Monitor/Spine.lean](DeciNSSE/Monitor/Spine.lean) and
[Monitor/Closure.lean](DeciNSSE/Monitor/Closure.lean).

### 4. Classify clashes as four kinds of events

Clashes of the extension are exactly inherited clashes or readiness, child,
cross and self events. Readiness is checked at every cut. The child test is
letter-free and applies at the terminal cut, even with an empty alphabet.
Cross and self events concern repeated suffixes; self-admission includes
both orientations of the sign-flipped labels.

For a satisfiable original system, an unsafe word is exactly a word without
events. The satisfiability hypothesis excludes inherited clashes and is
necessary for this model-existence argument.
See [Monitor/Events.lean](DeciNSSE/Monitor/Events.lean) and
[Monitor/Semantics.lean](DeciNSSE/Monitor/Semantics.lean).

### 5. Read the events with a finite label monitor

A state contains upper and lower label sets and a Boolean latch for earlier
readiness. Current readiness and the child condition complete the acceptance
test. For `m` variables there are `2 * 4^m` states; the signed input thus uses
`N = 2 * 4^(2*k)` states (`Monitor.card_state`).

A comparison has cuts `s < e ≤ |w|` such that `w.drop e` is a prefix of
`w.drop s`. It is admitted when the monitor states at those cuts satisfy the
cross or self relation. A *hole* reaches a rejected target and has no admitted
comparison, including terminal comparisons. `Monitor.hole_iff_unsafe` gives
the exact semantic bridge under satisfiability.

The label reader satisfies `RejectedTail.RejectedPath`: rejection holds
between rejected prefixes, and every admitted comparison ends at or before
the first rejected cut `J`. Thus admitted endpoints lie in the cone
`s < e ≤ J`. This is not closure of rejection under arbitrary extensions.
See [Monitor/Reader.lean](DeciNSSE/Monitor/Reader.lean) and
[Monitor/Bridge.lean](DeciNSSE/Monitor/Bridge.lean).

### 6. Bound holes over the finite path alphabet

The hole argument applies to any finite alphabet and reader satisfying the
rejected-path invariant. A hole can be chosen with rejected-tail length at
most `B = N^2 + 4*N`. A branching rejected cycle allows a final letter that
breaks short periods, using Fine–Wilf periodicity. Otherwise the rejected
continuation is forced and eventually periodic; tracking state and phase
allows it to be shortened.

For the depth argument, let `J` be the first rejected cut and let a comparison
`s < e` join two cuts with equal reader states. Removing the factor between
them leaves the prefix of length `|w| - (e-s)`, which reaches the same
rejected state as `w`. It cannot precede `J`, so the return gap `e - s` is at
most the rejected-tail length `|w| - J`; this holds for every reader. The
canonical hierarchy repeatedly cuts a word at its last letter; its supports of
reader cores decrease, and a constant nonempty support lasts at most `B + 1`
levels. Counting these plateaus bounds the first unary level by

```text
d = 2 * N * (B + 1) - 1.
```

At the first unary level the canonical word is a power `x^m`, and a hole of
this form can be chosen with `m` at most the number of cores of that level.
Below it, finite summaries of tuples of blocks record transitions,
admissions and equalities. Short representatives preserve these summaries,
so the letter `x` can be replaced by one of bounded expanded length. This
gives a computable length bound `BoundedDepth.holeBound N d`. This bounds
the length of a chosen witness, not the length of every hole. The empty word
and empty alphabet are covered by `RejectedTail.hole_iff_bounded_length`.

Finite enumeration up to this bound decides hole existence.
See [RejectedTail/Decision.lean](DeciNSSE/RejectedTail/Decision.lean) and
[Holes/BoundedDepth.lean](DeciNSSE/Holes/BoundedDepth.lean).

### 7. Transfer to regular and finite trees

Finite graphs realise the least solution, duality, normalisation and median.
Applying them to the spine extension gives a regular countermodel whenever
an arbitrary countermodel exists. Hence regular entailment coincides with
unrestricted entailment.

Finite satisfiability additionally excludes cycle clashes. The least-shape
solution and its sign dual have identical constructor positions; a polarity
selector produces a finite fixed solution. For finite countermodel transfer,
four spines enforce both source extremes and both target non-extremes.
The fourth condition is needed because a finite third median input may be
top; the full constructor tree cannot serve as a finite input in general.
Ranked spine extensions add no cycle clashes, so these conditions can be
realised finitely whenever the original system has a finite solution.

The finite procedure first tests finite satisfiability. If it fails, entailment
is vacuous; otherwise unrestricted entailment gives the answer. All arities
use this same construction. See [Transfer](DeciNSSE/Transfer) and
[Satisfiability/FiniteVariance.lean](DeciNSSE/Satisfiability/FiniteVariance.lean).

## Complexity and scope of the algorithm

The exported procedures are computable definitions with compiled code. They
implement finite searches justified by explicit bounds; a classical choice of
a `Decidable` instance alone would not supply an executable algorithm.
Classical reasoning is used in the proofs of the bounds and correctness.

The bounds are non-elementary: compression is iterated through a hierarchy
whose depth grows with the input. This proves termination in principle and
does not establish PSPACE membership or an optimal complexity bound. The
search is unsuitable for practical type inference.

The theorem covers one constructor with any finite arity and any variance
map. It does not cover arbitrary signatures with multiple constructors. The
hole procedure requires the rejected-path invariant, proved here for the
constructed label readers; it is not an unrestricted decision procedure for
all finite readers with arbitrary admission relations.

## Relation to previous work

- The 1996 [TLCA problem](https://tlca.di.unito.it/opltlca/opltlcasu23.html)
  connects subtype entailment with constraint simplification, citing Pottier
  and Trifonov–Smith. Undecidability of the full first-order theory does not
  settle this restricted implication problem.
- Henglein and Rehof studied the complexity of structural entailment and
  established hardness results for non-structural entailment. See
  [Henglein's publications](https://hjemmesider.diku.dk/~henglein/publications.html)
  and the discussion in
  [Niehren and Priesnitz (1999)](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf).
- [Niehren and Priesnitz (1999)](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf)
  proved PSPACE-completeness for the fragment without explicit top and bottom
  in constraints.
- Niehren and Priesnitz characterised non-structural entailment using cap
  expressions, regular languages and word equations, with a TACS 2001 version
  and a full account in *Information and Computation* (2003). See the
  [published article](https://doi.org/10.1016/S0890-5401(03)00140-8) and
  [author manuscript](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_02.pdf).
- Schubert's 2021 decidability claim was withdrawn because an error in
  Lemma 5.5 invalidated the subsequent construction; see the
  [withdrawal notice](https://arxiv.org/abs/2109.02458).
- Jiang, Cui and Oliveira discuss the open entailment problem in the context
  of type inference in
  [Bidirectional Higher-Rank Polymorphism with Intersection and Union Types, §3.1](https://cuichen.cc/assets/popl25/popl25-extended.pdf).

The present proof is self-contained in Lean and Mathlib. It establishes the
semantic bridge directly through signed constraints, spine clashes and the
label reader, then proves the combinatorial hole bounds. It does not rely on
the published automata characterisation's back-translation, a binary encoding
of paths, or the withdrawn argument. The backend bounds are proved theorems,
not external axioms.

## Building and checking

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build DeciNSSE
```

The package pins Lean and Mathlib to **v4.34.1**. The first command downloads
compiled Mathlib dependencies; the second checks the whole development.

To inspect the logical dependencies, save the following as `Check.lean` and
run `lake env lean Check.lean`:

```lean
import DeciNSSE

#print axioms DeciNSSE.decideEntails
#print axioms DeciNSSE.decideEntailsReg
#print axioms DeciNSSE.decideEntailsFin
#print axioms DeciNSSE.decideEntails_correct
#print axioms DeciNSSE.decideEntailsReg_correct
#print axioms DeciNSSE.decideEntailsFin_correct
```

These declarations use only the usual `propext`, `Classical.choice` and
`Quot.sound`. Lean's kernel checks their proof terms; execution of compiled
procedures also relies on the compiler.

## Repository layout

| Module | Purpose |
| --- | --- |
| [Words](DeciNSSE/Words.lean) | Finite-alphabet paths, powers and periods |
| [Semantics](DeciNSSE/Semantics) | Trees, variance order, normalisation and median |
| [Characterisation](DeciNSSE/Semantics/Characterisation.lean) | Fixed points, representation domains and flat expressiveness |
| [Constraints](DeciNSSE/Constraints) | Flat syntax, satisfaction, entailment and signed closure |
| [Satisfiability](DeciNSSE/Satisfiability) | Least solutions, label clashes and cycle clashes |
| [Transfer](DeciNSSE/Transfer) | Spines, symmetrisation and countermodel transfer |
| [Monitor](DeciNSSE/Monitor) | Exact clash analysis, label readers and semantic bridge |
| [Holes](DeciNSSE/Holes) | Desubstitution, supports and finite compression |
| [RejectedTail](DeciNSSE/RejectedTail) | Tail bounds, return gaps and finite search |
| [Instances](DeciNSSE/Instances.lean) | Product and arrow variance maps |
| [Main](DeciNSSE/Main.lean) | The three public decision procedures |

Every module is reachable from `import DeciNSSE`.

## License

Apache License 2.0
