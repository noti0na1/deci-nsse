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
simplifying inferred types.
[Problem 16 of the TLCA open problem list](https://tlca.di.unito.it/opltlca/opltlcasu23.html)
asks whether it is decidable for bottom, top and one binary constructor, without
fixing the constructor's variance. The theorem covers every variance and all
three tree domains, so it answers that question under each reading.
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
Nested type expressions reduce to this flat form by naming each compound
subterm with a fresh variable; this standard preprocessing is not part of the
formal development.

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

### 2. Recover variance models by the polarity selector

The least-shape solution of a system without label clash keeps a constructor
only where both a lower and an upper constructor bound require it. For a
system closed under sign duality, it has the same constructor positions as its
sign dual. Selecting between the two by the sign of the variable and the
polarity of the path gives a solution fixed by sign duality, provided the
system is sign coherent: each child carries the sign of its parent shifted by
its variance. A fixed solution decodes to a variance solution.
See [Satisfiability/LeastShape.lean](DeciNSSE/Satisfiability/LeastShape.lean)
and [Semantics/Selector.lean](DeciNSSE/Semantics/Selector.lean).

### 3. Express unsafety by a finite spine extension

Closure derives variable inequalities by reflexivity, transitivity and
constructor decomposition. Upper and lower path judgements describe the
bounds at a tree path. A label clash is exactly the obstruction to a
covariant solution; without one, the least shape is a solution.

Four fresh constraint spines enforce the prefix conditions for an unsafe
word: a lower spine from `x⁺` ending in top, a lower spine from `y⁻` ending in
a constructor lower bound, and their sign duals, upper spines from `x⁻` and
`y⁺`. Spine positions carry the sign of their root shifted by the polarity of
the prefix read so far, and the bottom and top fillers come in both signs.
The extension is therefore closed under sign duality and sign coherent. A word
is unsafe exactly when the extension has no label clash: the selected least
shape of the extension restricts to a witness, and a normalised witness
extends along the traces of its roots. Fresh lower positions are sources and
their sign duals sinks; ranks strictly increase along new nonempty paths. At
cut zero the roots are old variables and may coincide. The closure formulas
cover this case without a distinctness assumption.
See [Monitor/Spine.lean](DeciNSSE/Monitor/Spine.lean) and
[Monitor/Closure.lean](DeciNSSE/Monitor/Closure.lean).

### 4. Classify clashes as four kinds of events

Clashes of the extension are exactly inherited clashes or readiness, child,
cross and self events. The spine from `y⁻` adds no new event: by sign duality
its clashes are readiness or cross admissions. Readiness is checked at every
cut. The child test is letter-free and applies at the terminal cut, even with
an empty alphabet. Cross and self events concern repeated suffixes;
self-admission includes both orientations of the sign-flipped labels.

After variance normalisation, an order failure has two sides: at a prefix of
some word, `x` reaches top and `y` does not (top-prefix side), or `y` reaches
bottom and `x` does not (bottom-prefix side). The events are defined once, for the top-prefix side of a covariant
query; the bottom-prefix side uses the order dual of the signed system with
the query reversed.

For a satisfiable original system, an unsafe word is exactly a word without
events. The satisfiability hypothesis excludes inherited clashes and is
necessary for this model-existence argument.
See [Monitor/Clash.lean](DeciNSSE/Monitor/Clash.lean),
[Monitor/Events.lean](DeciNSSE/Monitor/Events.lean) and
[Monitor/Semantics.lean](DeciNSSE/Monitor/Semantics.lean).

### 5. Read the events with a finite label monitor

A state contains upper and lower label sets and a Boolean latch for earlier
readiness. Current readiness and the child condition complete the acceptance
test. For `m` variables there are `2 * 4^m` states; the signed input thus uses
`N = 2 * 4^(2*k)` states (`Monitor.card_state`). One reader serves both sides:
the bottom-prefix monitor is the reader of the order dual with the query
reversed.

A comparison has cuts `s < e ≤ |w|` such that `w.drop e` is a prefix of
`w.drop s`. It is admitted when the monitor states at those cuts satisfy the
cross or self relation. A *hole* reaches a rejected target and has no admitted
comparison, including terminal comparisons. `Monitor.hole_iff_unsafe` gives
the exact semantic bridge under satisfiability.

The label reader satisfies `RejectedTail.RejectedPath`: rejection holds
between rejected prefixes, and every admitted comparison ends at or before
the first rejected cut `J`. Thus admitted endpoints lie in the cone
`s < e ≤ J`. This is not closure of rejection under arbitrary extensions.
The cone has a simple cause: at a rejected cut no upper bound has a
constructor child, so the upper set is empty one letter later and stays empty,
while both admission relations need a nonempty upper set at their second cut.
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
Ordinary loop deletion does not suffice here: removing the factor between two
equal states keeps the final state but can create a new admitted comparison.
Below the unary level, finite summaries of tuples of blocks therefore record
transitions, admissions and equalities, and all blocks of a level are
shortened simultaneously. Short representatives preserve these summaries,
so the letter `x` can be replaced by one of bounded expanded length. This
gives a computable length bound `BoundedDepth.holeBound N d`. This bounds
the length of a chosen witness, not the length of every hole. The empty word
and empty alphabet are covered by `RejectedTail.hole_iff_bounded_length`.

Finite enumeration up to this bound decides hole existence.
See [RejectedTail/Decision.lean](DeciNSSE/RejectedTail/Decision.lean) and
[Holes/BoundedDepth.lean](DeciNSSE/Holes/BoundedDepth.lean).

### 7. Transfer to regular and finite trees

The least-shape label at a path depends only on the sets of lower and upper
bounds at that path, and both sets are updated letter by letter. Pairs of such
sets are the states of a finite graph whose unfolding is the least shape; a
polarity bit realises the selector and decoding on graphs. For an unsafe word,
the selected least shape of the four-spine extension is therefore regular, and
decoding its restriction gives a regular countermodel at the same word. Hence
regular entailment coincides with unrestricted entailment.
See [Satisfiability/ShapeGraph.lean](DeciNSSE/Satisfiability/ShapeGraph.lean)
and [Transfer/Regular.lean](DeciNSSE/Transfer/Regular.lean).

Finite satisfiability additionally excludes cycle clashes. Without them the
least-shape solution has bounded depth, and the polarity selector keeps its
domain, so it produces a finite fixed solution. The same argument transfers
countermodels. Since the spine extension is ranked, a nonempty cycle cannot
pass through its sources or sinks, so it adds no cycle clash. When the original
system has a finite solution, the selected least shape of the extension of an
unsafe word is therefore finite, and its decoding is a finite countermodel.

The finite procedure first tests finite satisfiability. If it fails, entailment
is vacuous; otherwise unrestricted entailment gives the answer. All arities
use this same construction. See [Transfer](DeciNSSE/Transfer) and
[Satisfiability/FiniteVariance.lean](DeciNSSE/Satisfiability/FiniteVariance.lean).

## Complexity and scope of the algorithm

The exported procedures are computable definitions with compiled code. They
implement finite searches justified by explicit bounds; a classical choice of
a `Decidable` instance alone would not supply an executable algorithm.
Classical reasoning is used in the proofs of the bounds and correctness.

The label reader has `N = 2 * 4^(2*k)` states, and the tail and depth bounds
are polynomial in `N`. The bounds are nevertheless non-elementary: compression
is iterated once per level of a hierarchy whose depth grows with the input.
This proves termination in principle and
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
label reader, then proves the combinatorial hole bounds. It uses neither
direction of the published automata characterisation, a binary encoding of
paths, or the withdrawn argument. The backend bounds are proved theorems,
not external axioms.

## An earlier proof for the binary covariant case

The first version of this repository (up to commit `79950d0`) decided
entailment only for one binary covariant constructor. Its semantic reduction
mechanized the forward cap-automaton characterisation of Niehren and
Priesnitz: for a satisfiable system, two cap automata accept exactly the safe
paths, once states made ready by the bottom, top or reflexivity rules count as
final. Holes were read from the transition monoids of these automata, and the
tail, depth and compression bounds were proved for the resulting readers over
the binary alphabet.

The current development replaces that reduction. The cap-automaton route is
tied to its signature: other arities would need alphabet reductions between
cap automata, and contravariance would need new automata with a new
completeness proof. The direct route is also better in its own right:

- **One construction replaces several.** The chains of fresh variables that
  the earlier proof used in its completeness argument and its transfers
  became the four-spine extension. Its clash analysis defines the reader, and
  its selected least shape gives the countermodels in all three domains. Cap
  automata, the finality convention and cap elimination are no longer needed.
- **Admissions have a semantic reading.** They are cross and self events of
  the constraints, rather than closed P-edges in a transition monoid.
- **Readers are smaller, and their bounds are generic.** The label reader has
  `2 * 4^(2*k)` states, and one reader serves both sides. A cap automaton has
  up to `(k+1)^2 + 1` states, and its transition monoid can have `2^(n^2)`
  elements for `n` states, so the rejected-tail bound drops from `2^O(k^4)` to
  `2^O(k)`. The return-gap bound now holds for every reader, and compression
  is needed only at a unary level.
- **Generality did not increase the size.** The development has 57 modules and
  about 11,800 lines of Lean, against 58 modules and about 12,200 lines for the
  binary one.

The cost is a longer semantic reduction, with four signed spines and their
bookkeeping. The combinatorial core (rejected tail, depth and compression)
carried over from the binary alphabet to arbitrary finite alphabets without a
change of method.

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
| [Semantics](DeciNSSE/Semantics) | Trees, variance order, normalisation and polarity selection |
| [Characterisation](DeciNSSE/Semantics/Characterisation.lean) | Fixed points, representation domains and flat expressiveness |
| [Constraints](DeciNSSE/Constraints) | Flat syntax, satisfaction, entailment and signed closure |
| [Satisfiability](DeciNSSE/Satisfiability) | Least shapes, their finite graphs, label clashes and cycle clashes |
| [Transfer](DeciNSSE/Transfer) | Ranked extensions, cycle preservation and countermodel transfer |
| [Monitor](DeciNSSE/Monitor) | Exact clash analysis, label readers and semantic bridge |
| [Holes](DeciNSSE/Holes) | Desubstitution, supports and finite compression |
| [RejectedTail](DeciNSSE/RejectedTail) | Tail bounds, return gaps and finite search |
| [Instances](DeciNSSE/Instances.lean) | Product and arrow variance maps |
| [Main](DeciNSSE/Main.lean) | The three public decision procedures |

Every module is reachable from `import DeciNSSE`.

## License

Apache License 2.0
