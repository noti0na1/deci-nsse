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
The proof works directly over paths in `Fin n` and proves an elementary
hole-length bound. The resulting exhaustive searches establish decidability
in principle; their universal bounds are too large for practical type inference.
The [Lean solver](#lean-solver) `nsse` searches for certificates instead and
checks them with proved checkers, so every answer it prints is correct.

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
[Semantics/Characterization.lean](DeciNSSE/Semantics/Characterization.lean), as
`Characterization.le_definable_iff` and `Characterization.nullary_not_definable`.
The decision interface accepts the queried inequality directly at every arity.

### Which trees are allowed as solutions?

| Domain | Meaning | Lean representation |
| --- | --- | --- |
| Arbitrary trees | All finite and infinite trees | `Tree n` |
| Regular trees | Trees with finitely many distinct rooted subtrees | Unfoldings of `RGraph n` |
| Finite trees | Trees with finitely many nodes | Images of `FTree n` |

The representation claims are proved by `Characterization.unfold_range_iff`
and `Characterization.toTree_range_iff`. The order characterization is
`Characterization.treeLe_eq_gfp`; `Characterization.lfp_ne_treeLe` shows that
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

Countermodels can be computed from a supplied side `θ : Side` and word
`w : List (Fin n)`. The assignment `extractRegular c ϕ x y θ w : V k → RGraph n`
satisfies `ϕ` and refutes `x ≤ y` when `Monitor.satB c ϕ = true` and `w` is a
hole of `Monitor.sideMonitor c ϕ x y θ`, by `extractRegular_spec`.
The Boolean check `refutesB c ϕ x y θ w` combines these two conditions;
`refutesB_correct` proves non-entailment, and `not_entails_iff_refutesB` states
that every non-entailment has such a certificate. Under `SatisfiableFin c ϕ`,
`extractFinite c ϕ x y θ w : V k → FTree n` gives the corresponding finite
countermodel, by `extractFinite_spec` for a hole or `extractFinite_of_unsafe`
for an unsafe word. Both extractors are computable; the finite extractor
truncates the regular unfolding at the proved depth bound. See
[Countermodels.lean](DeciNSSE/Countermodels.lean).

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

### API map

`import DeciNSSE` makes all of the following available; `import DeciNSSE.Main`
suffices for the three original procedures. Names are in namespace `DeciNSSE`.
Each decider of the first three rows returns a `Decidable` instance and has a
correctness theorem named by appending `_correct`, of the form of
`decideEntails_correct` and without premises. The packed decider has no
separate correctness theorem, since its type `Decidable (Entails c ϕ x y)`
already determines its value; the solver is correct by `solve_correct`.

| Interface | Declarations | Scope | Defined in |
| --- | --- | --- | --- |
| Original deciders | `decideEntails`, `decideEntailsReg`, `decideEntailsFin` | Every arity and variance; arbitrary, regular and finite trees. Hole search by enumeration up to `RejectedTail.holeLengthBound`. | [Main](DeciNSSE/Main.lean) |
| Summary deciders | `decideEntailsSummary`, `decideEntailsRegSummary`, `decideEntailsFinSummary` | Every arity and variance; the three domains. Hole search by the summary search (see [Complexity](#complexity-and-scope-of-the-algorithm)). | [Complexity/SummaryDecision](DeciNSSE/Complexity/SummaryDecision.lean) |
| Unary deciders | `decideEntailsUnary`, `decideEntailsRegUnary`, `decideEntailsFinUnary` | Arity one only (`c : Fin 1 → Bool`); the three domains. Hole search below the reader state count. | [Complexity/Unary](DeciNSSE/Complexity/Unary.lean) |
| Certifying solver | `solve`, `solveWithFuel`, with `solve_correct` and `solveWithFuel_correct` | Every arity and variance; arbitrary trees, hence regular trees by `entailsReg_iff_entails`. Returns checked evidence and a countermodel. | [Solver](DeciNSSE/Solver.lean) |
| Packed decider | `Solver.decideEntailsPacked` | Every arity and variance; arbitrary trees. | [Solver/Complete](DeciNSSE/Solver/Complete.lean) |

All nine deciders of the first three rows are instances of
`Monitor.decideEntailsOfMonitors`, `Monitor.decideEntailsRegOfMonitors` and
`Monitor.decideEntailsFinOfMonitors` in
[Monitor/Decision.lean](DeciNSSE/Monitor/Decision.lean), which take the two side
monitors and a side-hole decider. They are `@[instance_reducible] def`s rather
than instances, because several of them decide the same proposition; install one
with `letI` or pass it to `@decide`.

Only `decideEntails` is redirected by the compiler. The `@[csimp]` lemma
`Solver.decideEntails_eq_decideEntailsPacked` makes compiled code of
`decideEntails` run `Solver.decideEntailsPacked` in every module that imports
`DeciNSSE.Solver`, and so under `import DeciNSSE`. The decision value is the
same. The packed decider computes the reader state count from its formula and
enumerates only words. The other eight deciders evaluate the packaged side
monitors, whose `Fintype` instance enumerates every reader state.

## Proof overview

The proof reduces a countermodel to a finite word called a *hole* in one of
two finite monitors, then bounds the length of a hole witness. All reductions,
bounds and transfer arguments are proved in Lean.

### 1. Normalize variance and translate to signed variables

Normalization exchanges bottom and top according to path polarity and leaves
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
constructor decomposition. Upper and lower path judgments describe the
bounds at a tree path. A label clash is exactly the obstruction to a
covariant solution; without one, the least shape is a solution.

Four fresh constraint spines enforce the prefix conditions for an unsafe
word: a lower spine from `x⁺` ending in top, a lower spine from `y⁻` ending in
a constructor lower bound, and their sign duals, upper spines from `x⁻` and
`y⁺`. Spine positions carry the sign of their root shifted by the polarity of
the prefix read so far, and the bottom and top fillers come in both signs.
The extension is therefore closed under sign duality and sign coherent. A word
is unsafe exactly when the extension has no label clash: the selected least
shape of the extension restricts to a witness, and a normalized witness
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

After variance normalization, an order failure has two sides: at a prefix of
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
`N = 2 * 4^(2*k)` states (`Monitor.card_state`, `Monitor.card_sideMonitor`).
One reader serves both sides:
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
most `B = 4*N - 2`. A branching rejected cycle allows a final letter that
breaks short periods, using Fine–Wilf periodicity. Otherwise the rejected
continuation is forced and eventually periodic with some period `p ≤ N`. Its
transient part can be replaced by a path of at most `N` letters. Rejection
holds between rejected prefixes, so every cut after the first rejection is
rejected, and the word can be cut at most `N + p ≤ 2*N` letters after it.

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

Before shortening blocks, merge isolated letters with the same finite exchange
type. This preserves holehood and canonical depth, and does not increase length
or any dictionary. In the resulting normal form, boundary pairs propagate
linearly between levels. If `D` is the first unary level, then for
`1 ≤ i < D ≤ d` the checked bounds are

```text
2 * b_i ≤ (A - 1) * (3^(D - 1 - i) - 1),
g_i ≤ 1 + (A - 1) * 3^(D - 1 - i),
```

where `b_i` counts ordered nonterminal boundary pairs and `g_i` counts distinct
level letters. The unary top has at most one letter and no boundary pairs;
the level immediately below it also has no boundary pairs. Set

```text
C(N,d) = N^N * 2^(2*N^2 + 4*N*(N+d)*(d+1) + 3*N),
A(N,d) = d + 1 + C(N,d),
G(N,d) = 2 + A(N,d) * 3^d,
K(M,g) = M^((M+1)*g) * 2^(M*(M+1)*g + (1+(M+1)^2)*g^2),
L(N,d) = (N+d+1) * K(N+d+1,G(N,d))^d.
```

In Lean, `C`, `A`, `G` and `L` are `NormalForm.normalTypeBound`,
`NormalForm.normalAllowance`, `ElementaryBound.dictionaryBound` and
`ElementaryBound.lengthBound`. `K(M,g)` is `BoundedDepth.colBound M g`, the
state count of the column automaton, and `BoundedDepth.descentFactor N d g` is
`K(N+d+1,g)`. The depth `d` is `RejectedTail.holeDepthBound N`, and
`B = 4*N - 2` is the bound of `RejectedTail.boundedRejectedTail_of_rejectedPath`.

Every positive-level dictionary through the unary top can be bounded by `G`.
There is no bound required on the level-zero alphabet. At the unary level,
a hole `x^m` can be chosen with `m` at most the number of cores of that level.
Below it, simultaneous column compression preserves transitions, admissions,
and block equalities. Deduplicating the supports keeps every column call
within the original bounded dictionaries.

`ElementaryBound.exists_short_hole` proves the length bound `L(N,d)` for any
finite-core lettered monitor with a hole of depth at most `d`. It needs no
rejected-path hypothesis. The backend uses
`RejectedTail.holeLengthBound N = L(N, RejectedTail.holeDepthBound N)` and
proves (`RejectedTail.holeLengthBound_le`)

```text
holeLengthBound N ≤ 2^(2^(1280 * (N+1)^5)).
```

Here `G(N,d) ≤ 2^E` and `L(N,d) ≤ 2^(2^(5*E+3))` for the exponent
`E = ElementaryBound.dictionaryExponent N d`
(`ElementaryBound.dictionaryBound_le`, `ElementaryBound.lengthBound_le`). At the
depth bound, `d ≤ 8*N^2` (`RejectedTail.holeDepthBound_le`) and
`E < 256*(N+1)^5` (`RejectedTail.dictionaryExponent_hole_lt`), whence the
constant `1280 = 5 * 256`. This bounds the length of a chosen witness. The
empty word and empty alphabet are covered by
`RejectedTail.hole_iff_bounded_length`; `RejectedTail.hole_iff_search` reduces
hole existence to enumeration up to this bound.
See [RejectedTail/Decision.lean](DeciNSSE/RejectedTail/Decision.lean),
[Holes/ElementaryBound.lean](DeciNSSE/Holes/ElementaryBound.lean),
[Holes/BoundedDepth.lean](DeciNSSE/Holes/BoundedDepth.lean) and
[Holes/Columns.lean](DeciNSSE/Holes/Columns.lean).

### 7. Transfer to regular and finite trees

The least-shape label at a path depends only on the sets of lower and upper
bounds at that path, and both sets are updated letter by letter. Pairs of such
sets are the states of a finite graph whose unfolding is the least shape; a
polarity bit realizes the selector and decoding on graphs. For an unsafe word,
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

The label reader has `N = 2 * 4^(2*k)` states. The checked hole-length bound is
`2^(2^(1280 * (N+1)^5))`, doubly exponential in a polynomial in the state
count. Substituting the reader size gives the explicit path-length
allowance `2^(2^(1280 * (2 * 4^(2*k) + 1)^5))`. This bounds the unsafe path
used to construct a countermodel, not the number of nodes in an expanded tree.

The exhaustive hole searches of the original deciders enumerate words up to
`RejectedTail.holeLengthBound N`.
These universal searches remain unsuitable for practical type inference; the
[Lean solver](#lean-solver) uses them only as a fallback.

[Complexity](DeciNSSE/Complexity.lean) formalizes the combinatorial content of
the complexity bounds. The complexity classes themselves, space-bounded
machines and Savitch's theorem, are not formalized.

* **Summary search.** A search over level summaries of the block hierarchy
  decides holes of bounded depth without storing the word. It is sound and
  complete (`Complexity.Summary.summarySearch_sound`,
  `Complexity.Summary.summarySearch_complete`), and for the label readers its
  configurations number at most `2^((n+1)^2 * 2^(2^(20*k+20)))`
  (`Complexity.Summary.card_config_label_le`), so one configuration fits in
  doubly exponential space. These configuration bounds support the usual
  space-bounded reachability argument for the 2-EXPSPACE bound. The executable
  implementation `Complexity.Summary.summarySearch` computes the set of
  reachable configurations by saturation (`Complexity.reachSet`) and is not
  proved to meet that space bound. `decideEntailsSummary`,
  `decideEntailsRegSummary` and `decideEntailsFinSummary` decide entailment
  through this search.
* **Arity one.** A reader over a one-letter alphabet with a hole has one of
  length at most `N - 1` (`Complexity.Unary.exists_hole_length_le`).
  `decideEntailsUnary` and its regular and finite versions follow the run to
  the first rejected cut, which lies below `N`, and test that one word
  (`Complexity.Unary.hole_iff_firstRejectedCut`).
* **Hardness.** For every arity `n ≥ 2` and the covariant constructor,
  `Complexity.hardnessSystem n M` has linearly many literals
  (`Complexity.hardnessSystem_length_le`) and entails `x ≤ r` exactly when the
  binary automaton `M` accepts every word, over arbitrary, regular and finite
  trees (`Complexity.entails_hardnessSystem_iff` and its two variants).
  Universality of nondeterministic automata is PSPACE-hard, so entailment is
  PSPACE-hard for every fixed arity at least two.
* **Long witnesses.** For every `n ≥ 2` and `k`, the system
  `Complexity.expSystem n k` has `9k + 31` variables, a finite solution and no
  entailment in any domain, and its shortest counterexample word has length
  exactly `2(k+1)2^k`, both among the holes of the side monitors
  (`Complexity.expSystem_shortest_hole`) and among the words accepted by
  `refutesB` (`Complexity.expSystem_shortest_refutesB`). Every answer of the
  Lean solver on it is a refutation at least that long
  (`Complexity.expSystem_result`).

The theorem covers one constructor with any finite arity and any variance
map. It does not cover arbitrary signatures with multiple constructors. The
hole procedure requires the rejected-path invariant, proved here for the
constructed label readers; it is not an unrestricted decision procedure for
all finite readers with arbitrary admission relations.

## Lean solver

The `nsse` executable answers entailment queries in practice. It searches for
a certificate, checks it with proved checkers, and builds a countermodel for a
negative answer. [Solver.lean](DeciNSSE/Solver.lean) exports

```lean
def solve (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) : Result c ϕ x y

theorem solve_correct :
  (solve c ϕ x y).answer = true ↔ Entails c ϕ x y
```

and `solveWithFuel_correct`, the same statement for every search budget,
terminal window and countermodel setting.

```sh
lake build nsse nsse-check
.lake/build/bin/nsse examples/periodic.json
.lake/build/bin/nsse examples/modular.json --no-countermodel
sh examples/check.sh
```

### Input

A problem is a JSON object:

```json
{"k": 4, "variance": [0, 0], "lits": [["le", 0, 2, 3], ["ge", 1, 2, 3]], "x": 0, "y": 1}
```

* `k`: the number of variables, numbered from 0.
* `variance`: one entry per argument, `0` covariant and `1` contravariant. For
  a covariant constructor, `"arity": n` may be given instead; `"arity": 0`
  selects the nullary constructor. Without either, the constructor is binary
  and covariant.
* `lits`: the flat literals. `["bot", u]` is `u = ⊥`, `["top", u]` is `u = ⊤`,
  `["le", u, a0, …]` is `u ≤ f(a0, …)` and `["ge", u, a0, …]` is
  `f(a0, …) ≤ u`, with one child variable per argument.
* `x`, `y`: the query `x ≤ y` (defaults 0 and 1).

These are the literal forms of `DeciNSSE.Constraint`; the arrow `a → b` is
`f(a, b)` with variance `[1, 0]`. Other keys are ignored.

### Output and options

Standard output is one JSON object with `answer` (`true` when the constraints
entail the query), `used_fallback`, and a `certificate`:

| `certificate.kind` | Answer | Content |
| --- | --- | --- |
| `unsat` | true | The constraints have no solution. |
| `entailment` | true | A closed cover of each query side, `left` and `right`. |
| `refutation` | false | A side, `"l"` or `"r"`, and a word that is a hole of that side's reader. |
| `complete` | true | No certificate: the complete decider answered. |

A negative answer also has a `countermodel`: an array indexed by variables,
each entry a graph with a `root` and `nodes`. Nodes are `["B"]`, `["T"]` or
`["F", child0, …]`, with indices local to the graph. Its unfolding satisfies
every constraint and violates the query. The elapsed time is written to
standard error; malformed input exits with status 2.

| Option | Meaning |
| --- | --- |
| `--fuel N` | Search budget in turns (default 100000). |
| `--window N` | Window of terminal comparisons in entailment covers (default 0). |
| `--no-countermodel` | Do not build the countermodel of a negative answer. |

### Examples

| File | Answer | What it shows |
| --- | --- | --- |
| `transitivity.json` | entailed | `x ≤ f(a, b)` and `f(a, b) ≤ y` give `x ≤ y` |
| `reverse.json` | not entailed | the same constraints do not give `y ≤ x` |
| `arrow.json` | entailed | transitivity for the arrow, variance `[1, 0]` |
| `mixed-ternary.json` | entailed | transitivity for a ternary constructor, variance `[1, 0, 1]` |
| `infinite-tree.json` | not entailed | `x = f(x, x)` forces the infinite constructor tree |
| `nullary.json` | entailed | arity zero |
| `periodic.json` | entailed | rays alone cannot prove it; terminal comparisons do |
| `modular.json` | not entailed | 20 variables; the shortest hole is `0^209 1` |
| `deep-context.json` | entailed | 66 variables; a cover of rays alone would need 2^32 rays |

`sh examples/check.sh` solves all nine, compares the answers, and rechecks
each certificate with `nsse-check`. Each example takes well under a second,
except that building the 4,045-node countermodel of `modular.json` takes
about 75 seconds (about one second with `--no-countermodel`).

### How it works

A scout, an iterative-deepening refuter, and a breadth-first prover take turns
on both query sides. The prover explores the product of the reader with ray
and terminal-comparison automata and adds all admitted comparisons of its
shortest uncovered word as rays. Active-period masks track suffix
comparisons. The search uses arrays, bit masks and hash sets and needs no
correctness proof: only a certificate accepted by the checkers yields an
answer. If the search exhausts its fuel or a candidate is rejected,
`decideEntails` supplies the answer and `used_fallback` is `true`; this
fallback uses the proved length bound and can be impractically slow. In
compiled code it runs `Solver.decideEntailsPacked`, by the `@[csimp]` lemma
`Solver.decideEntails_eq_decideEntailsPacked`; only `decideEntails` is
redirected in this way (see the [API map](#api-map)). Fuel bounds the search,
not the total running time.

The checkers use packed closure rows, shared reader transition tables and
cached prefix states. Refinement lemmas connect them to the finite-set closure
and reader of the proof; neither checking nor countermodel validation
enumerates the reader's state space. The countermodel is the reachable part
of `extractRegular` from [Countermodels.lean](DeciNSSE/Countermodels.lean)
with the same unfolding (`Solver.extractReachable_unfold`), so it is part of
the verified result.

### Checking certificates

`nsse-check problem.json certificate.json` checks a certificate produced by
`nsse` or by another tool. The second file is either a complete `nsse` result
or a bare certificate:

```json
{"kind":"unsat"}
{"kind":"refutation","side":"l","word":[]}
{"kind":"entailment",
 "left":{"window":0,"rays":[],"access":[[],[0],[1]]},
 "right":{"window":0,"rays":[],"access":[[],[0],[1]]}}
```

The last object illustrates the schema; a real cover lists the access words
of a closed product for the particular problem. Success prints `VERIFIED` and
exits with status 0; rejection prints a reason and exits with status 1; file
or usage errors exit with status 2.

Words are arrays of letters smaller than the arity. A cover has a
natural-number `window`, a list `rays` of pairs `[u, v]` of words with nonempty
`v`, and a list `access` of words. Lean computes every product state from its
access word. It checks that each ray is admitted from the reader state after
`u` to the state after `u ++ v`, that the initial product state is listed,
that every listed state is covered, and that all its letter successors are
listed. A covered state accepts, holds a terminal residual, or has a mature
ray position, and each of these excludes a hole, so finite closure covers all
words. A refutation also checks that the system is satisfiable, and an
`unsat` certificate that it is not. `Certificates.checkEntailment_sound` and
`Certificates.checkRefutation_sound` in
[Certificates.lean](DeciNSSE/Certificates.lean) prove `Entails` or its
negation for the specification checkers;
`Certificates.checkEntailment_sound_regular`,
`Certificates.checkEntailment_sound_finite` and
`Certificates.checkRefutation_sound_regular` give the regular- and finite-tree
statements. A refutation need not refute finite entailment, which can hold
vacuously. `nsse` and `nsse-check` run the packed checkers of
[Solver/Checked.lean](DeciNSSE/Solver/Checked.lean):
`Solver.Checked.checkEntailmentPacked_sound` proves `Entails` for an accepted
entailment certificate, and `Solver.Checked.checkRefutationPacked_eq_refutesB`
identifies the packed refutation check with `refutesB`.

### What is trusted

The Lean kernel checks the proofs. Running the executables also trusts the
compiled code, including the compiler, the runtime, and JSON parsing and
serialization. `solve_correct`, `solveWithFuel_correct` and
`Solver.extractReachable_unfold` use only `propext`, `Classical.choice` and
`Quot.sound` (see [Building and checking](#building-and-checking)).

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
- Niehren and Priesnitz characterized non-structural entailment using cap
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
- R. Sato's Lean 4 formalization
  [nsse-lean](https://github.com/ryosu-sato/nsse-lean) (October 2026)
  independently decides entailment for bottom, top and one constructor of
  arity `d > 0`, covariant or with arbitrary variance, over arbitrary, regular
  and finite trees, with nested term premises and queries and computable
  countermodels. It re-proves the forward Niehren–Priesnitz cap-automaton
  characterization and decides universality of the resulting restricted cap
  set expressions; for the covariant case it also proves a counted elementary
  bound of seven nested exponentials.
- The [subtype-entailment](https://github.com/mhenglein/subtype-entailment)
  project of F. Henglein, J. Rehof and M. Henglein (2026) independently
  decides entailment for bottom and binary product without top, with a
  Lean-checked decision theorem over arbitrary and finite trees. Its paper,
  *Subtype entailment for bottom and binary product, with an explicit-top
  extension*, extends the arbitrary-tree result to an explicit top for the
  same product; contravariant arguments, and hence arrows, are not covered.

The present proof is self-contained in Lean and Mathlib. It establishes the
semantic bridge directly through signed constraints, spine clashes and the
label reader, then proves the combinatorial hole bounds. It uses neither
direction of the published automata characterization, a binary encoding of
paths, or the withdrawn argument. The backend bounds are proved theorems,
not external axioms; the hole-length bound is elementary for every variance
and also covers arity zero.

## An earlier proof for the binary covariant case

The first version of this repository (up to commit `79950d0`) decided
entailment only for one binary covariant constructor. Its semantic reduction
mechanized the forward cap-automaton characterization of Niehren and
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
  up to `(k+1)^2 + 1` states, and its transition monoid can have `2^(s^2)`
  elements for `s` states, so the rejected-tail bound drops from `2^O(k^4)` to
  `2^O(k)`. The return-gap bound now holds for every reader, and compression
  is needed only at a unary level.

The cost is a longer semantic reduction, with four signed spines and their
bookkeeping. The combinatorial core (rejected tail, depth and compression)
carried over from the binary alphabet to arbitrary finite alphabets without a
change of method.

## Building and checking

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The package pins Lean and Mathlib to **v4.35.0**. The first command downloads
compiled Mathlib dependencies; the second checks the whole development and
builds the executables `nsse` and `nsse-check`.

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
#print axioms DeciNSSE.solve_correct
#print axioms DeciNSSE.solveWithFuel_correct
#print axioms DeciNSSE.Solver.extractReachable_unfold
#print axioms DeciNSSE.RejectedTail.holeLengthBound_le
#print axioms DeciNSSE.decideEntailsSummary_correct
#print axioms DeciNSSE.Complexity.Summary.card_config_label_le
#print axioms DeciNSSE.decideEntailsUnary_correct
#print axioms DeciNSSE.Complexity.Unary.exists_hole_length_le
#print axioms DeciNSSE.Complexity.entailsFin_hardnessSystem_iff
#print axioms DeciNSSE.Complexity.expSystem_shortest_refutesB
```

These declarations use only the usual `propext`, `Classical.choice` and
`Quot.sound`. Lean's kernel checks their proof terms; execution of compiled
procedures also relies on the compiler.

## Repository layout

The library has 112 Lean files under `DeciNSSE/`, with 21,223 lines including
the root module `DeciNSSE.lean`; the counts include comments, docstrings and the
three executable front-end modules. Namespaces are relative to `DeciNSSE`;
"top level" means `DeciNSSE` itself, and dotted names such as `Tree.Le` live
in the namespace of their prefix.

| Module | Namespace | Purpose |
| --- | --- | --- |
| [Words](DeciNSSE/Words.lean) | `Words` | Finite-alphabet paths, powers and periods |
| [Semantics](DeciNSSE/Semantics): Sym, Tree, Finite, Regular, Order, Normalization, Safety | top level, `Sym`, `Tree`, `FTree`, `RGraph`, `Safety` | Labels, trees, finite terms, regular graphs, the variance order, normalization and finite witnesses to order failure |
| [Semantics/Selector](DeciNSSE/Semantics/Selector.lean) | `SignSelection` | Polarity selection for signed solutions |
| [Semantics/Characterization](DeciNSSE/Semantics/Characterization.lean) | `Characterization` | Fixed points, representation domains and flat expressiveness |
| [Constraints](DeciNSSE/Constraints) | top level, `Covariant`, `Closure`, `ConstraintDual`, `PathBounds`, `Signs` | Flat syntax, satisfaction, entailment, closure, duals, path bounds and the signed translation |
| [Satisfiability](DeciNSSE/Satisfiability) | top level, `PathDecision`, `FiniteSat`, `FiniteVariance`, `RGraph` | Least shapes, their finite graphs, label clashes, cycle clashes and finite satisfiability |
| [Transfer/Safety](DeciNSSE/Transfer/Safety.lean) | top level | The query sides `Side`, unsafe words `Unsafe`, and `entails_iff_not_sideUnsafe` |
| [Transfer](DeciNSSE/Transfer): RankedExtension, Cycle | `Ranked` | Ranked source and sink extensions, cycle clashes under extension |
| [Transfer](DeciNSSE/Transfer): Regular, Finite | `RegularTransfer`, `FiniteTransfer` | Countermodel transfer to regular and finite trees |
| [Monitor](DeciNSSE/Monitor): Spine, Closure, Clash | `Spine.Closure` | The four-spine extension, its closure and its clashes |
| [Monitor](DeciNSSE/Monitor): Events, Semantics | `Events` | Clash events and their semantics |
| [Monitor](DeciNSSE/Monitor): Reader, Bridge, Interface, Decision | `Monitor` | Label readers, side readers and monitors, the semantic bridge and the monitor deciders |
| [Holes/Basic](DeciNSSE/Holes/Basic.lean) | `Holes` | Readers, comparisons and holes |
| [Holes/Hierarchy](DeciNSSE/Holes/Hierarchy.lean) and [Holes/Hierarchy/](DeciNSSE/Holes/Hierarchy): Expansion, Derived, Canonical, Starts, Unary, Reader | `LetteredHierarchy` | The canonical hierarchy: expansion, derived monitors, canonical decomposition, start cores, unary levels and readers as lettered monitors |
| [Holes/Depth](DeciNSSE/Holes/Depth.lean) | `HierarchyDepth` | Canonical depth |
| [Holes](DeciNSSE/Holes): Cores, StartCores, CoreOccurrences, Supports | `Cores`, `StartCores`, `CoreOccurrences`, `Supports` | Cores, start cores and supports of hierarchy levels |
| [Holes](DeciNSSE/Holes): Packets, Desubstitution | `Packets`, `Desubstitution` | Tuples of blocks, marker codes and desubstitution |
| [Holes](DeciNSSE/Holes): CoAlignment, Exchange | `CoAlignment`, `CoAlignment.Lettered`, `Exchange` | Lettered monitors, comparison alignment and exchange types |
| [Holes](DeciNSSE/Holes): LevelMaps, NormalForm, BoundaryPairs | `LevelMaps`, `NormalForm`, `BoundaryPairs` | Level maps, the isolated-letter normal form and boundary-pair propagation |
| [Holes](DeciNSSE/Holes): Agree, Columns, BoundedDepth | `BoundedDepth` | Agreement on a support, the column automaton and compression at bounded depth |
| [Holes/ElementaryBound](DeciNSSE/Holes/ElementaryBound.lean) | `ElementaryBound` | Dictionary and length bounds for holes of bounded depth |
| [RejectedTail](DeciNSSE/RejectedTail) | `RejectedTail` | Rejected-path property, tail bound, return gap, depth and finite search |
| [Instances](DeciNSSE/Instances.lean) | top level | Product and arrow variance maps |
| [Main](DeciNSSE/Main.lean) | top level | The three original decision procedures |
| [Countermodels](DeciNSSE/Countermodels.lean) | top level | `refutesB` and computable regular and finite countermodels |
| [Certificates](DeciNSSE/Certificates.lean) and [Certificates/Product](DeciNSSE/Certificates/Product.lean) | `Certificates` | Certificate formats, covering products, specification checkers and their soundness |
| [Certificates/Json](DeciNSSE/Certificates/Json.lean) | `Certificates.Json` | JSON problems and certificate verification with the packed checkers |
| [Certificates/Command](DeciNSSE/Certificates/Command.lean) | none (`main`) | The executable `nsse-check` |
| [Solver](DeciNSSE/Solver.lean) and [Solver/](DeciNSSE/Solver) | top level, `Solver`, `Solver.Checked`, `Solver.Graph`, `Solver.Mask`, `Solver.Search` | The certifying solver: packed readers and checks, the packed decider, the search and reachable countermodels |
| [Solver/Command](DeciNSSE/Solver/Command.lean) | `Solver.Command` (and `main`) | The executable `nsse` |
| [Complexity](DeciNSSE/Complexity.lean) | none | Overview and imports of the complexity modules |
| [Complexity](DeciNSSE/Complexity): Reach, SummaryTables, SummaryColumns, SummaryGraph, SummarySound, SummaryComplete, SummaryBounds, SummaryDecision | `Complexity`, `Complexity.Summary`; deciders top level | Reachable sets, the summary search, its correctness and configuration bounds, and the summary deciders |
| [Complexity](DeciNSSE/Complexity): Unary, UnaryExamples | `Complexity.Unary`; deciders top level | Holes over one letter and the arity-one deciders, with kernel-checked examples |
| [Complexity](DeciNSSE/Complexity): BinNFA, Directions, FiniteTrees | `Complexity`, `Complexity.BinNFA`, `Complexity.Directions`, `Complexity.FiniteTrees` | Binary automata, child layouts and finite trees shared by the lower bounds |
| [Complexity](DeciNSSE/Complexity): HardnessCode, HardnessSystem, HardnessSolutions, HardnessCountermodel, Hardness | `Complexity`, `Complexity.Hardness` | The PSPACE-hardness reduction from universality of binary automata |
| [Complexity](DeciNSSE/Complexity): Counter, CounterBinary | `Complexity.Counter` | The counter automaton and its binary coding |
| [Complexity](DeciNSSE/Complexity): RejectionSystem, RejectionSolutions, RejectionCountermodel, RejectionCertificates, RejectionExamples, ExpWitness | `Complexity`, `Complexity.Rejection` | Rejection systems and exponentially long holes |

The root module `DeciNSSE.lean` imports the proof library and the solver. Every
module is reachable from `import DeciNSSE` except the executable front ends
`Certificates/Command` and `Solver/Command` and their JSON parser
`Certificates/Json`, which Lake's executable targets `nsse-check` and `nsse`
build. The folder [examples](examples) holds the solver examples and `check.sh`.

## License

Apache License 2.0
