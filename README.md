# Decidability of non-structural subtype entailment

**Non-structural subtype entailment is decidable.** This repository gives a
machine-checked proof in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), together with
computable decision procedures for finite, regular, and possibly infinite trees.

The question is whether a finite set of subtype constraints forces another
subtype relation to hold in **every** solution. It appears in the simplification
of inferred types and was listed as
[Problem 16 of the TLCA open problem list](https://tlca.di.unito.it/opltlca/opltlcasu23.html).
The proof combines the automata characterization of Niehren and Priesnitz with
an argument that bounds the search for a counterexample. Its search bounds are
non-elementary, so the result establishes decidability rather than a practical
algorithm for type inference.

## The problem

### Why entailment matters

Constraint-based type inference records requirements on unknown types as subtype
constraints. Simplifying an inferred type requires removing redundant constraints
without changing its meaning. In particular, `x ≤ y` can be removed when it
follows from the remaining constraints. This application motivated the study of
subtype entailment. See
[Niehren and Priesnitz (1999)](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf).

There are two distinct questions. **Satisfiability** asks whether the constraints
have at least one solution. **Entailment** asks whether a proposed relation holds
in all solutions. A procedure for finding a solution does not, by itself,
answer the second question.

### Trees and non-structural subtyping

The types considered here are binary trees over the signature `{⊥, f, ⊤}`.
A leaf is labelled `⊥` or `⊤`; a node labelled `f` has two ordered children.
Trees may be finite or infinite. The subtype order has the following properties:

```text
⊥ ≤ t ≤ ⊤                         for every tree t
f(t₁, t₂) ≤ f(u₁, u₂)             iff t₁ ≤ u₁ and t₂ ≤ u₂.
```

Thus `f` is covariant in both arguments. More precisely, label the root by the
empty path and the two children of each constructor node by `0` and `1`.
Order the labels by `⊥ < f < ⊤`. Then `t ≤ u` means that, at every finite path
present in both trees, the label in `t` is at most the label in `u`. This defines
the order for infinite trees as well as finite ones.

The order is **non-structural** because comparable trees need not have the same
shape. For example,

```text
⊥ ≤ f(⊤, ⊥) ≤ ⊤.
```

The first and last trees have only a root; the middle tree has two children.
In the structural subtype order studied in the earlier literature, comparisons
are restricted to trees of the same shape.

### Constraints, solutions, and the decision question

A flat constraint system `ϕ` is a finite conjunction of literals of these forms:

```text
x = ⊥     x = ⊤     x ≤ f(y, z)     f(y, z) ≤ x
```

A **solution** is an assignment `ρ` of a tree to every variable that makes all
the literals true. Write `ρ ⊨ ϕ` when `ρ` is a solution. The entailment judgment

```text
ϕ ⊨ x ≤ y
```

means

```text
for every assignment ρ, if ρ ⊨ ϕ then ρ(x) ≤ ρ(y).
```

**The non-structural subtype entailment problem (NSSE)** takes a finite
constraint system `ϕ` and two variables `x` and `y` as input and asks whether
`ϕ ⊨ x ≤ y`. Decidability requires an algorithm that terminates with the correct
yes or no answer for every such input. The input is finite even when solutions
may contain infinite trees.

For a simple example, let

```text
ϕ = (x ≤ f(u, v)) ∧ (f(u, v) ≤ y).
```

Then `ϕ ⊨ x ≤ y` by transitivity. The reverse judgment `ϕ ⊨ y ≤ x` is false:
assigning `x = ⊥`, `y = ⊤`, and `u = v = ⊥` satisfies both constraints but
violates `y ≤ x`. Such an assignment is a **counterexample to entailment**.
If `ϕ` has no solution, every entailment from `ϕ` holds vacuously.

### Which trees are allowed as solutions?

The development treats three domains of assignments:

| Domain | Meaning |
| --- | --- |
| Finite trees | Trees with finitely many nodes, representing finite type expressions |
| Regular trees | Trees with finitely many distinct subtrees, representable by finite rooted graphs |
| Arbitrary trees | All finite and infinite trees over the signature |

A regular tree can be infinite. For example, the equation `t = f(t, ⊥)` describes
an infinite tree with a finite graph representation. The choice of domain can
change satisfiability: the constraints `f(x, x) ≤ x` and `x ≤ f(x, x)` have an
infinite regular solution, but no finite solution.

The three entailment problems are related, but their definitions quantify over
different assignments. This development proves that unrestricted and
regular-tree entailment coincide. Finite-tree entailment holds exactly when
there is no finite solution or unrestricted entailment holds.

The formalized signature has one binary covariant constructor. The flat syntax
follows Niehren and Priesnitz. Nested terms can be flattened using fresh
variables, and a variable inequality `u ≤ v` can be expressed as
`∃ z b, f(u, b) ≤ z ∧ z ≤ f(v, b)`. This preprocessing is not formalized here.
The development does not treat contravariant constructors or signatures with
several constructors.

## How the problem developed

* **1996: constraint simplification and the open problem.** The TLCA entry traces
  the question to work by Pottier and by Trifonov and Smith on simplifying
  subtype constraints. Jakob Rehof submitted it to the open problem list in
  1996. The entry asks whether the corresponding universally quantified Horn
  implications are decidable.
  [TLCA Problem 16](https://tlca.di.unito.it/opltlca/opltlcasu23.html).

* **1997 and 1998: complexity of structural and non-structural entailment.**
  Henglein and Rehof established coNP-completeness for structural entailment
  over finite trees and PSPACE-completeness for structural entailment over
  possibly infinite trees. For non-structural entailment they proved
  PSPACE-hardness, including the signature with bottom, top, and a binary
  constructor. A decision procedure for that case remained unknown.
  [Summary in Niehren and Priesnitz (1999)](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf),
  [Henglein and Rehof, ICALP 1998](https://hjemmesider.diku.dk/~henglein/publications.html).

* **1999: a decidable fragment.** Niehren and Priesnitz proved PSPACE-completeness
  when the constraints omit explicit occurrences of top and bottom, although
  solutions may still contain them. Their automata approach left the general
  problem open.
  [Entailment of Non-Structural Subtype Constraints](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf).

* **2001 and 2003: the cap-automata characterization.** Niehren and Priesnitz
  reduced NSSE to universality for restricted cap expressions, with a conference
  version at TACS 2001 and a full account in *Information and Computation* in
  2003. The characterization applies to finite, regular, and infinite trees.
  It yields decidability for a unary constructor, but leaves the branching case
  open. The additional difficulty is expressed by word equations and periodic
  conditions beyond ordinary finite-automaton acceptance.
  [Non-structural subtype entailment in automata theory](https://doi.org/10.1016/S0890-5401(03)00140-8),
  [author manuscript](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_02.pdf).

* **2021: a withdrawn decidability claim.** Schubert claimed membership in
  PSPACE for finite and regular types. The preprint was withdrawn in December
  2021 because an error in Lemma 5.5 invalidated the subsequent construction.
  This development does not use that argument.
  [Withdrawal notice](https://arxiv.org/abs/2109.02458).

* **2025: the question remained relevant to type inference.** Jiang, Cui, and
  Oliveira still identified entailment with top and bottom types as an open
  problem when discussing the obstacles posed by non-structural subtyping to
  type inference.
  [Bidirectional Higher-Rank Polymorphism with Intersection and Union Types, §3.1](https://cuichen.cc/assets/popl25/popl25-extended.pdf).

The undecidability of the full first-order theory of non-structural subtyping
was already known. It does not settle entailment, which uses a restricted form
of implication. This distinction is recorded in the
[TLCA problem statement](https://tlca.di.unito.it/opltlca/opltlcasu23.html).

## What this development contributes

The development has two mathematical parts. The first formalizes the known
reduction from subtype entailment to an automata problem, including its
soundness, completeness, satisfiability tests, and transfer between classes of
trees. The second supplies the decision argument for the automata arising from
that construction.

The new argument proceeds through three bounds. A counterexample word can be
chosen with a bounded rejected tail. That bounds the depth of a canonical
hierarchy of word decompositions. At bounded depth, finite summaries allow the
word to be compressed to a computably bounded length. Exhaustive search up to
that bound decides whether a counterexample exists.

The formalization of the reduction is in `Semantics/`, `Constraints/`,
`Satisfiability/`, `Transfer/`, `Automata/`, `Coverage/`, and `Monitor/`.
The decision argument is in `Holes/` and `RejectedTail/`; `Main.lean` combines
them into the three public procedures. The admission properties used in the
argument are proved for the constructed monitors. They are not additional
axioms of the development.

The result provides a terminating algorithm for the binary signature specified
above. Its bounds are non-elementary, and it does not establish membership in
PSPACE or an optimal complexity bound.

## Proof overview

The proof reduces entailment to the absence of particular words in two finite
monitors. Such words are called *holes*. It then proves that the existence of a
hole implies the existence of one within a computable length bound. The main
intermediate bounds concern the length of a rejected suffix and the depth of a
canonical decomposition of a word.

The need for these bounds comes from the periodic acceptance conditions.
Deleting a loop preserves a finite automaton state, but can change which
suffixes have a common period and hence which comparisons are admitted.
The compression argument must preserve both kinds of information.

### 1. Satisfiability and the automata reduction

Constraint closure records the variable inequalities implied by the literals.
Bounds along binary paths determine a least assignment of trees. A label clash
is the obstruction to satisfiability. For finite solutions there is a further
obstruction, a cycle clash, which forces unbounded tree height. The predicates
`LabelClash` and `CycleClash` are decided by finite searches; `satInfB` and
`satFinB` decide the corresponding satisfiability problems.

For a satisfiable system, failure of `x ≤ y` has a finite path witnessing an
incompatible pair of labels. The two possible kinds of mismatch give the two
sides of the automata construction. Each side is represented by a cap automaton,
which accepts ordinary finite runs and words with a suffix that is a prefix of
a power of an admitted root word. Soundness and completeness relate these
languages to the path comparisons required by entailment.

The automata are then represented by finite deterministic monitors over the
binary path alphabet. A monitor consists of a reader `M`, a target set `T`, and
an admission relation `R` on states. Write `qᵢ = M.eval (w.take i)`. A comparison
in a word `w` consists of positions

```text
s < e ≤ |w|, with w.drop e a prefix of w.drop s.
```

Equivalently, the suffix starting at `s` has period `e − s`. The comparison is
admitted when `R qₛ qₑ` holds. A hole is a word whose final state belongs to `T`
and which has no admitted comparison. This definition is `Holes.IsReaderHole`.

The theorem `Bridge.entails_iff_unsat_or_no_holes` states that entailment holds
exactly when the constraints are unsatisfiable or neither side monitor has a
hole. Thus, after deciding satisfiability, it suffices to decide hole existence
for each side. See [Automata](DeciNSSE/Automata),
[Coverage](DeciNSSE/Coverage), and [Monitor/Bridge.lean](DeciNSSE/Monitor/Bridge.lean).

### 2. Transition images and the admission cone

For each side, the transition relations induced by words form a finite monoid.
The associated image reader records the product of the images of successive
letters. A word is *ordinarily rejected* if its image is outside the ordinary
acceptance set. Cap elimination proves that holes of this reader coincide with
holes of the finite monitor (`nsse_image_hole_iff`).

Let `J` be the length of the first rejected prefix of a rejected word `w`.
The rejected tail is the suffix after that prefix, with length `r = |w| − J`.
The construction has two properties:

1. Every prefix between two rejected prefixes is rejected.
2. Every admitted comparison satisfies `s < J` and `e ≤ J`.

The second property is the *admission cone*. It implies that extending the
rejected tail can destroy comparisons by breaking their periods, while all
potentially admitted endpoints remain in the initial segment. The first
property concerns intervals between rejected prefixes; it does not assert
closure of rejection under arbitrary extensions.

`RejectedPath` packages these properties. They are proved for the constructed
image reader in [RejectedTail/Image.lean](DeciNSSE/RejectedTail/Image.lean).

### 3. A quadratic bound on the rejected tail

For a binary reader with `K` states satisfying `RejectedPath`, the theorem
`boundedRejectedTail_of_rejectedPath` proves

```text
If a hole exists, a hole exists with rejected-tail length at most K² + 4K.
```

The proof separates two cases according to the transitions within rejected
states.

**A cycle with a choice of letters.** Suppose a reachable rejected state lies
on a cycle and both letters lead to rejected states. Choose a short path `v`
to that state and a short nonempty cycle word `c`. Traverse the cycle sufficiently
many times, then read a letter `b` different from the first letter of `c`.
The resulting word is `v cᴺ b`. The admission cone bounds every potentially
admitted period by the length of `v`. The Fine–Wilf periodicity theorem
shows that such a period, if it survived through the repeated cycle, would
force the final letter to equal the first letter of `c`. This contradicts the
choice of `b`. The resulting hole has rejected-tail length at most `4K`.

**Cycles with a unique possible letter.** Otherwise, each rejected state on a
cycle has at most one letter leading to another rejected state. A sufficiently
long rejected path therefore has an infinite periodic continuation. Extending
a hole in this way preserves the absence of admitted comparisons between equal
infinite suffixes. Choose the earliest onset of the period and replace the
preceding path by a shortest path reaching the same state, retaining the
letter mismatch immediately before the onset. That mismatch excludes new equal
suffixes beginning before the periodic part. Finally, track both the reader
state and the phase of the period. For a period of length `d ≤ K`, the product
has at most `K d` states. A visit in the required phase and a sufficiently long
finite prefix yield a hole with rejected-tail length at most `K² + 2K`.

The larger bound covers both cases. The proof and its specialization
`nsse_boundedRejectedTail` are in
[RejectedTail/BoundedTail.lean](DeciNSSE/RejectedTail/BoundedTail.lean).

### 4. From tail length to hierarchy depth

The canonical hierarchy repeatedly decomposes a nonempty word at occurrences
of its last letter. The blocks preceding those occurrences become letters of
the next level. Repeating this construction is called *desubstitution*.
Expansion recovers the original word at every level, and the corresponding
derived monitors preserve holes.

A level is unary when all its letters are equal. Each non-unary level strictly
shortens the word, so some level is unary. The first such level is the canonical
hierarchy depth (`HierarchyDepth.depth`).

A core records the reader state before a letter. Derived levels introduce
initial cores and retain some cores from the original word. The support of a
level is the set of original reader states represented by its retained cores.
These supports decrease with the level.

For a rejected word with tail length `r`, a comparison between equal monitor
states has displacement at most `r − 1` (`literal_return_gap`). Equal nonempty
supports at two levels give such a comparison. Consequently, a fixed nonempty
support can persist for at most `max(1, r)` consecutive levels. There can be at
most `N` strict decreases in a nonempty support, where `N` is the number of
monitor states. Once the support is empty, the number of introduced initial
cores bounds the remaining word length. Combining these counts gives

```text
canonical depth ≤ 2N · max(1, r) − 1.
```

This bound holds for every nonempty ordinarily rejected word, including holes.
The argument appears in [RejectedTail/ReturnGap.lean](DeciNSSE/RejectedTail/ReturnGap.lean),
[RejectedTail/DepthCount.lean](DeciNSSE/RejectedTail/DepthCount.lean), and
[RejectedTail/Depth.lean](DeciNSSE/RejectedTail/Depth.lean).

### 5. Finite search at bounded depth

The remaining result is a compression theorem: if a hole exists at bounded
hierarchy depth, then a hole exists below an explicit computable length bound.
Bounding depth alone does not bound the length of every hole. For example, a
reader with one target state and no admissions has unary holes of every length.

The proof uses lettered monitors, whose labels record a core and a letter.
For each finite tuple of blocks, a finite summary records the induced state
transitions, final admissions, equalities between blocks, and admissions
between pairs of blocks. Reading the tuple as columns of optional letters
produces a finite summary automaton. A shortest path to the same summary gives
shorter blocks while preserving the derived monitor on the letters in use.
This preservation property is expressed by `BoundedDepth.Agree`.

At the final level, unary holes can be shortened using the finite core set.
The more general compression theorem also permits a bounded *comparison
horizon*: every comparison ending before the final position leaves at most
`h` letters. In this case, a finite record of the core and comparison data near
the final positions identifies intervals that can be deleted. Compression
then proceeds through the preceding levels while preserving the summaries.

The predicate `InL d h w` means that some level at most `d` is unary or has
comparison horizon at most `h`. For a reader with `N` states, the resulting
length bound is `BoundedDepth.holeBound N d h`. The theorem
`exists_hole_InL_iff_search` reduces hole existence in this class to enumeration
of words up to that bound. The instance `decExistsReaderInL` implements this
finite decision. See [Holes/BoundedDepth.lean](DeciNSSE/Holes/BoundedDepth.lean).

### 6. Entailment and the three classes of trees

For each side, let `K` be the number of image states and `N` the number of
monitor states. Set

```text
B = K² + 4K
d = 2N · max(1, B) − 1.
```

If a hole exists, the bound on rejected tails provides one with tail length at
most `B`. If that hole is nonempty, its hierarchy depth is at most `d`, so it
belongs to `InL d 0`. Finite enumeration using `holeBound N d 0` therefore
decides whether a nonempty hole exists. The empty word is checked separately.
The bridge theorem combines the decisions for both sides with the
satisfiability test to give `decideEntails`.

The transfer theorems then give the other procedures. Entailment over arbitrary
trees agrees with entailment over regular trees (`entails_iff_entailsReg`).
Entailment over finite trees holds exactly when the system has no finite
solution or unrestricted entailment holds (`entailsFin_iff_decider`). These
equivalences yield `decideEntailsReg` and `decideEntailsFin`.

## Formal statements and decision procedures

In Lean, variables are elements of `Fin k`, a constraint is a list of literals,
and unrestricted entailment is defined in
[Constraints/Basic.lean](DeciNSSE/Constraints/Basic.lean) by

```lean
def Entails {k : ℕ} (ϕ : Constraint k) (x y : V k) : Prop :=
  ∀ ρ, Sat ρ ϕ → ρ x ≤ ρ y
```

The public procedures in [Main.lean](DeciNSSE/Main.lean) take `ϕ`, `x`, and `y`:

| Procedure | Result | Domain of solutions |
| --- | --- | --- |
| `DeciNSSE.decideEntails` | `Decidable (Entails ϕ x y)` | Arbitrary trees |
| `DeciNSSE.decideEntailsReg` | `Decidable (EntailsReg ϕ x y)` | Regular trees |
| `DeciNSSE.decideEntailsFin` | `Decidable (EntailsFin ϕ x y)` | Finite trees |

Each has a correctness theorem with the suffix `_correct`. Import `DeciNSSE`
to use this interface.

These definitions implement finite searches with explicit bounds and are not
marked `noncomputable`. The significance is their computability: classical
logic alone would also give a `Decidable` instance for any proposition, but
would not supply an executable algorithm. Classical reasoning is used in the
proofs that justify the search bounds and the procedures.

## Complexity and scope of the algorithm

The finite search gives a non-elementary upper bound. Compression bounds are
iterated through a hierarchy whose depth grows with the input. This construction
does not determine the optimal complexity of NSSE; the gap with the known
PSPACE lower bound remains.

The procedure relies on the admission properties of monitors constructed from
subtype constraints. It does not decide hole existence for arbitrary finite
readers and admission relations. The implementation is intended to establish
decidability, and its bounds are too large for practical type inference.

## Building and checking

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The first command downloads compiled Mathlib dependencies. The second checks
the development with the pinned toolchain. When updating dependencies, change
Lean and Mathlib together, run `lake update`, and rebuild before committing the
updated manifest.

To inspect the logical dependencies, save the following as `Check.lean` and run
`lake env lean Check.lean`:

```lean
import DeciNSSE

#print axioms DeciNSSE.decideEntails
#print axioms DeciNSSE.decideEntailsReg
#print axioms DeciNSSE.decideEntailsFin
```

Each procedure depends only on usual `propext`, `Classical.choice`, and `Quot.sound`.
No additional axioms or unfinished proofs are used. Lean's kernel checks the
proof terms; execution of the compiled procedures also relies on the compiler.

## Repository layout

| Module | Purpose |
| --- | --- |
| [Words](DeciNSSE/Words.lean) | Binary words, prefixes, powers, and periods |
| [Semantics](DeciNSSE/Semantics) | Tree representations and the subtype order |
| [Constraints](DeciNSSE/Constraints) | Flat syntax, satisfaction, entailment, and closure |
| [Satisfiability](DeciNSSE/Satisfiability) | Least solutions, label clashes, and cycle clashes |
| [Transfer](DeciNSSE/Transfer) | Path witnesses and transfer between classes of trees |
| [Automata](DeciNSSE/Automata) | Cap automata, construction, soundness, and completeness |
| [Coverage](DeciNSSE/Coverage) | Ordinary acceptance and periodic coverage |
| [Monitor](DeciNSSE/Monitor) | Transition images, admission properties, and finite monitors |
| [Holes](DeciNSSE/Holes) | Desubstitution, supports, and finite compression |
| [RejectedTail](DeciNSSE/RejectedTail) | Bounds on rejected tails and hierarchy depth |
| [Main](DeciNSSE/Main.lean) | The three public decision procedures |

## License

Apache License 2.0
