# deci-nsse

**Non-structural subtype entailment is decidable** — a complete proof, machine-checked in
[Lean 4](https://lean-lang.org/) with [Mathlib](https://github.com/leanprover-community/mathlib4).

```lean
def DeciNSSE.decideEntails    (ϕ : Constraint k) (x y : V k) : Decidable (Entails ϕ x y)     -- finite or infinite trees
def DeciNSSE.decideEntailsReg (ϕ : Constraint k) (x y : V k) : Decidable (EntailsReg ϕ x y)  -- regular trees
def DeciNSSE.decideEntailsFin (ϕ : Constraint k) (x y : V k) : Decidable (EntailsFin ϕ x y)  -- finite trees
```

The three deciders are in `DeciNSSE/Main.lean`, together with the theorems
`decideEntails_correct`, `decideEntailsReg_correct` and `decideEntailsFin_correct`.

* **No hypotheses.** They are ordinary Lean definitions.
* **Computable.** None of them is marked `noncomputable`, and Lean compiles them to code.
* **Standard axioms only.** They depend only on `propext`, `Classical.choice` and `Quot.sound`.
* **A genuine algorithm.** Every proposition is classically decidable in Lean, so the content
  of these definitions is not the `Decidable` type itself. It is that the instances are built
  from an actual finite search, with classical reasoning used only in proofs: a terminating
  algorithm that takes the finite description `(ϕ, x, y)` as input.

The algorithm is effective only in principle: its bounds are non-elementary, and even trivial
inputs are far beyond practical execution (see [Complexity](#complexity)).

## The problem

**Trees.** Types are finite or infinite binary trees whose nodes are labelled by the constants
`⊥`, `⊤` or by one binary type constructor `f`. They are ordered *non-structurally*:

* `⊥` is below every tree and `⊤` is above every tree;
* `f(t₁, t₂) ≤ f(u₁, u₂)` holds when `t₁ ≤ u₁` and `t₂ ≤ u₂`, so the constructor is covariant.

Equivalently, two trees are compared label by label on the paths they share. Trees of different
shapes can therefore be comparable, e.g. `⊥ ≤ f(⊤, ⊥) ≤ ⊤`.

**Constraints.** A flat constraint system `ϕ` over variables `x₁, …, x_k` is a finite
conjunction of literals

```
x = ⊥     x = ⊤     x ≤ f(y, z)     f(y, z) ≤ x
```

A *solution* assigns a tree to every variable so that all literals hold.

**Entailment.** `ϕ` entails `x ≤ y` if every solution of `ϕ` satisfies `x ≤ y`. The
**non-structural subtype entailment problem (NSSE)** asks to decide, given `ϕ`, `x` and `y`,
whether `ϕ ⊨ x ≤ y`.

In Lean (`DeciNSSE/Constraints/Basic.lean`):

```lean
def Entails (ϕ : Constraint k) (x y : V k) : Prop :=
  ∀ ρ : V k → Tree, Sat ρ ϕ → ρ x ≤ ρ y
```

`EntailsReg` and `EntailsFin` quantify over regular and finite solutions instead.

This follows the flat formulation of Niehren and Priesnitz. Some details of the representation:

* **Variables** are the elements of `Fin k`, and a constraint is a list of literals.
* **Comparisons between variables.** A premise `u ≤ v` is not a literal, but it is
  expressible: `u ≤ v` holds iff `∃ z b, f(u, b) ≤ z ∧ z ≤ f(v, b)`.
* **Nested terms.** Constraints over nested terms reduce to flat ones by introducing fresh
  variables. This preprocessing step is standard and is not formalised here.
* **Tree classes.** Finite trees are inductive. Regular trees are those given by finite rooted
  graphs, i.e. trees with finitely many distinct subtrees.

### History

* **Origin.** The problem arises in type inference with subtyping for languages with recursive
  types. It was posed as Problem 16 of the TLCA list of open problems (Rehof, 1996).
* **Lower bound.** NSSE is PSPACE-hard (Henglein and Rehof, *Constraint automata and the
  complexity of recursive subtype entailment*, ICALP 1998).
* **Automata reduction.** Niehren and Priesnitz (*Non-structural subtype entailment in automata
  theory*, Information and Computation 186(2), 2003) characterised entailment, for finite,
  regular and infinite trees, by the universality of automata with restricted cap expressions.
  They decided the case of a unary constructor and left the general problem open.
* **A withdrawn claim.** In 2021 a preprint claimed decidability in PSPACE (A. Schubert,
  arXiv:2109.02458). It was withdrawn in December 2021 because of an error in its Lemma 5.5.
* **Recent status.** The problem is still described as open in recent work, e.g. Jiang, Cui and
  Oliveira (POPL 2025).

To our knowledge, no valid proof of decidability of the general problem has been published
before.

## The proof

The proof has six steps. Step 1 is a formalisation of the Niehren–Priesnitz reduction. Steps 2–6
are the decidability argument (see [Relation to previous work](#relation-to-previous-work)).

### 1. From entailment to holes (`Monitor/`, `Automata/`, `Coverage/`)

For each of the two *sides* of a query, a finite deterministic automaton (a *monitor*) over the
binary path alphabet is built from `ϕ`, `x` and `y`. Each monitor comes with a target set `T`
and an *admission* relation `R` on its states.

A *comparison* in a word `w` is a pair of positions `s < e` such that the suffix of `w` after
`e` is a prefix of the suffix after `s`, i.e. the suffix from `s` has period `e − s`. It is
*admitted* when `(q_s, q_e) ∈ R`, where `q_i` is the monitor state after the first `i` letters.

A word `w` is a **hole** if it ends in a target state and has no admitted comparison.

The bridge theorem `entails_iff_unsat_or_no_holes` (`Monitor/Bridge.lean`) states:

```
ϕ ⊨ x ≤ y   ⟺   ϕ has no solution, or neither of the two monitors has a hole.
```

Satisfiability is decidable (`Satisfiability/`), so NSSE reduces to the **hole problem** for
these two monitors.

### 2. Cap elimination and the admission cone (`RejectedTail/Basic.lean`, `RejectedTail/Image.lean`)

The monitor's holes coincide with the holes of a simpler *image reader*, whose states are the
images of words in a finite transition monoid (`nsse_image_hole_iff`). A word is *ordinarily
rejected* when its image is not accepting.

Write `J` for the length of the shortest rejected prefix of `w`. Two facts hold
(`nsse_rejectedPath`):

* **Rejection between rejected prefixes.** If two prefixes are rejected, so is every prefix
  between them. Rejection need not persist under arbitrary extensions.
* **Admission cone.** Every admitted comparison satisfies `s < J` and `e ≤ J`.

Consequently the letters after `J`, the **rejected tail**, never carry an admission. They only
matter because they can break comparisons that would otherwise be admitted.

### 3. Bounded rejected tail (`RejectedTail/BoundedTail.lean`)

> **Theorem (bounded rejected tail).** If the image reader has a hole, it has a hole whose
> rejected tail has length at most `|Q|² + 4|Q|` (`rejectedPath_brt`, instantiated for the
> monitors as `nsse_brt`).

The proof distinguishes two cases.

* **Branching (tail at most `4|Q|`).** Some reachable rejected state `q` lies on a cycle `c` of
  rejected states and has two letters keeping it rejected.
  * Take a shortest word `v` reaching `q`, loop around `c` `K` times, and exit with the other
    letter `b`.
  * By the admission cone, any admitted comparison in `v c^K b` has period at most `|v|`.
  * If such a comparison survived, the spelling of `c` would be invariant under rotation by
    that period. This contradicts the exit letter `b`.
* **Forced cycles (tail at most `|Q|² + 2|Q|`).** Every rejected cycle has a single safe letter.
  A hole with a long tail then ends on a forced cycle. Extending it around the cycle yields an
  infinite periodic word with no admitted pair of equal infinite suffixes. A short hole is then
  obtained in three steps:
  1. **Earliest periodic onset.** Locate it.
  2. **Compress the prefix.** Replace the prefix before the onset by a shortest path to the same
     state, keeping the letter that marks the onset. That mismatch prevents new equal-suffix
     pairs from starting before the onset.
  3. **Truncate.** Follow the period until the chosen rejected state reappears in phase. This
     takes at most `|Q| · d` steps for period `d`.

### 4. From short tails to bounded depth (`RejectedTail/ReturnGap.lean`, `RejectedTail/Depth*.lean`, `Holes/`)

Every word has a *canonical hierarchy* (`Holes/Hierarchy.lean`):

* **Levels.** Level `i + 1` records the occurrences of the suffix that starts at the last core
  of level `i`.
* **Support.** The *support* of a level is the set of monitor states read at its cores.
* **Depth.** The *depth* is the first level at which the hierarchy becomes unary.

For an ordinarily rejected word with rejected tail `r`:

* **Return gap.** A comparison between equal monitor states has displacement at most `r − 1`
  (`literal_return_gap`, `RejectedTail/ReturnGap.lean`).
* **Support width.** Equal nonempty supports persist for at most `max(1, r)` consecutive levels.
* **Depth.** Supports are nested and there are at most `N` monitor states, so the depth is at
  most `2N · max(1, r) − 1` (`equal_support_width`, `depth_le_of_support_width`,
  `rejected_depth`).

These bounds hold for every ordinarily rejected word, not only for holes or shortest holes.

### 5. Holes of bounded depth are decidable (`Holes/BoundedDepth.lean`)

Fix a reader with `N` states and a depth `d`. **If a hole of hierarchy depth at most `d` exists,
then such a hole exists whose length is at most an explicit computable bound
`holeBound N d 0`** (`exists_hole_InL_iff_search`). The bound applies to a suitably chosen hole,
not to every hole. For example, a one-state reader whose state is a target and whose admission
relation is empty has holes of every length, all of depth `0`.

The proof compresses tuples of blocks using finite summaries of block transitions, equalities
and admission behaviour. Compression keeps the summaries, and therefore holehood, unchanged. The
existence of a bounded-depth hole is therefore decided by finite enumeration up to the bound
(`decExistsReaderInL`).

### 6. Putting it together (`RejectedTail/Decision.lean`, `Main.lean`)

Fix a side, and let `K` be the number of image states and `N` the number of monitor states.

* If the side has a hole, step 3 provides one with tail at most `B = K² + 4K`.
* By step 4, that hole has depth at most `2N · max(1, B) − 1`.
* Step 5 decides whether a hole of that depth exists.

The empty word is checked separately. Combined with the bridge and the satisfiability test,
this gives `decideEntails`.

The other tree classes follow by transfer (`Transfer/`):

* **Regular trees** give the same entailment relation (`entails_iff_entailsReg`), which yields
  `decideEntailsReg`.
* **Finite trees** differ only when `ϕ` has no finite solution (`entailsFin_iff_decider`), and
  finite satisfiability is decidable. This yields `decideEntailsFin`.

## Relation to previous work

The development has two parts: a formalisation of the known reduction of NSSE to an automata
problem, and a new argument that decides that automata problem.

**Formalised from the literature** — about 7,000 lines (57%) of the Lean code, in `Semantics/`,
`Constraints/`, `Satisfiability/`, `Transfer/`, `Automata/`, `Coverage/` and `Monitor/`:

* **The problem.** Trees, the non-structural order, flat constraints and entailment follow
  Niehren and Priesnitz (2003, §2).
* **The reduction.** Cap automata, the construction of the automata from a constraint system,
  and the soundness and completeness arguments characterising entailment by universality follow
  Niehren and Priesnitz (2003). These are re-proved here in Lean.
* **Transfer between tree classes.** The passage between finite, regular and infinite trees
  follows the same line of work.
* **Satisfiability.** The decision of satisfiability and finite satisfiability uses standard
  closure, least-solution and cycle-clash arguments.
* **Reformulation.** `Monitor/` restates the universality condition of Niehren and Priesnitz as
  the absence of *holes* in two finite monitors. It also isolates the structural properties of
  their construction that the rest of the proof uses, as a list of properties proved for the
  construction (`DerivedAxioms`, `constructed_derivedAxioms`). The mathematical content is
  theirs; the form is adapted to the argument that follows.

**New** — about 5,200 lines (43%), in `Holes/`, `RejectedTail/` and `Main.lean`:

* **The admission cone** (step 2). Every admitted comparison ends by the first rejection, so the
  rejected tail only breaks periodicities. This is a property of the specific monitors arising
  from the construction; it is not used in the earlier work.
* **The bounded rejected-tail theorem** (step 3). It uses classical tools from combinatorics on
  words (periodicity, rotation invariance, periodic onsets), but the statement and argument are
  new.
* **The canonical hierarchy of a word, its supports, and the decidability of holes of bounded
  hierarchy depth** (steps 4–5).
* **The return-gap and support-width bounds**, and the resulting depth bound from a short
  rejected tail (step 4).
* **The decision procedure** that combines these with the reduction (step 6).

The argument never manipulates solutions of the constraints. After the reduction it works
entirely with the monitors. This differs from the approach of the withdrawn 2021 preprint
mentioned above, which worked directly with solutions.

The general problem behind step 1 — deciding holes for *arbitrary* finite readers and admission
relations — is not addressed here. The decision procedure relies on the admission cone, which the
NSSE monitors satisfy but general readers do not.

## Complexity

* **Upper bound.** The proof gives an explicit, computable, non-elementary bound: the
  bounded-depth step iterates exponential compressions to a depth that itself grows with the
  input.
* **Not a lower bound.** The non-elementary bound is a property of this proof, not a lower bound
  for NSSE.
* **Open gap.** The best known lower bound is PSPACE-hardness. The exact complexity remains
  open, and this development does not establish membership in PSPACE.

## Repository layout

| Directory | Contents |
|---|---|
| `DeciNSSE/Words.lean` | words over the binary path alphabet, prefixes, periods |
| `DeciNSSE/Semantics/` | symbols, possibly infinite trees and their order, finite and regular trees |
| `DeciNSSE/Constraints/` | constraint syntax and semantics, `Entails`, constraint closure |
| `DeciNSSE/Satisfiability/` | least solutions, cycle clashes, decidability of (finite) satisfiability |
| `DeciNSSE/Transfer/` | safety arguments; regular- and finite-tree entailment |
| `DeciNSSE/Automata/` | cap automata, the automaton construction, soundness and completeness |
| `DeciNSSE/Coverage/` | coverage of words by caps, periods, the end-to-end language characterisation |
| `DeciNSSE/Monitor/` | the finite transition image, its properties, the hole monitors, the bridge theorem |
| `DeciNSSE/Holes/` | abstract holes, the canonical hierarchy, supports, cores, bounded-depth decision |
| `DeciNSSE/RejectedTail/` | admission cone, bounded rejected tail, depth bound, the decision wrapper |
| `DeciNSSE/Main.lean` | the final decision procedures |

## Building and checking

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

To check the axioms of the main results:

```lean
import DeciNSSE
#print axioms DeciNSSE.decideEntails
#print axioms DeciNSSE.decideEntailsReg
#print axioms DeciNSSE.decideEntailsFin
```

Each prints `[propext, Classical.choice, Quot.sound]`. The checked statements rely on the Lean
kernel and on Mathlib. Running the compiled deciders additionally relies on the Lean compiler.

The proof is machine-checked but has not yet been peer reviewed. Independent reproduction of
the build and review of the mathematical argument are welcome.

## Scope

The development covers the signature of the original problem: the constants `⊥`, `⊤` and a
single binary covariant constructor, with flat constraints. It does not treat:

* contravariant constructors, such as function types;
* several constructors.

## License

Apache License 2.0; see [LICENSE](LICENSE).
