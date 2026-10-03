# deci-nsse

**Non-structural subtype entailment is decidable** — a complete proof, machine-checked in
[Lean 4](https://lean-lang.org/) with [Mathlib](https://github.com/leanprover-community/mathlib4).

```lean
def DeciNSSE.decideEntails    (ϕ : Constraint k) (x y : V k) : Decidable (Entails ϕ x y)     -- finite or infinite trees
def DeciNSSE.decideEntailsReg (ϕ : Constraint k) (x y : V k) : Decidable (EntailsReg ϕ x y)  -- regular trees
def DeciNSSE.decideEntailsFin (ϕ : Constraint k) (x y : V k) : Decidable (EntailsFin ϕ x y)  -- finite trees
```

All three are ordinary, computable Lean definitions without hypotheses, with correctness
theorems `decideEntails_correct`, `decideEntailsReg_correct` and `decideEntailsFin_correct`
(`DeciNSSE/Main.lean`). They depend only on the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

## The problem

**Trees.** Types are finite or infinite binary trees whose nodes are labelled by the constants
`⊥`, `⊤` or by one binary type constructor `f`. They are ordered *non-structurally*: `⊥` is
below every tree, `⊤` is above every tree, and `f(t₁, t₂) ≤ f(u₁, u₂)` holds when
`t₁ ≤ u₁` and `t₂ ≤ u₂` (the constructor is covariant). Trees of different shapes can be
comparable, e.g. `⊥ ≤ f(⊤, ⊥) ≤ ⊤`.

**Constraints.** A flat constraint system `ϕ` over variables `x₁, …, x_k` is a finite
conjunction of literals

```
x = ⊥     x = ⊤     x ≤ f(y, z)     f(y, z) ≤ x
```

A *solution* assigns a tree to every variable so that all literals hold.

**Entailment.** `ϕ` entails `x ≤ y` if every solution of `ϕ` satisfies `x ≤ y`. The
**non-structural subtype entailment problem (NSSE)** asks to decide, given `ϕ`, `x` and `y`,
whether `ϕ ⊨ x ≤ y`.

The problem arises in type inference with subtyping for languages with recursive types. Its
decidability has been open since the 1990s: it is Problem 16 of the TLCA list of open problems.
It is known to be PSPACE-hard (Henglein–Rehof, ICALP 1998). Niehren and Priesnitz
(*Non-structural subtype entailment in automata theory*, Information and Computation 186(2),
2003) reduced it to the universality of a class of automata with cap expressions, and solved
the case of a unary constructor.

In Lean (`DeciNSSE/Constraints/Basic.lean`):

```lean
def Entails (ϕ : Constraint k) (x y : V k) : Prop :=
  ∀ ρ : V k → Tree, Sat ρ ϕ → ρ x ≤ ρ y
```

`EntailsReg` and `EntailsFin` quantify over regular and finite solutions instead.

## The proof

The proof has six steps. The first two make the Niehren–Priesnitz reduction effective; the
remaining four are the new decidability argument.

### 1. From entailment to holes (`Monitor/`, `Automata/`, `Coverage/`)

For each of the two *sides* of a query, a finite deterministic automaton (a *monitor*) over the
binary path alphabet is built from `ϕ`, `x` and `y`. Each monitor comes with a target set `T`
and an *admission* relation `R` on its states. A word `w` is a **hole** if:

* it ends in a target state, and
* no comparison is admitted. A *comparison* is a pair of positions `s < e` such that the
  suffix of `w` after `e` is a prefix of the suffix after `s`, i.e. the suffix from `s` has
  period `e − s`. It is admitted when `(q_s, q_e) ∈ R`.

The bridge theorem `entails_iff_unsat_or_no_holes` (`Monitor/Bridge.lean`) states that

```
ϕ ⊨ x ≤ y   ⟺   ϕ has no solution, or neither of the two monitors has a hole.
```

Satisfiability is decidable (`Satisfiability/`), so NSSE reduces to the **hole problem** for
these two monitors.

### 2. Cap elimination and the admission cone (`RejectedTail/Basic.lean`, `RejectedTail/Image.lean`)

The monitor's holes coincide with the holes of a simpler *image reader*, whose states are the
images of words in a finite transition monoid (`nsse_image_hole_iff`). A word is *ordinarily
rejected* when its image is not accepting.

Write `J` for the length of the shortest rejected prefix of `w`. Rejection persists between
rejected prefixes, and every admitted comparison satisfies `s < J` and `e ≤ J`
(`nsse_rejectedPath`). Consequently the letters after `J`, the **rejected tail**, never carry
an admission. They only matter because they can break comparisons that would otherwise be
admitted.

### 3. Bounded rejected tail (`RejectedTail/BoundedTail.lean`)

> **Theorem (bounded rejected tail).** If the image reader has a hole, it has a hole whose
> rejected tail has length at most `|Q|² + 4|Q|` (`rejectedPath_brt`, instantiated for the
> monitors as `nsse_brt`).

The proof distinguishes two cases.

* **Branching.** Some reachable rejected state `q` lies on a cycle `c` of rejected states and
  has two letters keeping it rejected. Take a shortest word `v` reaching `q`, loop around `c`
  `K` times, and exit with the other letter `b`. A comparison surviving in `v c^K b` would make
  the spelling of `c` invariant under rotation by its period, which contradicts the exit letter
  `b`.
* **Forced cycles.** Every rejected cycle has a single safe letter. A hole with a long tail then
  ends on a forced cycle, and extending it around the cycle yields an infinite periodic word
  with no admitted pair of equal infinite suffixes. Three steps produce a short hole:
  1. locate the earliest periodic onset;
  2. replace the prefix before it by a shortest path to the same state, keeping the one letter
     that marks the onset;
  3. follow the period until the chosen rejected state reappears in phase, then truncate.

### 4. From short tails to bounded depth (`RejectedTail/ReturnGap.lean`, `RejectedTail/Depth*.lean`, `Holes/`)

Every word has a *canonical hierarchy* (`Holes/Hierarchy.lean`). Level `i + 1` records the
occurrences of the suffix that starts at the last core of level `i`. The *support* of a level
is the set of monitor states read at its cores, and the *depth* is the first level at which the
hierarchy becomes unary.

For an ordinarily rejected word with rejected tail `r`:

* **Return gap.** A comparison between equal monitor states has displacement at most `r − 1`
  (`literal_return_gap`, `RejectedTail/ReturnGap.lean`).
* **Support width.** Equal nonempty supports persist for at most `max(1, r)` consecutive levels.
* **Depth.** Supports are nested and there are at most `N` monitor states, so the depth is at
  most `2N · max(1, r) − 1` (`equal_support_width`, `depth_le_of_support_width`,
  `rejected_depth`).

This holds for every rejected word, not only shortest holes.

### 5. Holes of bounded depth are decidable (`Holes/BoundedDepth.lean`)

For a reader with `N` states, holes whose canonical hierarchy has depth at most `d` have length
at most an explicit computable bound `holeBound N d 0`. Their existence is therefore decidable
by finite search (`exists_hole_InL_iff_search`, `decExistsReaderInL`).

### 6. Putting it together (`RejectedTail/Decision.lean`, `Main.lean`)

If a side has a hole, step 3 provides one with tail at most `B = K² + 4K`, where `K` is the
number of image states. By step 4 that hole has depth at most `2N · max(1, B) − 1`, where `N`
is the number of monitor states. Step 5 decides whether such a hole exists. Combined with the
bridge and the satisfiability test, this gives `decideEntails`.

Regular trees give the same entailment relation (`entails_iff_entailsReg`). Finite trees differ
only when `ϕ` has no finite solution (`entailsFin_iff_decider`), which is again decidable. This
yields `decideEntailsReg` and `decideEntailsFin` (`Transfer/`).

The procedure is effective but very far from efficient: the bounds are non-elementary.

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
| `DeciNSSE/Monitor/` | the finite transition image, its axioms, the hole monitors, the bridge theorem |
| `DeciNSSE/Holes/` | abstract holes, the canonical hierarchy, supports, cores, bounded-depth decision |
| `DeciNSSE/RejectedTail/` | admission cone, bounded rejected tail, depth bound, the decision wrapper |
| `DeciNSSE/Main.lean` | the final decision procedures |

## Building

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

Each prints `[propext, Classical.choice, Quot.sound]`.

## Scope

The development covers the signature of the original problem: the constants `⊥`, `⊤` and a
single binary covariant constructor, with flat constraints. It does not treat contravariant
constructors (function types) or several constructors.

## License

Apache License 2.0; see [LICENSE](LICENSE).
