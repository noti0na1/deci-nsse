import DeciNSSE.Satisfiability.Decide

/-! # Sets of path bounds

The lower and the upper bounds of a variable along a path form two finite sets
of variables. Each is updated by a one-letter step, so the pair is the state of
a deterministic automaton reading the path. The label reader and the graph of
the least shape both run this automaton.

## Main declarations

- `lowerSet`, `upperSet`, `mem_lowerSet`, `mem_upperSet`: the sets of lower and upper
  bounds of a variable along a path.
- `lowerStep`, `upperStep`, `mem_lowerStep`, `mem_upperStep`: the one-letter steps, over
  a precomputed closure.
- `lowerSet_append`, `upperSet_append`: the steps extend the path by one letter.
-/

namespace DeciNSSE

variable {n k : ℕ}

/-- The lower bounds of `z` along the path `π`. -/
def lowerSet (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) : Finset (V k) :=
  Finset.univ.filter fun v => lowerAtB ϕ π v z = true

/-- The upper bounds of `z` along the path `π`. -/
def upperSet (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) : Finset (V k) :=
  Finset.univ.filter fun v => upperAtB ϕ π z v = true

/-- The one-letter lower extension of a set, over a precomputed closure. -/
def lowerStep (ϕ : Constraint n k) (pairs : Finset (V k × V k)) (i : Fin n)
    (S : Finset (V k)) : Finset (V k) :=
  Finset.univ.filter fun v => ∃ u ∈ S, PathDecision.lower ϕ pairs [i] v u = true

/-- The one-letter upper extension of a set, over a precomputed closure. -/
def upperStep (ϕ : Constraint n k) (pairs : Finset (V k × V k)) (i : Fin n)
    (S : Finset (V k)) : Finset (V k) :=
  Finset.univ.filter fun v => ∃ u ∈ S, PathDecision.upper ϕ pairs [i] u v = true

variable {ϕ : Constraint n k}

@[simp] theorem mem_lowerSet {z v : V k} {π : List (Fin n)} :
    v ∈ lowerSet ϕ z π ↔ LowerAt ϕ π v z := by
  simp [lowerSet, lowerAtB_iff]

@[simp] theorem mem_upperSet {z v : V k} {π : List (Fin n)} :
    v ∈ upperSet ϕ z π ↔ UpperAt ϕ π z v := by
  simp [upperSet, upperAtB_iff]

/-- The lower step collects the one-letter lower path bounds of the set. -/
theorem mem_lowerStep {i : Fin n} {S : Finset (V k)} {v : V k} :
    v ∈ lowerStep ϕ (derivedPairs ϕ) i S ↔ ∃ u ∈ S, LowerAt ϕ [i] v u := by
  simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun u => and_congr_right fun _ => lowerAtB_iff ϕ [i] v u

/-- The upper step collects the one-letter upper path bounds of the set. -/
theorem mem_upperStep {i : Fin n} {S : Finset (V k)} {v : V k} :
    v ∈ upperStep ϕ (derivedPairs ϕ) i S ↔ ∃ u ∈ S, UpperAt ϕ [i] u v := by
  simp only [upperStep, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun u => and_congr_right fun _ => upperAtB_iff ϕ [i] u v

/-- Reading one more letter applies the lower step. -/
theorem lowerSet_append (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) (i : Fin n) :
    lowerSet ϕ z (π ++ [i]) = lowerStep ϕ (derivedPairs ϕ) i (lowerSet ϕ z π) := by
  ext v
  simp only [mem_lowerSet, mem_lowerStep]
  exact ⟨fun h => (LowerAt.factor h).imp fun _ h => h, fun ⟨_, hu, hi⟩ => hi.comp hu⟩

/-- Reading one more letter applies the upper step. -/
theorem upperSet_append (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) (i : Fin n) :
    upperSet ϕ z (π ++ [i]) = upperStep ϕ (derivedPairs ϕ) i (upperSet ϕ z π) := by
  ext v
  simp only [mem_upperSet, mem_upperStep]
  exact ⟨fun h => (UpperAt.factor h).imp fun _ h => h, fun ⟨_, hu, hi⟩ => hu.comp hi⟩

end DeciNSSE
