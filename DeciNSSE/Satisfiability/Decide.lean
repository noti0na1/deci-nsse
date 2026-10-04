import DeciNSSE.Satisfiability.Finite

/-! # Deciding satisfiability

Finite closure and bounded path enumeration decide label and cycle clashes.
The resulting Boolean procedures decide unrestricted and finite satisfiability.
-/

namespace DeciNSSE

variable {k : ℕ}

namespace PathDecision

def lower (ϕ : Constraint k) (pairs : Finset (V k × V k)) :
    List (Fin 2) → V k → V k → Bool
  | [], x, y => decide ((x, y) ∈ pairs)
  | i :: π, x, y => ϕ.any fun
      | .fLe z₁ z₂ z => decide ((z, y) ∈ pairs) && lower ϕ pairs π x (if i = 0 then z₁ else z₂)
      | _ => false

def upper (ϕ : Constraint k) (pairs : Finset (V k × V k)) :
    List (Fin 2) → V k → V k → Bool
  | [], x, y => decide ((x, y) ∈ pairs)
  | i :: π, x, y => ϕ.any fun
      | .leF z z₁ z₂ => decide ((x, z) ∈ pairs) && upper ϕ pairs π (if i = 0 then z₁ else z₂) y
      | _ => false

end PathDecision

def lowerAtB (ϕ : Constraint k) (π : List (Fin 2)) (x y : V k) : Bool :=
  PathDecision.lower ϕ (derivedPairs ϕ) π x y

def upperAtB (ϕ : Constraint k) (π : List (Fin 2)) (x y : V k) : Bool :=
  PathDecision.upper ϕ (derivedPairs ϕ) π x y

theorem lowerAtB_iff (ϕ : Constraint k) (π : List (Fin 2)) (x y : V k) :
    lowerAtB ϕ π x y = true ↔ LowerAt ϕ π x y := by
  induction π generalizing x y with
  | nil => simp [lowerAtB, PathDecision.lower, mem_derivedPairs]
  | cons i π ih =>
    change (ϕ.any fun
      | .fLe z₁ z₂ z => derivesB ϕ z y && lowerAtB ϕ π x (if i = 0 then z₁ else z₂)
      | _ => false) = true ↔ _
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨l, hl, h⟩
      cases l <;> simp only [Bool.false_eq_true, Bool.and_eq_true, derivesB_iff, ih] at h
      exact .cons hl h.1 h.2
    · intro h
      cases h with
      | cons hl hd hp =>
        refine ⟨_, hl, ?_⟩
        simp only [Bool.and_eq_true, derivesB_iff, ih]
        exact ⟨hd, hp⟩

theorem upperAtB_iff (ϕ : Constraint k) (π : List (Fin 2)) (x y : V k) :
    upperAtB ϕ π x y = true ↔ UpperAt ϕ π x y := by
  induction π generalizing x y with
  | nil => simp [upperAtB, PathDecision.upper, mem_derivedPairs]
  | cons i π ih =>
    change (ϕ.any fun
      | .leF z z₁ z₂ => derivesB ϕ x z && upperAtB ϕ π (if i = 0 then z₁ else z₂) y
      | _ => false) = true ↔ _
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨l, hl, h⟩
      cases l <;> simp only [Bool.false_eq_true, Bool.and_eq_true, derivesB_iff, ih] at h
      exact .cons h.1 hl h.2
    · intro h
      cases h with
      | cons hd hl hp =>
        refine ⟨_, hl, ?_⟩
        simp only [Bool.and_eq_true, derivesB_iff, ih]
        exact ⟨hd, hp⟩

/-- Enumerate the nonempty binary paths of length at most the given bound. -/
def pathsUpTo : ℕ → List (List (Fin 2))
  | 0 => []
  | n + 1 => [[0], [1]] ++ (pathsUpTo n).map (0 :: ·) ++ (pathsUpTo n).map (1 :: ·)

theorem mem_pathsUpTo (ρ : List (Fin 2)) (n : ℕ) :
    ρ ∈ pathsUpTo n ↔ 0 < ρ.length ∧ ρ.length ≤ n := by
  induction n generalizing ρ with
  | zero => cases ρ <;> simp [pathsUpTo]
  | succ n ih =>
    cases ρ with
    | nil => simp [pathsUpTo]
    | cons i ρ =>
      fin_cases i <;> simp [pathsUpTo, ih] <;>
        cases ρ <;> simp_all

/-- Search for a cycle clash along paths of length at most the number of variable pairs. -/
def cycleClashB (ϕ : Constraint k) : Bool :=
  let pairs := derivedPairs ϕ
  (pathsUpTo (k * k)).any fun ρ =>
    (List.finRange k).any fun x => (List.finRange k).any fun y =>
      PathDecision.lower ϕ pairs ρ x x && decide ((x, y) ∈ pairs) &&
        PathDecision.upper ϕ pairs ρ y y

theorem cycleClashB_iff_bounded (ϕ : Constraint k) :
    cycleClashB ϕ = true ↔ ∃ ρ x y,
      0 < ρ.length ∧ ρ.length ≤ k * k ∧
      LowerAt ϕ ρ x x ∧ Derives ϕ x y ∧ UpperAt ϕ ρ y y := by
  change (pathsUpTo (k * k)).any (fun ρ => (List.finRange k).any fun x =>
    (List.finRange k).any fun y =>
      lowerAtB ϕ ρ x x && derivesB ϕ x y && upperAtB ϕ ρ y y) = true ↔ _
  simp only [List.any_eq_true, mem_pathsUpTo, List.mem_finRange,
    true_and, Bool.and_eq_true,
    lowerAtB_iff, derivesB_iff, upperAtB_iff]
  aesop

theorem cycleClashB_sound {ϕ : Constraint k} (h : cycleClashB ϕ = true) :
    CycleClash ϕ := by
  obtain ⟨ρ, x, y, hp, _, hl, hd, hu⟩ := (cycleClashB_iff_bounded ϕ).mp h
  exact ⟨ρ, x, y, List.ne_nil_of_length_pos hp, hl, hd, hu⟩

theorem cycleClashB_complete {ϕ : Constraint k} (hn : ¬ LabelClash ϕ)
    (h : CycleClash ϕ) : cycleClashB ϕ = true :=
  (cycleClashB_iff_bounded ϕ).mpr ((cycleClash_iff_bounded hn).mp h)

/-- Decide satisfiability over arbitrary trees by excluding label clashes. -/
def satInfB (ϕ : Constraint k) : Bool := !labelClashB ϕ

/-- Decide satisfiability over finite trees by excluding label and cycle clashes. -/
def satFinB (ϕ : Constraint k) : Bool := !labelClashB ϕ && !cycleClashB ϕ

theorem satInfB_iff (ϕ : Constraint k) :
    satInfB ϕ = true ↔ ∃ ρ : V k → Tree, Sat ρ ϕ := by
  rw [satisfiable_iff_not_labelClash]
  simp [satInfB, Bool.eq_false_iff, labelClashB_iff]

theorem satFinB_iff (ϕ : Constraint k) :
    satFinB ϕ = true ↔ ∃ σ : V k → FTree, Sat (FTree.toTree ∘ σ) ϕ := by
  rw [satFin_iff]
  have hl : satInfB ϕ = true ↔ ¬ LabelClash ϕ :=
    (satInfB_iff ϕ).trans satisfiable_iff_not_labelClash
  change (satInfB ϕ && !cycleClashB ϕ) = true ↔ _
  rw [Bool.and_eq_true, hl]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun h => ?_⟩
    simp [cycleClashB_complete hn h] at hc
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    have hb : cycleClashB ϕ ≠ true := fun h => hc (cycleClashB_sound h)
    cases h : cycleClashB ϕ <;> simp_all

namespace Lit

def rename {m : ℕ} (r : V k → V m) : Lit k → Lit m
  | .leF x a b => .leF (r x) (r a) (r b)
  | .fLe a b x => .fLe (r a) (r b) (r x)
  | .eqBot x => .eqBot (r x)
  | .eqTop x => .eqTop (r x)

@[simp] theorem holds_rename {m : ℕ} (r : V k → V m) (ρ : V m → Tree)
    (l : Lit k) : (l.rename r).holds ρ ↔ l.holds (ρ ∘ r) := by
  cases l <;> rfl

end Lit

theorem sat_rename {m : ℕ} (r : V k → V m) (ρ : V m → Tree) (ϕ : Constraint k) :
    Sat ρ (ϕ.map (Lit.rename r)) ↔ Sat (ρ ∘ r) ϕ := by
  simp [Sat]

end DeciNSSE
