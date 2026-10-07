import DeciNSSE.Satisfiability.Finite

/-! # Finite searches for satisfiability

Finite closure and bounded path searches decide label and cycle clashes,
and hence arbitrary-tree and finite-tree covariant satisfiability.
-/

section

namespace DeciNSSE

variable {n k : ℕ}

namespace PathDecision

/-- The shared closure is data, so recursive path checks do not recompute it. -/
def lower (ϕ : Constraint n k) (pairs : Finset (V k × V k)) :
    List (Fin n) → V k → V k → Bool
  | [], x, y => decide ((x, y) ∈ pairs)
  | i :: π, x, y => (lowerLits ϕ).any fun l =>
      decide ((l.2, y) ∈ pairs) && lower ϕ pairs π x (l.1 i)

/-- The symmetric recursion with the same precomputed closure. -/
def upper (ϕ : Constraint n k) (pairs : Finset (V k × V k)) :
    List (Fin n) → V k → V k → Bool
  | [], x, y => decide ((x, y) ∈ pairs)
  | i :: π, x, y => (upperLits ϕ).any fun m =>
      decide ((x, m.1) ∈ pairs) && upper ϕ pairs π (m.2 i) y

end PathDecision

/-- Read a lower path judgment from the root, searching the finite literal list. -/
def lowerAtB (ϕ : Constraint n k) (π : List (Fin n)) (x y : V k) : Bool :=
  PathDecision.lower ϕ (derivedPairs ϕ) π x y

/-- The symmetric executable upper path judgment. -/
def upperAtB (ϕ : Constraint n k) (π : List (Fin n)) (x y : V k) : Bool :=
  PathDecision.upper ϕ (derivedPairs ϕ) π x y

/-- The Boolean lower-path test agrees with the inductive path judgement. -/
theorem lowerAtB_iff (ϕ : Constraint n k) (π : List (Fin n)) (x y : V k) :
    lowerAtB ϕ π x y = true ↔ LowerAt ϕ π x y := by
  induction π generalizing x y with
  | nil => simp [lowerAtB, PathDecision.lower, mem_derivedPairs]
  | cons i π ih =>
    change ((lowerLits ϕ).any fun l =>
      derivesB ϕ l.2 y && lowerAtB ϕ π x (l.1 i)) = true ↔ _
    simp only [List.any_eq_true, Bool.and_eq_true, derivesB_iff, ih]
    constructor
    · rintro ⟨⟨a, u⟩, hl, hd, hp⟩
      exact .cons ((mem_lowerLits ϕ a u).mp hl) hd hp
    · intro h
      cases h with
      | @cons a u _ _ _ _ hl hd hp =>
        exact ⟨(a, u), (mem_lowerLits ϕ a u).mpr hl, hd, hp⟩

/-- The Boolean upper-path test agrees with the inductive path judgement. -/
theorem upperAtB_iff (ϕ : Constraint n k) (π : List (Fin n)) (x y : V k) :
    upperAtB ϕ π x y = true ↔ UpperAt ϕ π x y := by
  induction π generalizing x y with
  | nil => simp [upperAtB, PathDecision.upper, mem_derivedPairs]
  | cons i π ih =>
    change ((upperLits ϕ).any fun m =>
      derivesB ϕ x m.1 && upperAtB ϕ π (m.2 i) y) = true ↔ _
    simp only [List.any_eq_true, Bool.and_eq_true, derivesB_iff, ih]
    constructor
    · rintro ⟨⟨v, b⟩, hm, hd, hp⟩
      exact .cons hd ((mem_upperLits ϕ v b).mp hm) hp
    · intro h
      cases h with
      | @cons _ v b _ _ _ hd hm hp =>
        exact ⟨(v, b), (mem_upperLits ϕ v b).mpr hm, hd, hp⟩

/-- Satisfiability over arbitrary, possibly infinite path trees. -/
def satInfB (ϕ : Constraint n k) : Bool := !labelClashB ϕ

theorem satInfB_iff_not_labelClash (ϕ : Constraint n k) :
    satInfB ϕ = true ↔ ¬ LabelClash ϕ := by
  simp [satInfB, Bool.eq_false_iff, labelClashB_iff]

/-- The covariant satisfiability test succeeds exactly when an arbitrary-tree solution exists. -/
theorem satInfB_iff (ϕ : Constraint n k) :
    satInfB ϕ = true ↔ ∃ ρ : V k → Tree n, Covariant.Sat ρ ϕ := by
  rw [satisfiable_iff_not_labelClash, satInfB_iff_not_labelClash]

end DeciNSSE

end

section

namespace DeciNSSE

variable {n k : ℕ}

/-- All nonempty paths over `Fin n` of length at most the supplied bound. -/
def pathsUpTo (n : ℕ) : ℕ → List (List (Fin n))
  | 0 => []
  | m + 1 => (List.finRange n).map (fun i => [i]) ++
      (List.finRange n).flatMap (fun i => (pathsUpTo n m).map (i :: ·))

theorem mem_pathsUpTo (ρ : List (Fin n)) (m : ℕ) :
    ρ ∈ pathsUpTo n m ↔ 0 < ρ.length ∧ ρ.length ≤ m := by
  induction m generalizing ρ with
  | zero =>
    simp only [pathsUpTo, List.not_mem_nil, false_iff, not_and]
    omega
  | succ m ih =>
    cases ρ with
    | nil => simp [pathsUpTo]
    | cons i ρ =>
      have h1 : i :: ρ ∈ (List.finRange n).map (fun j => [j]) ↔ ρ = [] := by
        simp only [List.mem_map, List.mem_finRange, true_and]
        constructor
        · rintro ⟨j, hj⟩
          exact (List.cons.inj hj).2.symm
        · rintro rfl
          exact ⟨i, rfl⟩
      have h2 : i :: ρ ∈ (List.finRange n).flatMap
          (fun j => (pathsUpTo n m).map (j :: ·)) ↔ ρ ∈ pathsUpTo n m := by
        simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
        constructor
        · rintro ⟨j, σ, hσ, he⟩
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          exact hσ
        · intro h
          exact ⟨i, ρ, h, rfl⟩
      rw [pathsUpTo, List.mem_append, h1, h2, ih]
      cases ρ <;> simp

/-- Search the bounded witnesses; completeness needs absence of a label clash. -/
def cycleClashB (ϕ : Constraint n k) : Bool :=
  let pairs := derivedPairs ϕ
  (pathsUpTo n (k * k)).any fun ρ =>
    (List.finRange k).any fun x => (List.finRange k).any fun y =>
      PathDecision.lower ϕ pairs ρ x x && decide ((x, y) ∈ pairs) &&
        PathDecision.upper ϕ pairs ρ y y

theorem cycleClashB_iff_bounded (ϕ : Constraint n k) :
    cycleClashB ϕ = true ↔ ∃ ρ x y,
      0 < ρ.length ∧ ρ.length ≤ k * k ∧
      LowerAt ϕ ρ x x ∧ Derives ϕ x y ∧ UpperAt ϕ ρ y y := by
  change (pathsUpTo n (k * k)).any (fun ρ => (List.finRange k).any fun x =>
    (List.finRange k).any fun y =>
      lowerAtB ϕ ρ x x && derivesB ϕ x y && upperAtB ϕ ρ y y) = true ↔ _
  simp only [List.any_eq_true, mem_pathsUpTo, List.mem_finRange, true_and,
    Bool.and_eq_true, lowerAtB_iff, derivesB_iff, upperAtB_iff]
  constructor
  · rintro ⟨ρ, ⟨h1, h2⟩, x, y, ⟨hl, hd⟩, hu⟩
    exact ⟨ρ, x, y, h1, h2, hl, hd, hu⟩
  · rintro ⟨ρ, x, y, h1, h2, hl, hd, hu⟩
    exact ⟨ρ, ⟨h1, h2⟩, x, y, ⟨hl, hd⟩, hu⟩

theorem cycleClashB_sound {ϕ : Constraint n k} (h : cycleClashB ϕ = true) :
    CycleClash ϕ := by
  obtain ⟨ρ, x, y, hp, _, hl, hd, hu⟩ := (cycleClashB_iff_bounded ϕ).mp h
  exact ⟨ρ, x, y, List.ne_nil_of_length_pos hp, hl, hd, hu⟩

theorem cycleClashB_complete {ϕ : Constraint n k} (hn : ¬ LabelClash ϕ)
    (h : CycleClash ϕ) : cycleClashB ϕ = true :=
  (cycleClashB_iff_bounded ϕ).mpr ((cycleClash_iff_bounded hn).mp h)

/-- Satisfiability over finite trees. -/
def Covariant.satFinB (ϕ : Constraint n k) : Bool := !labelClashB ϕ && !cycleClashB ϕ

theorem Covariant.satFinB_iff_not_clash (ϕ : Constraint n k) :
    Covariant.satFinB ϕ = true ↔ ¬ LabelClash ϕ ∧ ¬ CycleClash ϕ := by
  change (satInfB ϕ && !cycleClashB ϕ) = true ↔ _
  rw [Bool.and_eq_true, satInfB_iff_not_labelClash]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun h => ?_⟩
    simp [cycleClashB_complete hn h] at hc
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    have hb : cycleClashB ϕ ≠ true := fun h => hc (cycleClashB_sound h)
    cases h : cycleClashB ϕ <;> simp_all

/-- The covariant finite satisfiability test succeeds exactly when a finite solution exists. -/
theorem Covariant.satFinB_iff (ϕ : Constraint n k) :
    Covariant.satFinB ϕ = true ↔ ∃ σ : V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ϕ := by
  rw [satFin_iff, Covariant.satFinB_iff_not_clash]

end DeciNSSE

end
