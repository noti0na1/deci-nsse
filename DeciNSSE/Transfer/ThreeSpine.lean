import DeciNSSE.Constraints.Signed
import DeciNSSE.Semantics.Median

/-! # Three-spine witnesses and symmetrisation

Three prefix conditions on a signed solution suffice to preserve unsafety
under median with the full constructor tree. Symmetrisation then decodes the
witness into the original variance semantics.
-/

namespace DeciNSSE

variable {n k : ℕ}

/-- Constructor literals use three solutions; constants use the two equal leaves. -/
theorem sat_median_full {A B : V k → Tree n} {ϕ : Constraint n k}
    (ha : Covariant.Sat A ϕ) (hb : Covariant.Sat B ϕ) : Covariant.Sat (fun z => Tree.median (A z) (B z) Tree.full) ϕ := by
  intro l hl
  have h₁ := ha l hl
  have h₂ := hb l hl
  cases l with
  | leF u a =>
    have h := median_mono h₁ h₂ full_bounds.1
    rw [median_node] at h
    exact h
  | fLe a u =>
    have h := median_mono h₁ h₂ full_bounds.2
    rw [median_node] at h
    exact h
  | eqBot u =>
    change A u = Tree.bot at h₁
    change B u = Tree.bot at h₂
    change Tree.median (A u) (B u) Tree.full = Tree.bot
    simp [h₁, h₂]
  | eqTop u =>
    change A u = Tree.top at h₁
    change B u = Tree.top at h₂
    change Tree.median (A u) (B u) Tree.full = Tree.top
    simp [h₁, h₂]

/-- Median of a signed assignment, its sign-dual, and the all-constructor tree. -/
noncomputable def Signed.symmetrize (A : V (2 * k) → Tree n) (z : V (2 * k)) : Tree n :=
  Tree.median (A z) (Signed.dual A z) Tree.full

/-- Median symmetrisation preserves the signed constraints. -/
theorem symmetrize_sat (c : Fin n → Bool) {A : V (2 * k) → Tree n}
    {ϕ : Constraint n k} (h : Covariant.Sat A (signed c ϕ)) :
    Covariant.Sat (Signed.symmetrize A) (signed c ϕ) :=
  sat_median_full h (sat_signedDual c h)

/-- Median symmetrisation produces an assignment fixed by sign duality. -/
@[simp] theorem symmetrize_fixed (A : V (2 * k) → Tree n) :
    Signed.dual (Signed.symmetrize A) = Signed.symmetrize A := by
  funext z
  obtain ⟨u, p, rfl⟩ := sv_cases z
  simp only [signedDual_sv, Signed.symmetrize, dual_median, dual_full, Bool.not_not, dual_involutive]
  exact median_swap _ _ _

theorem median_signed_solution (c : Fin n → Bool) {A : V (2 * k) → Tree n}
    {ϕ : Constraint n k} (h : Covariant.Sat A (signed c ϕ)) :
    Covariant.Sat (Signed.symmetrize A) (signed c ϕ) ∧ Signed.dual (Signed.symmetrize A) = Signed.symmetrize A :=
  ⟨symmetrize_sat c h, symmetrize_fixed A⟩

/-- A covariant signed solution gives a variance solution by symmetrisation and decoding. -/
theorem signed_sat_implies_sat (c : Fin n → Bool) (ϕ : Constraint n k)
    (h : ∃ A, Covariant.Sat A (signed c ϕ)) : ∃ ρ, Sat c ρ ϕ := by
  obtain ⟨A, ha⟩ := h
  obtain ⟨ρ, hρ, _⟩ := (fixed_solution_correspondence c ϕ (Signed.symmetrize A)).mp
    (median_signed_solution c ha)
  exact ⟨ρ, hρ⟩

/-- Satisfiability is preserved and reflected by the signed translation. -/
theorem sat_iff_signed_sat (c : Fin n → Bool) (ϕ : Constraint n k) :
    (∃ ρ, Sat c ρ ϕ) ↔ ∃ A, Covariant.Sat A (signed c ϕ) :=
  ⟨sat_implies_signed_sat c ϕ, signed_sat_implies_sat c ϕ⟩

@[simp] theorem trace_median_full_top (a b : Tree n) (w : List (Fin n)) :
    Tree.trace (Tree.median a b Tree.full) w = .top ↔ Tree.trace a w = .top ∧ Tree.trace b w = .top := by
  simp only [trace_median, trace_full]
  cases Tree.trace a w <;> cases Tree.trace b w <;> decide

@[simp] theorem trace_median_full_bot (a b : Tree n) (w : List (Fin n)) :
    Tree.trace (Tree.median a b Tree.full) w = .bot ↔ Tree.trace a w = .bot ∧ Tree.trace b w = .bot := by
  simp only [trace_median, trace_full]
  cases Tree.trace a w <;> cases Tree.trace b w <;> decide

@[simp] theorem covPrefTop_dual (w : List (Fin n)) (t : Tree n) :
    covPrefTop w (Tree.dual t) ↔ covPrefBot w t := by
  simp only [covPrefTop_iff_trace, covPrefBot_iff_trace, trace_dual]
  cases Tree.trace t w <;> decide

@[simp] theorem covPrefBot_dual (w : List (Fin n)) (t : Tree n) :
    covPrefBot w (Tree.dual t) ↔ covPrefTop w t := by
  simp only [covPrefTop_iff_trace, covPrefBot_iff_trace, trace_dual]
  cases Tree.trace t w <;> decide

theorem symmetrize_prefTop (A : V (2 * k) → Tree n) (u : V k) (w : List (Fin n)) :
    covPrefTop w (Signed.symmetrize A (sv u false)) ↔
      covPrefTop w (A (sv u false)) ∧ covPrefBot w (A (sv u true)) := by
  rw [covPrefTop_iff_trace, Signed.symmetrize, trace_median_full_top]
  simp only [signedDual_sv, Bool.not_false, ← covPrefTop_iff_trace, covPrefTop_dual]

theorem symmetrize_prefBot (A : V (2 * k) → Tree n) (u : V k) (w : List (Fin n)) :
    covPrefBot w (Signed.symmetrize A (sv u false)) ↔
      covPrefBot w (A (sv u false)) ∧ covPrefTop w (A (sv u true)) := by
  rw [covPrefBot_iff_trace, Signed.symmetrize, trace_median_full_bot]
  simp only [signedDual_sv, Bool.not_false, ← covPrefBot_iff_trace, covPrefBot_dual]

/-- Exactly one lower and two upper prefix requirements witness left unsafety. -/
theorem leftUnsafe_iff_threeSpine (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) (w : List (Fin n)) :
    (∃ ρ, Sat c ρ ϕ ∧ prefTop c w (ρ x) ∧ ¬ prefTop c w (ρ y)) ↔
      ∃ A, Covariant.Sat A (signed c ϕ) ∧ covPrefTop w (A (sv x false)) ∧
        covPrefBot w (A (sv x true)) ∧ ¬ covPrefTop w (A (sv y false)) := by
  constructor
  · rintro ⟨ρ, hs, hx, hy⟩
    refine ⟨normalized c ρ, (sat_iff_signed c ρ ϕ).mp hs, ?_, ?_, ?_⟩
    · simpa only [normalized_sv, ← prefTop_iff_normalize] using hx
    · simpa only [normalized_sv, normalize_true, covPrefBot_dual, ← prefTop_iff_normalize] using hx
    · simpa only [normalized_sv, ← prefTop_iff_normalize] using hy
  · rintro ⟨A, hs, hx, hx', hy⟩
    obtain ⟨ρ, hρ, he⟩ := (fixed_solution_correspondence c ϕ (Signed.symmetrize A)).mp
      (median_signed_solution c hs)
    have hmx := (symmetrize_prefTop A x w).mpr ⟨hx, hx'⟩
    have hmy : ¬ covPrefTop w (Signed.symmetrize A (sv y false)) :=
      fun h => hy ((symmetrize_prefTop A y w).mp h).1
    rw [he] at hmx hmy
    exact ⟨ρ, hρ, (prefTop_iff_normalize c w (ρ x)).mpr (by simpa using hmx),
      fun h => hmy (by simpa using (prefTop_iff_normalize c w (ρ y)).mp h)⟩

/-- The dual criterion exchanges the extremes and the two query variables. -/
theorem rightUnsafe_iff_threeSpine (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) (w : List (Fin n)) :
    (∃ ρ, Sat c ρ ϕ ∧ prefBot c w (ρ y) ∧ ¬ prefBot c w (ρ x)) ↔
      ∃ A, Covariant.Sat A (signed c ϕ) ∧ covPrefBot w (A (sv y false)) ∧
        covPrefTop w (A (sv y true)) ∧ ¬ covPrefBot w (A (sv x false)) := by
  constructor
  · rintro ⟨ρ, hs, hy, hx⟩
    refine ⟨normalized c ρ, (sat_iff_signed c ρ ϕ).mp hs, ?_, ?_, ?_⟩
    · simpa only [normalized_sv, ← prefBot_iff_normalize] using hy
    · simpa only [normalized_sv, normalize_true, covPrefTop_dual, ← prefBot_iff_normalize] using hy
    · simpa only [normalized_sv, ← prefBot_iff_normalize] using hx
  · rintro ⟨A, hs, hy, hy', hx⟩
    obtain ⟨ρ, hρ, he⟩ := (fixed_solution_correspondence c ϕ (Signed.symmetrize A)).mp
      (median_signed_solution c hs)
    have hmy := (symmetrize_prefBot A y w).mpr ⟨hy, hy'⟩
    have hmx : ¬ covPrefBot w (Signed.symmetrize A (sv x false)) :=
      fun h => hx ((symmetrize_prefBot A x w).mp h).1
    rw [he] at hmy hmx
    exact ⟨ρ, hρ, (prefBot_iff_normalize c w (ρ y)).mpr (by simpa using hmy),
      fun h => hmx (by simpa using (prefBot_iff_normalize c w (ρ x)).mp h)⟩

end DeciNSSE
