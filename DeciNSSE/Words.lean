import Mathlib.Data.List.PeriodicityLemma

/-! # Binary words and periodic caps

Binary words describe paths in trees. Prefix closure, powers and periods describe
the ordinary and periodic parts of the automata languages used for entailment.
-/

namespace DeciNSSE.Words

/-- Binary words, representing paths through the two children of constructor nodes. -/
abbrev Word := List (Fin 2)

variable {μ π : Word} {S : Set Word} {p : ℕ}

/-- Concatenate a word with itself the specified number of times. -/
def pow (μ : Word) : ℕ → Word
  | 0 => []
  | n + 1 => μ ++ pow μ n

@[simp] theorem pow_zero (μ : Word) : pow μ 0 = [] := rfl

@[simp] theorem pow_succ (μ : Word) (n : ℕ) : pow μ (n + 1) = μ ++ pow μ n := rfl

@[simp] theorem pow_one (μ : Word) : pow μ 1 = μ := by simp

@[simp] theorem length_pow (μ : Word) (n : ℕ) : (pow μ n).length = n * μ.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem pow_nil (n : ℕ) : pow [] n = [] := by
  induction n <;> simp_all

/-- The prefix closure of a language of words. -/
def Pr (S : Set Word) : Set Word := {π | ∃ σ ∈ S, π <+: σ}

theorem subset_pr : S ⊆ Pr S := fun π hπ => ⟨π, hπ, List.prefix_rfl⟩

@[simp] theorem pr_idempotent (S : Set Word) : Pr (Pr S) = Pr S := by
  apply Set.Subset.antisymm
  · rintro π ⟨τ, ⟨σ, hσ, hτ⟩, hπ⟩
    exact ⟨σ, hσ, hπ.trans hτ⟩
  · exact subset_pr

/-- A word is a prefix of some finite power of the given root word. -/
def IsPrefixOfPower (μ π : Word) : Prop := ∃ n, π <+: pow μ n

theorem prefix_append_of_prefix_pow (n : ℕ) (h : π <+: pow μ n) : π <+: μ ++ π := by
  induction n generalizing π with
  | zero => simp only [pow_zero, List.prefix_nil] at h; simp [h]
  | succ n ih =>
    rw [pow_succ] at h
    by_cases hlen : π.length ≤ μ.length
    · exact ((List.isPrefix_append_of_length hlen).mp h).trans (List.prefix_append _ _)
    · have hμ : μ <+: π :=
        List.prefix_of_prefix_length_le (List.prefix_append _ _) h (by omega)
      obtain ⟨τ, rfl⟩ := hμ
      rw [List.prefix_append_right_inj] at h
      simpa only [List.append_assoc, List.prefix_append_right_inj] using ih h

/-- For a nonempty root, being a prefix of a power is equivalent to a single prefix comparison. -/
theorem prefix_pow_iff (hμ : μ ≠ []) : IsPrefixOfPower μ π ↔ π <+: μ ++ π := by
  constructor
  · rintro ⟨n, h⟩
    exact prefix_append_of_prefix_pow n h
  · intro h
    induction hlen : π.length using Nat.strong_induction_on generalizing π with
    | h len ih =>
      by_cases hshort : π.length ≤ μ.length
      · exact ⟨1, by simpa using (List.isPrefix_append_of_length hshort).mp h⟩
      · have hprefix : μ <+: π :=
          List.prefix_of_prefix_length_le (List.prefix_append _ _) h (by omega)
        obtain ⟨τ, rfl⟩ := hprefix
        have hτ : τ <+: μ ++ τ := by
          simpa only [List.append_assoc, List.prefix_append_right_inj] using h
        have hpos : 0 < μ.length := List.length_pos_iff.mpr hμ
        obtain ⟨n, hn⟩ := ih τ.length (by simp only [List.length_append] at hlen; omega) hτ rfl
        exact ⟨n + 1, by simpa only [pow_succ, List.prefix_append_right_inj] using hn⟩

@[simp] theorem isPrefixOfPower_nil_iff : IsPrefixOfPower [] π ↔ π = [] := by
  simp [IsPrefixOfPower]

/-- Letters at positions separated by the period agree whenever both positions exist. -/
def HasPeriod (π : Word) (p : ℕ) : Prop :=
  ∀ i, i + p < π.length → π[i]? = π[i + p]?

theorem hasPeriod_iff_list_hasPeriod : HasPeriod π p ↔ List.HasPeriod π p := by
  rw [List.hasPeriod_iff_getElem?]
  unfold HasPeriod
  constructor <;> intro h i hi <;> apply h i <;> omega

theorem hasPeriod_iff_prefix_pow (_hpos : 0 < p) (_hle : p ≤ π.length) :
    HasPeriod π p ↔ π <+: (π.take p) ++ π :=
  hasPeriod_iff_list_hasPeriod

theorem hasPeriod_iff_isPrefixOfPower_take (hpos : 0 < p) (hle : p ≤ π.length) :
    HasPeriod π p ↔ IsPrefixOfPower (π.take p) π := by
  have htake : π.take p ≠ [] := by
    apply List.length_pos_iff.mp
    simp only [List.length_take, Nat.min_eq_left hle]
    exact hpos
  rw [prefix_pow_iff htake, hasPeriod_iff_prefix_pow hpos hle]

/-- The language of prefixes of powers of root words in the given language. -/
def Cap (S : Set Word) : Set Word := {π | ∃ μ ∈ S, IsPrefixOfPower μ π}

theorem Pr_subset_cap : Pr S ⊆ Cap S := by
  rintro π ⟨μ, hμ, hπ⟩
  exact ⟨μ, hμ, 1, by simpa using hπ⟩

/-- Cap membership splits into ordinary prefix membership and a proper periodic witness. -/
theorem mem_cap_iff : π ∈ Cap S ↔ π ∈ Pr S ∨
    ∃ p, 0 < p ∧ p < π.length ∧ HasPeriod π p ∧ π.take p ∈ S := by
  constructor
  · rintro ⟨μ, hμ, n, hπ⟩
    have hshift := prefix_append_of_prefix_pow n hπ
    by_cases hshort : π.length ≤ μ.length
    · exact Or.inl ⟨μ, hμ, (List.isPrefix_append_of_length hshort).mp hshift⟩
    · have hnonempty : μ ≠ [] := by
        intro heq
        subst μ
        simp only [pow_nil, List.prefix_nil] at hπ
        simp [hπ] at hshort
      have hpos : 0 < μ.length := List.length_pos_iff.mpr hnonempty
      have hroot : μ <+: π :=
        List.prefix_of_prefix_length_le (List.prefix_append _ _) hshift (by omega)
      have htake := List.prefix_iff_eq_take.mp hroot
      refine Or.inr ⟨μ.length, hpos, by omega, ?_, by rwa [← htake]⟩
      rw [hasPeriod_iff_prefix_pow hpos (by omega), ← htake]
      exact hshift
  · rintro (h | ⟨p, hpos, hlt, hperiod, hroot⟩)
    · exact Pr_subset_cap h
    · exact ⟨π.take p, hroot,
        (hasPeriod_iff_isPrefixOfPower_take hpos (Nat.le_of_lt hlt)).mp hperiod⟩

end DeciNSSE.Words
