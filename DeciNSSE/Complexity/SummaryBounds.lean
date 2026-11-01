import DeciNSSE.Complexity.SummaryGraph
import DeciNSSE.RejectedTail.Decision

/-! # Space bounds for the summary search

A configuration of the summary search stores a level, a table over at most
`n + g` letters and `N + d` cores, and optionally a derivation in progress:
a marker letter, a track count `h ≤ g`, a column summary over `h` tracks and
the started flags of the tracks. The number of bits for each part is
polynomial, so a configuration takes `O((N + d + 1)^2 (n + g + 1)^2)` bits.
For the label monitors of a system with `k` variables, `N = 2 * 4^(2k)`, and
the depth and dictionary bounds of the bounded-depth search make this
`(n + 1)^2 * 2^2^(20k + 20)` bits.

## Main declarations

- `tableBits`, `summaryBits`, `configBits`: bit counts of tables, column
  summaries and configurations.
- `card_config_le`: there are at most `2 ^ configBits N n d g` configurations.
- `configBits_le`: the polynomial bound with constant `11`.
- `configBits_hole_le`: the bound at the depth and dictionary bounds of a
  reader with `N` states.
- `configBits_label_le`: the doubly exponential bound for the label monitors.
-/

namespace DeciNSSE.Complexity.Summary

open LetteredHierarchy BoundedDepth ElementaryBound RejectedTail

/-- Bits of a table with `M` cores over `h` letters, as in `card_table_le`. -/
def tableBits (M h : ℕ) : ℕ := 3 * (M * (h + 1) + 1) ^ 2

/-- Bits of a column summary with `M` cores over `k` tracks, as in `colBound_le_pow`. -/
def summaryBits (M k : ℕ) : ℕ := 2 * M * (M + 1) * k + k ^ 2 + (M + 1) ^ 2 * k ^ 2

/-- Bits of a configuration for a reader with `N` states over `n` letters, at
levels up to `d` and with derivations over at most `g` tracks: the level, the
alphabet size, the table, and the derivation state. -/
def configBits (N n d g : ℕ) : ℕ :=
  d + 2 * (n + g) + 2 * g + 1 + tableBits (N + d) (n + g) + summaryBits (N + d) g

/-- Table bits grow with the cores and the letters. -/
theorem tableBits_mono {M M' h h' : ℕ} (hM : M ≤ M') (hh : h ≤ h') :
    tableBits M h ≤ tableBits M' h' := by
  unfold tableBits; gcongr

/-- Summary bits grow with the cores and the tracks. -/
theorem summaryBits_mono {M M' k k' : ℕ} (hM : M ≤ M') (hk : k ≤ k') :
    summaryBits M k ≤ summaryBits M' k' := by
  unfold summaryBits; gcongr

section Card
universe u

/-- A derivation over `h₀` letters, with at most `M` cores and at most `g` tracks, takes at
most `h₀ + 2 g + summaryBits M g` bits. -/
theorem card_derivation_le (C : Type u) [Fintype C] [DecidableEq C] (h₀ g : ℕ) {M : ℕ}
    (hM : Fintype.card C ≤ M) :
    Fintype.card (Derivation C h₀ g) ≤ 2 ^ (h₀ + 2 * g + summaryBits M g) := by
  have hterm (h : Fin (g + 1)) :
      Fintype.card (ColumnSummary C h × (Fin h → Bool)) ≤ 2 ^ (summaryBits M g + g) := by
    rw [Fintype.card_prod, card_columnSummary, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, pow_add]
    exact Nat.mul_le_mul ((colBound_le_pow _ _).trans
      (Nat.pow_le_pow_right (by decide) (summaryBits_mono hM (by omega))))
      (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    _ = ∑ _ : Fin h₀, ∑ h : Fin (g + 1), Fintype.card (ColumnSummary C h × (Fin h → Bool)) := by
      simp only [Derivation, Fintype.card_sigma]
    _ ≤ ∑ _ : Fin h₀, ∑ _ : Fin (g + 1), 2 ^ (summaryBits M g + g) := by
      gcongr with _ _ h
      exact hterm h
    _ = h₀ * ((g + 1) * 2 ^ (summaryBits M g + g)) := by simp
    _ ≤ 2 ^ h₀ * (2 ^ g * 2 ^ (summaryBits M g + g)) := by
      gcongr
      · exact Nat.lt_two_pow_self.le
      · exact Nat.lt_two_pow_self
    _ = 2 ^ (h₀ + 2 * g + summaryBits M g) := by rw [← pow_add, ← pow_add]; ring_nf

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- The summary search for a reader with `N` states has at most `2 ^ configBits N n d g`
configurations. -/
theorem card_config_le (n d g : ℕ) :
    Fintype.card (Config Q n d g) ≤ 2 ^ configBits (Fintype.card Q) n d g := by
  set N := Fintype.card Q
  set e := tableBits (N + d) (n + g) + (n + g + 2 * g + summaryBits (N + d) g + 1) with he
  have hterm (j : Fin (d + 1)) (h₀ : Fin (max n g + 1)) :
      Fintype.card (Table (Fin h₀) (Cores Q j) × Option (Derivation (Cores Q j) h₀ g)) ≤ 2 ^ e := by
    have hC : Fintype.card (Cores Q j) ≤ N + d := by rw [card_cores]; omega
    have hh : (h₀ : ℕ) ≤ n + g := by have := h₀.2; omega
    rw [Fintype.card_prod, Fintype.card_option, pow_add]
    refine Nat.mul_le_mul ((card_table_le _ _).trans (Nat.pow_le_pow_right (by decide) ?_)) ?_
    · rw [Fintype.card_fin]
      exact tableBits_mono hC hh
    · have hD := (card_derivation_le (Cores Q j) h₀ g hC).trans
        (Nat.pow_le_pow_right (by decide) (by omega :
          (h₀ : ℕ) + 2 * g + summaryBits (N + d) g ≤ n + g + 2 * g + summaryBits (N + d) g))
      have := Nat.one_le_two_pow (n := n + g + 2 * g + summaryBits (N + d) g)
      rw [pow_succ]
      omega
  calc
    _ = ∑ j : Fin (d + 1), ∑ h₀ : Fin (max n g + 1),
        Fintype.card (Table (Fin h₀) (Cores Q j) × Option (Derivation (Cores Q j) h₀ g)) := by
      simp only [Config, Fintype.card_sigma]
    _ ≤ ∑ _ : Fin (d + 1), ∑ _ : Fin (max n g + 1), 2 ^ e := by
      gcongr with j _ h₀
      exact hterm j h₀
    _ = (d + 1) * ((max n g + 1) * 2 ^ e) := by simp
    _ ≤ 2 ^ d * (2 ^ (n + g) * 2 ^ e) := by
      gcongr
      · exact Nat.lt_two_pow_self
      · exact (by omega : max n g + 1 ≤ n + g + 1).trans Nat.lt_two_pow_self
    _ = 2 ^ configBits N n d g := by
      rw [← pow_add, ← pow_add, he]
      unfold configBits
      ring_nf

end Card

/-- A configuration takes a number of bits quadratic in `N + d + 1` and in `n + g + 1`. -/
theorem configBits_le (N n d g : ℕ) :
    configBits N n d g ≤ 11 * (N + d + 1) ^ 2 * (n + g + 1) ^ 2 := by
  unfold configBits tableBits summaryBits
  have hd : d ≤ N + d := Nat.le_add_left d N
  generalize N + d = M at hd ⊢
  have hg : g ≤ n + g := Nat.le_add_left g n
  generalize n + g = h at hg ⊢
  have hM1 : M + 1 ≤ (M + 1) * (h + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hM : M ≤ (M + 1) * (h + 1) := (Nat.le_succ M).trans hM1
  have hh : h + 1 ≤ (M + 1) * (h + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hMh : M * (h + 1) + 1 ≤ (M + 1) * (h + 1) := by nlinarith
  have h2 : (M * (h + 1) + 1) ^ 2 ≤ ((M + 1) * (h + 1)) ^ 2 := Nat.pow_le_pow_left hMh 2
  have h3 : M * (M + 1) * g ≤ ((M + 1) * (h + 1)) ^ 2 := by
    rw [sq, show M * (M + 1) * g = (M + 1) * (M * g) by ring]
    exact Nat.mul_le_mul (by omega) ((Nat.mul_le_mul_left M (by omega : g ≤ h + 1)).trans
      (by omega))
  have h4 : (M + 1) ^ 2 * g ^ 2 ≤ ((M + 1) * (h + 1)) ^ 2 := by
    rw [mul_pow]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h5 : g ^ 2 ≤ ((M + 1) * (h + 1)) ^ 2 := Nat.pow_le_pow_left (hg.trans (by omega)) 2
  have h6 : (M + 1) * (h + 1) ≤ ((M + 1) * (h + 1)) ^ 2 := Nat.le_self_pow (by decide) _
  nlinarith

/-- At the depth and dictionary bounds of a reader with `N` states, a
configuration takes at most `(n + 1)^2 * 2^(1024 (N + 1)^5)` bits. -/
theorem configBits_hole_le (N n : ℕ) :
    configBits N n (holeDepthBound N) (dictionaryBound N (holeDepthBound N)) ≤
      (n + 1) ^ 2 * 2 ^ (1024 * (N + 1) ^ 5) := by
  set d := holeDepthBound N
  set g := dictionaryBound N d
  set X := (N + 1) ^ 5
  have hE : dictionaryExponent N d < 256 * X := dictionaryExponent_hole_lt N
  have hg : g + 1 ≤ 2 ^ (dictionaryExponent N d + 1) := by
    have := dictionaryBound_le N d
    have := Nat.one_le_two_pow (n := dictionaryExponent N d)
    rw [pow_succ]
    omega
  have hd : N + d + 1 ≤ 9 * (N + 1) ^ 2 := by
    have := holeDepthBound_le N
    nlinarith
  have hN : (N + 1) ^ 4 ≤ 2 ^ (4 * N) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self 4
  have hX : N + 1 ≤ X := Nat.le_self_pow (by decide) _
  have hng : n + g + 1 ≤ (n + 1) * (g + 1) := by nlinarith
  calc
    _ ≤ 11 * (N + d + 1) ^ 2 * (n + g + 1) ^ 2 := configBits_le N n d g
    _ ≤ 11 * (9 * (N + 1) ^ 2) ^ 2 * ((n + 1) * (g + 1)) ^ 2 := by gcongr
    _ = (n + 1) ^ 2 * (891 * (N + 1) ^ 4 * (g + 1) ^ 2) := by ring
    _ ≤ (n + 1) ^ 2 * (2 ^ 11 * 2 ^ (4 * N) * (2 ^ (dictionaryExponent N d + 1)) ^ 2) := by
      gcongr
      omega
    _ = (n + 1) ^ 2 * 2 ^ (11 + 4 * N + 2 * (dictionaryExponent N d + 1)) := by
      rw [← pow_mul, ← pow_add, ← pow_add, mul_comm (dictionaryExponent N d + 1)]
    _ ≤ (n + 1) ^ 2 * 2 ^ (1024 * X) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))

/-- For the label monitors of a system with `k` variables, a configuration
takes at most `(n + 1)^2 * 2^2^(20k + 20)` bits. -/
theorem configBits_label_le (n k : ℕ) :
    configBits (2 * 4 ^ (2 * k)) n (holeDepthBound (2 * 4 ^ (2 * k)))
        (dictionaryBound (2 * 4 ^ (2 * k)) (holeDepthBound (2 * 4 ^ (2 * k)))) ≤
      (n + 1) ^ 2 * 2 ^ 2 ^ (20 * k + 20) := by
  refine (configBits_hole_le _ n).trans (Nat.mul_le_mul_left _ ?_)
  apply Nat.pow_le_pow_right (by decide)
  have hN : 2 * 4 ^ (2 * k) + 1 ≤ 2 ^ (4 * k + 2) := by
    have h4 : 4 ^ (2 * k) = 2 ^ (4 * k) := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]; ring_nf
    rw [h4, pow_add]
    have := Nat.one_le_two_pow (n := 4 * k)
    omega
  calc
    _ ≤ 2 ^ 10 * (2 ^ (4 * k + 2)) ^ 5 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hN 5)
    _ = 2 ^ (20 * k + 20) := by rw [← pow_mul, ← pow_add]; ring_nf

end DeciNSSE.Complexity.Summary
