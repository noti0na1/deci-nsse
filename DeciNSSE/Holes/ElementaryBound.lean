import DeciNSSE.Holes.NormalForm

/-! # Elementary bounds for holes of bounded depth

Normal forms bound the positive dictionaries by a geometric recurrence.
Supported column compression then gives a length bound with fixed exponential height.
-/

set_option autoImplicit false

namespace DeciNSSE.ElementaryBound
open CoAlignment LetteredHierarchy HierarchyDepth NormalForm BoundaryPairs BoundedDepth

/-- A uniform bound on every positive dictionary through the first unary level. -/
def dictionaryBound (N d : ℕ) : ℕ := 2 + normalAllowance N d * 3 ^ d

/-- The length allowance obtained by descending through bounded dictionaries. -/
def lengthBound (N d : ℕ) : ℕ :=
  (N + d + 1) * descentFactor N d (dictionaryBound N d) ^ d

section Normal
variable {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q] [DecidableEq Q]
variable {D0 : Lettered α Q} {w : List α} {d i : ℕ}

/-- The first unary dictionary has at most one letter. -/
theorem alphCard_depth_le_one (w : List α) : alphCard w (depth w) ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact isUnary_depth w a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb)

/-- The division-free geometric bound on boundary pairs in a normal form. -/
theorem normal_boundary_count_le (hw : D0.IsHole w) (hn : Normal D0 w)
    (hd : depth w ≤ d) (hi : 1 ≤ i) (hid : i < depth w) :
    2 * (boundaryPairs (hierOf w i)).card ≤
      (normalAllowance (Fintype.card Q) d - 1) * (3 ^ (depth w - 1 - i) - 1) := by
  let A := normalAllowance (Fintype.card Q) d
  have hA : 1 ≤ A := by dsimp [A, normalAllowance]; omega
  have H : ∀ k i, 1 ≤ i → i + k + 1 = depth w →
      2 * (boundaryPairs (hierOf w i)).card + (A - 1) ≤ (A - 1) * 3 ^ k := by
    intro k
    induction k with
    | zero =>
      intro i hi he
      have hs := boundaryCount_step_add_one hw.ne_nil i
      have ht := alphCard_depth_le_one w
      have hb := boundaryPairs_eq_empty_of_isUnary (isUnary_depth w)
      have he' : i + 1 = depth w := by omega
      change _ + 1 ≤ _ + alphCard w (i + 1) at hs
      rw [he', hb, Finset.card_empty] at hs
      simp only [pow_zero, mul_one]
      omega
    | succ k ih =>
      intro i hi he
      have hb := ih (i + 1) (by omega) (by omega)
      have hg := normalAt_alphCard_le hw (hn (i + 1) (by omega) (by omega))
        (by omega) (by omega) hd
      have hs := boundaryCount_step_add_one hw.ne_nil i
      change _ ≤ A + _ at hg
      change _ + 1 ≤ _ + alphCard w (i + 1) at hs
      rw [pow_succ]
      nlinarith only [hb, hg, hs, Nat.sub_add_cancel hA]
  have h := H (depth w - 1 - i) i hi (by omega)
  change _ ≤ (A - 1) * _
  rw [Nat.mul_sub_left_distrib, mul_one]
  omega

/-- Normal dictionaries grow by at most a factor of three per level below the top. -/
theorem normal_alphCard_le (hw : D0.IsHole w) (hn : Normal D0 w)
    (hd : depth w ≤ d) (hi : 1 ≤ i) (hid : i < depth w) :
    alphCard w i ≤ 1 + (normalAllowance (Fintype.card Q) d - 1) *
      3 ^ (depth w - 1 - i) := by
  have hg := normalAt_alphCard_le hw (hn i hi hid) hi hid hd
  have hb := normal_boundary_count_le hw hn hd hi hid
  have hA : 1 ≤ normalAllowance (Fintype.card Q) d := by unfold normalAllowance; omega
  have hp : 1 ≤ 3 ^ (depth w - 1 - i) := Nat.one_le_pow _ _ (by decide)
  rw [Nat.mul_sub_left_distrib, mul_one] at hb
  have hm := Nat.mul_le_mul_left (normalAllowance (Fintype.card Q) d - 1) hp
  simp only [mul_one] at hm
  omega

/-- Every hole has a hole of the same depth and no greater length with bounded positive dictionaries. -/
theorem exists_bounded_dictionary_hole (hw : D0.IsHole w) (hd : depth w ≤ d) :
    ∃ v, D0.IsHole v ∧ depth v = depth w ∧ v.length ≤ w.length ∧
      ∀ i, 1 ≤ i → i ≤ depth v → alphCard v i ≤ dictionaryBound (Fintype.card Q) d := by
  obtain ⟨v, hv, hdepth, hlen, _, _, hn⟩ := exists_normal_form hw
  refine ⟨v, hv, hdepth, hlen, fun i hi hid => ?_⟩
  rcases eq_or_lt_of_le hid with rfl | hid
  · exact (alphCard_depth_le_one v).trans (by unfold dictionaryBound; omega)
  · have hg := normal_alphCard_le (d := d) hv hn (by omega) hi hid
    refine hg.trans ?_
    unfold dictionaryBound
    have hp : 3 ^ (depth v - 1 - i) ≤ 3 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    have hm := Nat.mul_le_mul (Nat.sub_le (normalAllowance (Fintype.card Q) d) 1) hp
    omega

end Normal

/-- Every bounded-depth hole has an elementary-length witness over the same alphabet. -/
theorem exists_short_hole {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q]
    {D0 : Lettered α Q} {w : List α} {d : ℕ} (hw : D0.IsHole w) (hL : InL d w) :
    ∃ v, D0.IsHole v ∧ InL d v ∧ v.length ≤ lengthBound (Fintype.card Q) d := by
  classical
  obtain ⟨i, hi, hu⟩ := hL
  have hd : depth w ≤ d := (Nat.find_min' (exists_isUnary_hierOf w) hu).trans hi
  obtain ⟨v, hv, hdepth, _, hg⟩ := exists_bounded_dictionary_hole hw hd
  exact exists_short_hole_of_dictionary D0 hv (hdepth ▸ hd) (isUnary_depth v) hg

/-- A power-of-two allowance for the normal dictionary. -/
def dictionaryExponent (N d : ℕ) : ℕ :=
  3 * N ^ 2 + 4 * N * (N + d) * (d + 1) + 3 * N + 3 * d + 4

private theorem add_le_two_pow {a b p q : ℕ} (ha : a ≤ 2 ^ p) (hb : b ≤ 2 ^ q) :
    a + b ≤ 2 ^ (p + q + 1) := by
  have hp : 2 ^ p ≤ 2 ^ (p + q) := Nat.pow_le_pow_right (by decide) (by omega)
  have hq : 2 ^ q ≤ 2 ^ (p + q) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega

/-- The dictionary allowance is singly exponential in a polynomial in cores and depth. -/
theorem dictionaryBound_le (N d : ℕ) : dictionaryBound N d ≤ 2 ^ dictionaryExponent N d := by
  let E := 3 * N ^ 2 + 4 * N * (N + d) * (d + 1) + 3 * N
  have hC : normalTypeBound N d ≤ 2 ^ E := by
    unfold normalTypeBound Exchange.typeBound
    calc
      _ ≤ (2 ^ N) ^ N * 2 ^ (2 * N ^ 2 + 4 * N * (N + d) * (d + 1) + 3 * N) := by
        gcongr
        exact Nat.lt_two_pow_self.le
      _ = 2 ^ E := by rw [← pow_mul, ← pow_add]; congr 1; dsimp [E]; ring
  have hA : normalAllowance N d ≤ 2 ^ (d + 1 + E + 1) :=
    add_le_two_pow (Nat.le_of_lt (Nat.lt_two_pow_self (n := d + 1))) hC
  have h3 : 3 ^ d ≤ 2 ^ (2 * d) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by decide) d
  have hprod := Nat.mul_le_mul hA h3
  rw [← pow_add] at hprod
  have htwo : 2 ≤ 2 ^ (d + 1 + E + 1 + 2 * d) := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ d + 1 + E + 1 + 2 * d by omega)
    simpa using this
  unfold dictionaryBound
  calc
    _ ≤ 2 ^ (d + 1 + E + 1 + 2 * d) * 2 := by omega
    _ ≤ 2 ^ dictionaryExponent N d := by
      rw [← pow_succ]
      apply Nat.pow_le_pow_right (by decide)
      dsimp [dictionaryExponent, E]
      omega

private theorem colBound_le_pow (M g : ℕ) :
    colBound M g ≤ 2 ^ (2 * M * (M + 1) * g + g ^ 2 + (M + 1) ^ 2 * g ^ 2) := by
  unfold colBound
  calc
    _ ≤ ((2 ^ M) ^ (M + 1)) ^ g * ((2 ^ M) ^ (M + 1)) ^ g * (2 ^ g) ^ g *
        (((2 ^ (M + 1)) ^ (M + 1)) ^ g) ^ g := by
      gcongr
      exact Nat.lt_two_pow_self.le
    _ = _ := by simp only [← pow_mul, ← pow_add]; congr 1; ring

/-- The length allowance has two exponentials with a polynomial top exponent. -/
theorem lengthBound_le (N d : ℕ) :
    lengthBound N d ≤ 2 ^ 2 ^ (5 * dictionaryExponent N d + 3) := by
  let H := dictionaryExponent N d
  let M := N + d + 1
  let g := dictionaryBound N d
  have hH : M + 1 ≤ H := by dsimp [M, H, dictionaryExponent]; omega
  have hM : M ≤ 2 ^ H := (by omega : M ≤ H).trans Nat.lt_two_pow_self.le
  have hM1 : M + 1 ≤ 2 ^ H := hH.trans Nat.lt_two_pow_self.le
  have hd : d ≤ 2 ^ H := (by dsimp [M] at hH; omega : d ≤ H).trans Nat.lt_two_pow_self.le
  have hg : g ≤ 2 ^ H := dictionaryBound_le N d
  have hP : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have hcol : colBound M g ≤ 2 ^ (4 * (2 ^ H) ^ 4) := by
    apply (colBound_le_pow M g).trans
    apply Nat.pow_le_pow_right (by decide)
    calc
      _ ≤ 2 * (2 ^ H) * (2 ^ H) * (2 ^ H) + (2 ^ H) ^ 2 +
          (2 ^ H) ^ 2 * (2 ^ H) ^ 2 := by gcongr
      _ = 2 * (2 ^ H) ^ 3 + (2 ^ H) ^ 2 + (2 ^ H) ^ 4 := by ring
      _ ≤ 2 * (2 ^ H) ^ 4 + (2 ^ H) ^ 4 + (2 ^ H) ^ 4 := by
        exact Nat.add_le_add (Nat.add_le_add
          (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hP (by decide : 3 ≤ 4)))
          (Nat.pow_le_pow_right hP (by decide : 2 ≤ 4))) le_rfl
      _ = 4 * (2 ^ H) ^ 4 := by ring
  have hcol' : colBound M g ≤ 2 ^ 2 ^ (4 * H + 2) := by
    have he : 4 * (2 ^ H) ^ 4 = 2 ^ (4 * H + 2) := by
      rw [← pow_mul, show H * 4 = 4 * H by omega, pow_add]
      simp only [show (2 : ℕ) ^ 2 = 4 from rfl]
      omega
    rwa [he] at hcol
  unfold lengthBound descentFactor
  change M * colBound M g ^ d ≤ _
  calc
    _ ≤ 2 ^ H * (2 ^ 2 ^ (4 * H + 2)) ^ d := by gcongr
    _ = 2 ^ (H + 2 ^ (4 * H + 2) * d) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ 2 ^ (5 * H + 3) := by
      apply Nat.pow_le_pow_right (by decide)
      have hp : 2 ^ H ≤ 2 ^ (5 * H + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      calc
        _ ≤ 2 ^ H + 2 ^ (4 * H + 2) * 2 ^ H := by gcongr; exact Nat.lt_two_pow_self.le
        _ ≤ 2 ^ (5 * H + 2) * 2 := by
          rw [← pow_add, show 4 * H + 2 + H = 5 * H + 2 by omega]
          omega
        _ = 2 ^ (5 * H + 3) := (pow_succ 2 (5 * H + 2)).symm

end DeciNSSE.ElementaryBound
