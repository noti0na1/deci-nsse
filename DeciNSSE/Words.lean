import Mathlib

/-! # Finite words and periods

Prefix comparisons, powers and finite periodic words supply the word operations
used by the rejected-tail argument.
-/

set_option autoImplicit false
namespace DeciNSSE.Words
variable {α : Type*}
variable {μ π u v w : List α} {p q n : ℕ}

/-- Concatenate the word with itself the given number of times. -/
def pow (μ : List α) : ℕ → List α
  | 0 => []
  | n + 1 => μ ++ pow μ n

@[simp] theorem pow_zero (μ : List α) : pow μ 0 = [] := rfl

@[simp] theorem pow_succ (μ : List α) (n : ℕ) : pow μ (n + 1) = μ ++ pow μ n := rfl

@[simp] theorem pow_one (μ : List α) : pow μ 1 = μ := by simp

@[simp] theorem length_pow (μ : List α) (n : ℕ) : (pow μ n).length = n * μ.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem pow_nil (n : ℕ) : pow ([] : List α) n = [] := by
  induction n <;> simp_all

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

/-- Letters at distance `p` agree wherever both positions exist. -/
def HasPeriod (π : List α) (p : ℕ) : Prop :=
  ∀ i, i + p < π.length → π[i]? = π[i + p]?

/-- Bridge to Mathlib's equivalent self-overlap definition. -/
theorem hasPeriod_iff_list_hasPeriod : HasPeriod π p ↔ List.HasPeriod π p := by
  rw [List.hasPeriod_iff_getElem?]
  unfold HasPeriod
  constructor <;> intro h i hi <;> apply h i <;> omega

theorem fine_wilf (hp : HasPeriod w p) (hq : HasPeriod w q)
    (hlen : p + q - Nat.gcd p q ≤ w.length) : HasPeriod w (Nat.gcd p q) :=
  hasPeriod_iff_list_hasPeriod.mpr
    ((hasPeriod_iff_list_hasPeriod.mp hp).gcd (hasPeriod_iff_list_hasPeriod.mp hq) hlen)

theorem HasPeriod.infix (h : HasPeriod w p) (hv : v <:+: w) : HasPeriod v p :=
  hasPeriod_iff_list_hasPeriod.mpr ((hasPeriod_iff_list_hasPeriod.mp h).infix hv)

theorem HasPeriod.mod_eq (h : HasPeriod w p) (hi : n < w.length) :
    w[n]? = w[n % p]? :=
  ((hasPeriod_iff_list_hasPeriod.mp h).getElem?_mod p n w hi).symm

theorem HasPeriod.eq_of_mod (h : HasPeriod w p) {a b : ℕ}
    (ha : a < w.length) (hb : b < w.length) (heq : a % p = b % p) :
    w[a]? = w[b]? := by rw [h.mod_eq ha, h.mod_eq hb, heq]

theorem hasPeriod_pow (u : List α) (n : ℕ) : HasPeriod (pow u n) u.length := by
  apply hasPeriod_iff_list_hasPeriod.mpr
  cases n with
  | zero => simp
  | succ n =>
    change pow u (n + 1) <+: (pow u (n + 1)).take u.length ++ pow u (n + 1)
    rw [pow_succ, List.take_left]
    exact prefix_append_of_prefix_pow (n + 1) List.prefix_rfl

theorem getElem?_pow (hu : u ≠ []) (hi : n < (pow u q).length) :
    (pow u q)[n]? = u[n % u.length]? := by
  rw [(hasPeriod_pow u q).mod_eq hi]
  cases q with
  | zero => simp at hi
  | succ q =>
    exact List.getElem?_append_left (Nat.mod_lt _ (List.length_pos_iff.mpr hu))

theorem fine_wilf_escape {c : List α} {N p : ℕ} {b : α}
    (hc : c ≠ []) (hp : 0 < p) (hlen : p + c.length ≤ N * c.length)
    (hb : c.head? ≠ some b) : ¬ HasPeriod (pow c N ++ [b]) p := by
  intro hper
  let L := N * c.length
  have hcpos := List.length_pos_iff.mpr hc
  have hL : 0 < L := by dsimp [L]; omega
  have hpL : p < L := by dsimp [L]; omega
  have hpow : HasPeriod (pow c N) p := hper.infix (List.prefix_append _ _).isInfix
  have hg := fine_wilf hpow (hasPeriod_pow c N) (by simp only [length_pow]; omega)
  have hdL : Nat.gcd p c.length ∣ L := (Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _)
  have hd : Nat.gcd p c.length ∣ L - p := Nat.dvd_sub hdL (Nat.gcd_dvd_left _ _)
  have he := hg.eq_of_mod (a := L - p) (b := 0)
    (by simp only [length_pow]; dsimp [L] at *; omega)
    (by simpa only [length_pow] using hL) (by simp [Nat.mod_eq_zero_of_dvd hd])
  have hh := hper (L - p) (by
    simp only [List.length_append, length_pow, List.length_singleton]
    dsimp [L] at *
    omega)
  rw [show L - p + p = L by omega] at hh
  rw [List.getElem?_append_left (by simp only [length_pow]; dsimp [L] at *; omega),
    List.getElem?_append_right (by simp only [length_pow]; rfl)] at hh
  simp only [length_pow, show L - N * c.length = 0 by simp [L], List.getElem?_cons_zero] at hh
  rw [he, getElem?_pow hc (by simpa only [length_pow] using hL), Nat.zero_mod] at hh
  cases c with
  | nil => exact (hc rfl).elim
  | cons a c => exact hb hh

/-- The number of cycle repetitions needed to exceed the prescribed initial length. -/
def cycleCopies (v c : List α) : ℕ := (v.length + c.length + c.length - 1) / c.length

theorem cycleCopies_bounds (v c : List α) (hc : c ≠ []) :
    v.length + c.length ≤ cycleCopies v c * c.length ∧
    cycleCopies v c * c.length < v.length + 2 * c.length := by
  have hp := List.length_pos_iff.mpr hc
  have hrem := Nat.mod_lt (v.length + c.length + c.length - 1) hp
  have hdiv := Nat.mod_add_div (v.length + c.length + c.length - 1) c.length
  rw [Nat.mul_comm c.length] at hdiv
  dsimp [cycleCopies]
  constructor <;> omega

theorem comparison_period {w : List α} {s e : ℕ} (hse : s ≤ e)
    (hp : w.drop e <+: w.drop s) : HasPeriod (w.drop s) (e-s) := by
  apply hasPeriod_iff_list_hasPeriod.mpr
  change w.drop s <+: (w.drop s).take (e-s) ++ w.drop s
  have hd : (w.drop s).drop (e-s) <+: w.drop s := by
    simpa only [List.drop_drop, Nat.add_sub_of_le hse] using hp
  have hh := (List.prefix_append_right_inj ((w.drop s).take (e-s))).mpr hd
  simpa only [List.take_append_drop] using hh

end DeciNSSE.Words
