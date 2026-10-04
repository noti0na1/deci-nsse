import DeciNSSE.Coverage.Periods
import DeciNSSE.Coverage.Dominance

/-! # Algebraic properties of admission

A word morphism, ordinary acceptance and an admission relation satisfy
properties controlling rejected paths and cap roots. These properties imply
that admitted roots occur before rejection and that suitable cycle words
break all admitted periods.
-/

namespace DeciNSSE.DerivedClass
open Words FullCoverage
open scoped TerminalCopy
variable {H : Type*} [Monoid H]

/-- Images whose every right extension is ordinarily accepted. -/
def permanentlyAccepted (VA : Set H) : Set H := {x | ∀ y, x * y ∈ VA}

/--
Algebraic admission properties controlling endpoints, rejection and proper factors of cap roots.
-/
structure DerivedAxioms (μ : Word →* H) (VA : Set H) (D : Set (H × H)) : Prop where
  /-- Equal one-letter extensions have equally accepted predecessor images. -/
  shared : ∀ h g a b, h * μ [a] = g * μ [b] → (h ∈ VA ↔ g ∈ VA)
  /-- Admission depends only on the starting image and the resulting endpoint image. -/
  endpoint : ∀ e h h', e * h = e * h' → ((e, h) ∈ D ↔ (e, h') ∈ D)
  /-- An admitted root starts at an ordinarily accepted image. -/
  entry : ∀ e h, (e, h) ∈ D → e ∈ VA
  /-- Every proper prefix of an admitted root ends at an ordinarily accepted image. -/
  strictCap : ∀ e h f t, (e, h) ∈ D → f * t = h → t ∈ Set.range μ →
    t ≠ 1 → e * f ∈ VA
  /-- A return to acceptance after rejection enters the permanently accepted region. -/
  gap : ∀ e a, e ∉ VA → e * μ [a] ∈ VA → e * μ [a] ∈ permanentlyAccepted VA
  /-- Admission of the identity root implies permanent acceptance. -/
  emptyRoot : ∀ e, (e, 1) ∈ D → e ∈ permanentlyAccepted VA
  /-- Only the empty word has identity image. -/
  identity : ∀ w, μ w = 1 → w = []

theorem covered_iff_root (μ : Word →* H) (VA : Set H) (D : Set (H × H)) (w : Word) :
    FullCovered μ VA (fun h => {h}) (fun e => {h | (e, h) ∈ D}) w ↔
      μ w ∈ VA ∨ ∃ a u r, w = a ++ u ∧ (μ a, μ r) ∈ D ∧ IsPrefixOfPower r u := by
  simp only [FullCovered, CapInflation.capCovered_iff, Cap, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro (hw | ⟨e, a, u, hw, rfl, r, hr, hp⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨a, u, r, hw, hr, hp⟩
  · rintro (hw | ⟨a, u, r, hw, hr, hp⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨μ a, a, u, hw, rfl, r, hr, hp⟩

variable {μ : Word →* H} {VA : Set H} {D : Set (H × H)}

theorem strictCap_word (ax : DerivedAxioms μ VA D) {a f t : Word}
    (hd : (μ a, μ (f ++ t)) ∈ D) (ht : t ≠ []) : μ (a ++ f) ∈ VA := by
  rw [TerminalCopy.map_append]
  exact ax.strictCap _ _ _ _ hd (TerminalCopy.map_append μ f t).symm
    ⟨t, rfl⟩ (fun he => ht (ax.identity t he))

theorem rejected_path (ax : DerivedAxioms μ VA D) {e : H} (he : e ∉ VA)
    (u t : Word) (hw : e * μ (u ++ t) ∉ VA) : e * μ u ∉ VA := by
  induction u generalizing e with
  | nil => simpa only [TerminalCopy.map_nil, mul_one] using he
  | cons a u ih =>
    have hc : μ (a :: (u ++ t)) = μ [a] * μ (u ++ t) := μ.map_mul [a] (u ++ t)
    have hn : e * μ [a] ∉ VA := by
      intro ha
      exact hw (by simpa only [List.cons_append, hc, ← mul_assoc] using
        (ax.gap e a he ha (μ (u ++ t))))
    have hh := ih hn (by simpa only [List.cons_append, hc, ← mul_assoc] using hw)
    simpa only [show μ (a :: u) = μ [a] * μ u from μ.map_mul [a] u, mul_assoc] using hh

theorem rejected_between (ax : DerivedAxioms μ VA D) {v u w : Word}
    (hv : μ v ∉ VA) (hw : μ w ∉ VA) (hvu : v <+: u) (huw : u <+: w) : μ u ∉ VA := by
  obtain ⟨t, rfl⟩ := huw
  obtain ⟨z, rfl⟩ := hvu
  simpa only [TerminalCopy.map_append] using
    rejected_path ax hv z t (by simpa only [TerminalCopy.map_append, mul_assoc] using hw)

theorem admitted_proper_prefix (ax : DerivedAxioms μ VA D) {a r v : Word}
    (hd : (μ a, μ r) ∈ D) (ha : a <+: v) (hv : v <+: a ++ r)
    (hlt : v.length < (a ++ r).length) : μ v ∈ VA := by
  obtain ⟨f, rfl⟩ := ha
  obtain ⟨t, he⟩ := hv
  have hr : r = f ++ t := List.append_cancel_left (by simpa only [List.append_assoc] using he.symm)
  subst r
  exact strictCap_word ax hd (by intro he; simp [he] at hlt)

theorem cap_root_bound (ax : DerivedAxioms μ VA D) {v a u r : Word}
    (hv : μ v ∉ VA) (hw : μ (a ++ u) ∉ VA) (hvw : v <+: a ++ u)
    (hd : (μ a, μ r) ∈ D) (hp : IsPrefixOfPower r u) :
    a.length < v.length ∧ a.length + r.length ≤ v.length := by
  have ha : a.length < v.length := by
    by_contra hn
    have hva : v <+: a := List.prefix_of_prefix_length_le hvw
      (List.prefix_append _ _) (by omega)
    exact rejected_between ax hv hw hva (List.prefix_append _ _) (ax.entry _ _ hd)
  refine ⟨ha, ?_⟩
  by_contra hn
  have hav : a <+: v := List.prefix_of_prefix_length_le
    (List.prefix_append _ _) hvw ha.le
  obtain ⟨k, hk⟩ := hp
  have hvpow : v <+: a ++ pow r k := hvw.trans ((List.prefix_append_right_inj a).mpr hk)
  have hvbase : v <+: a ++ r := by
    cases k with
    | zero =>
      simp only [Words.pow_zero, List.append_nil] at hvpow
      exact hvpow.trans (List.prefix_append _ _)
    | succ k =>
      apply List.prefix_of_prefix_length_le hvpow
        (show a ++ r <+: a ++ pow r (k + 1) by
          simp only [Words.pow_succ, ← List.append_assoc]; exact List.prefix_append _ _)
      simp only [List.length_append]
      omega
  exact hv (admitted_proper_prefix ax hd hav hvbase (by simp only [List.length_append]; omega))

theorem root_prefix_of_power {r u : Word} (hp : IsPrefixOfPower r u)
    (hl : r.length ≤ u.length) : r <+: u := by
  obtain ⟨k, hk⟩ := hp
  cases k with
  | zero =>
    have hu : u = [] := by simpa using hk
    have hr : r = [] := List.eq_nil_of_length_eq_zero (by simpa only [hu, List.length_nil, Nat.le_zero] using hl)
    simp [hr]
  | succ k =>
    exact List.prefix_of_prefix_length_le (List.prefix_append _ _) hk hl

theorem cap_root_in_prefix (ax : DerivedAxioms μ VA D) {v a u r : Word}
    (hv : μ v ∉ VA) (hw : μ (a ++ u) ∉ VA) (hvw : v <+: a ++ u)
    (hd : (μ a, μ r) ∈ D) (hp : IsPrefixOfPower r u) :
    r ≠ [] ∧ a.length < v.length ∧ ∃ t, v = a ++ r ++ t := by
  have hb := cap_root_bound ax hv hw hvw hd hp
  have hn : r ≠ [] := by
    intro hr
    subst r
    have hi := ax.emptyRoot (μ a) (by simpa only [TerminalCopy.map_nil] using hd)
    exact hw (by simpa only [TerminalCopy.map_append] using hi (μ u))
  have hu : r.length ≤ u.length := by
    have hl := hvw.length_le
    simp only [List.length_append] at hl
    omega
  have hbase : a ++ r <+: v := List.prefix_of_prefix_length_le
    ((List.prefix_append_right_inj a).mpr (root_prefix_of_power hp hu)) hvw
    (by simpa only [List.length_append] using hb.2)
  obtain ⟨t, ht⟩ := hbase
  exact ⟨hn, hb.1, t, ht.symm⟩

/-- A long cycle power followed by a different letter excludes every shorter admitted period. -/
theorem fine_wilf_escape {c : Word} {N p : ℕ} {b : Fin 2}
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

/-- The number of cycle repetitions sufficient for the Fine–Wilf period-breaking argument. -/
def cycleCopies (v c : Word) : ℕ := (v.length + c.length + c.length - 1) / c.length

theorem cycleCopies_bounds (v c : Word) (hc : c ≠ []) :
    v.length + c.length ≤ cycleCopies v c * c.length ∧
    cycleCopies v c * c.length < v.length + 2 * c.length := by
  have hp := List.length_pos_iff.mpr hc
  have hrem := Nat.mod_lt (v.length + c.length + c.length - 1) hp
  have hdiv := Nat.mod_add_div (v.length + c.length + c.length - 1) c.length
  rw [Nat.mul_comm c.length] at hdiv
  dsimp [cycleCopies]
  constructor <;> omega

section DecidableAxioms
variable [Fintype H] [DecidableEq H]

theorem mem_imageReach_iff (μ : Word →* H) (h : H) :
    h ∈ CapInflation.imageReach μ (Fintype.card H) ↔ h ∈ Set.range μ := by
  rw [CapInflation.mem_imageReach]
  constructor
  · rintro ⟨w, _, hw⟩; exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, hl, hv⟩ := CapInflation.short_image μ w
    exact ⟨v, hl.le, hv⟩

instance rangeDecidable (μ : Word →* H) : DecidablePred (· ∈ Set.range μ) :=
  fun h => decidable_of_iff (h ∈ CapInflation.imageReach μ (Fintype.card H))
    (mem_imageReach_iff μ h)

end DecidableAxioms

end DeciNSSE.DerivedClass
