import Mathlib.Computability.NFA
import DeciNSSE.Coverage.TerminalCopy

/-! # Finite-monoid cap coverage

Prefix and periodic coverage are expressed through a word morphism into a
finite monoid. Bounded reachability makes coverage of a given word decidable.
-/

namespace DeciNSSE.CapInflation

open Words

open scoped TerminalCopy

variable {H : Type*} [Monoid H]

section Membership
variable {α : Type*}

def PrM (μ : List α →* H) (U : Set H) (w : List α) : Prop :=
  ∃ t : List α, μ (w ++ t) ∈ U

def PeriodCovered (μ : List α →* H) (U : Set H) (w : List α) : Prop :=
  ∃ p, 0 < p ∧ p < w.length ∧
    (∀ i, i + p < w.length → w[i]? = w[i + p]?) ∧ μ (w.take p) ∈ U

def CapCovered (μ : List α →* H) (U : Set H) (w : List α) : Prop :=
  PrM μ U w ∨ PeriodCovered μ U w

def imageDFA (μ : List α →* H) : DFA α H where
  step h a := h * μ [a]
  start := 1
  accept := Set.univ

theorem imageDFA_eval (μ : List α →* H) (w : List α) (h : H) :
    (imageDFA μ).evalFrom h w = h * μ w := by
  induction w generalizing h with
  | nil => change h = h * μ 1; rw [μ.map_one, mul_one]
  | cons a w ih =>
    rw [DFA.evalFrom_cons, ih]
    have hm : μ (a :: w) = μ [a] * μ w := μ.map_mul [a] w
    simp [imageDFA, hm, mul_assoc]

theorem short_image [Fintype H] (μ : List α →* H) (w : List α) :
    ∃ v : List α, v.length < Fintype.card H ∧ μ v = μ w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hs : w.length < Fintype.card H
    · exact ⟨w, hs, rfl⟩
    obtain ⟨q, a, b, c, hw, _, hb, ha, hloop, hc⟩ :=
      (imageDFA μ).evalFrom_split (s := 1) (by omega)
        (show (imageDFA μ).evalFrom 1 w = μ w by simp [imageDFA_eval])
    have he : μ (a ++ c) = μ w := by
      have he := (imageDFA μ).evalFrom_of_append (start := 1) (x := a) (y := c)
      rw [ha, hc, imageDFA_eval, one_mul] at he
      exact he
    have hshort : (a ++ c).length < n := by
      have := List.length_pos_iff.mpr hb
      simp only [hw, List.length_append] at hn
      simp only [List.length_append]
      omega
    obtain ⟨v, hv, he'⟩ := ih _ hshort (a ++ c) rfl
    exact ⟨v, hv, he'.trans he⟩

def imageReach [Fintype α] [DecidableEq H] (μ : List α →* H) (n : ℕ) : Finset H :=
  match n with
  | 0 => {1}
  | n + 1 => {1} ∪ (Finset.univ ×ˢ imageReach μ n).image (fun p => μ [p.1] * p.2)

theorem mem_imageReach [Fintype α] [DecidableEq H] (μ : List α →* H) (n : ℕ) (h : H) :
    h ∈ imageReach μ n ↔ ∃ w : List α, w.length ≤ n ∧ μ w = h := by
  induction n generalizing h with
  | zero =>
    simp only [imageReach, Finset.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨[], rfl, μ.map_one⟩
    · rintro ⟨w, rfl, he⟩; exact he.symm.trans μ.map_one
  | succ n ih =>
    simp only [imageReach, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_product, Finset.mem_univ, true_and, Prod.exists, ih]
    constructor
    · rintro (rfl | ⟨a, h, ⟨w, hw, rfl⟩, rfl⟩)
      · exact ⟨[], by simp, μ.map_one⟩
      · exact ⟨a :: w, by simp; omega, μ.map_mul [a] w⟩
    · rintro ⟨w, hw, rfl⟩
      cases w with
      | nil => exact Or.inl μ.map_one
      | cons a w =>
        exact Or.inr ⟨a, μ w, ⟨w, by simpa using hw, rfl⟩, (μ.map_mul [a] w).symm⟩

def capCoveredB [Fintype α] [DecidableEq α] [Fintype H] [DecidableEq H]
    (μ : List α →* H) (U : Set H) [DecidablePred (· ∈ U)] (w : List α) : Bool :=
  decide (∃ h ∈ imageReach μ (Fintype.card H), μ w * h ∈ U) ||
    (List.range w.length).any (fun p => decide (0 < p ∧ μ (w.take p) ∈ U) &&
      (List.range w.length).all (fun i => decide (i + p < w.length → w[i]? = w[i + p]?)))

theorem capCoveredB_iff [Fintype α] [DecidableEq α] [Fintype H] [DecidableEq H]
    (μ : List α →* H) (U : Set H) [DecidablePred (· ∈ U)] (w : List α) :
    capCoveredB μ U w = true ↔ CapCovered μ U w := by
  have hpr : (∃ h ∈ imageReach μ (Fintype.card H), μ w * h ∈ U) ↔ PrM μ U w := by
    constructor
    · rintro ⟨h, hh, ht⟩
      obtain ⟨t, _, rfl⟩ := (mem_imageReach μ _ _).mp hh
      exact ⟨t, (μ.map_mul w t) ▸ ht⟩
    · rintro ⟨t, ht⟩
      obtain ⟨v, hv, he⟩ := short_image μ t
      refine ⟨μ v, (mem_imageReach μ _ _).mpr ⟨v, hv.le, rfl⟩, ?_⟩
      rw [he, ← μ.map_mul w t]
      exact ht
  simp only [capCoveredB, Bool.or_eq_true, decide_eq_true_eq, hpr,
    List.any_eq_true, List.mem_range, Bool.and_eq_true, List.all_eq_true]
  change (PrM μ U w ∨ _) ↔ PrM μ U w ∨ _
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨p, hpw, ⟨hp, hu⟩, hper⟩
    exact ⟨p, hp, hpw, fun i hi => hper i (by omega) hi, hu⟩
  · rintro ⟨p, hp, hpw, hper, hu⟩
    exact ⟨p, hpw, ⟨hp, hu⟩, fun i _ hi => hper i hi⟩

end Membership

theorem prM_iff (μ : Word →* H) (U : Set H) (w : Word) :
    PrM μ U w ↔ w ∈ Pr (μ ⁻¹' U) := by
  constructor
  · rintro ⟨t, ht⟩; exact ⟨w ++ t, ht, List.prefix_append _ _⟩
  · rintro ⟨v, hv, t, rfl⟩; exact ⟨t, hv⟩

theorem capCovered_iff (μ : Word →* H) (U : Set H) (w : Word) :
    CapCovered μ U w ↔ w ∈ Cap (μ ⁻¹' U) := by
  change (PrM μ U w ∨ PeriodCovered μ U w) ↔ _
  rw [mem_cap_iff, prM_iff]
  rfl

end DeciNSSE.CapInflation
