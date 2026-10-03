import DeciNSSE.Coverage.FullCoverage

/-! # Coverage pairs and dominance

Prefix extensions and proper periods determine pairs of monoid images.
Containment of these pairs defines dominance and expresses full coverage
as the existence of an admitted pair.
-/

namespace DeciNSSE.Dominance

open Words FullCoverage
open scoped TerminalCopy

variable {H : Type*} [Monoid H]

def CovPr (μ : Word →* H) (w : Word) : Set (H × H) :=
  {q | ∃ s, s ≤ w.length ∧ ∃ t ∈ Set.range μ,
    q = (μ (w.take s), μ (w.drop s) * t)}

def CovPer (μ : Word →* H) (w : Word) : Set (H × H) :=
  {q | ∃ s p, s < w.length ∧ 0 < p ∧ p < w.length - s ∧
    HasPeriod (w.drop s) p ∧ q = (μ (w.take s), μ ((w.drop s).take p))}

def Cov (μ : Word →* H) (w : Word) : Set (H × H) := CovPr μ w ∪ CovPer μ w

def Dominates (μ : Word →* H) (v w : Word) : Prop :=
  μ v = μ w ∧ Cov μ v ⊆ Cov μ w

theorem mem_covPr_iff (μ : Word →* H) (w : Word) (e h : H) :
    (e, h) ∈ CovPr μ w ↔
      ∃ a b t : Word, w = a ++ b ∧ e = μ a ∧ h = μ (b ++ t) := by
  constructor
  · rintro ⟨s, _, _, ⟨t, rfl⟩, he⟩
    exact ⟨w.take s, w.drop s, t, (List.take_append_drop s w).symm,
      congrArg Prod.fst he, (congrArg Prod.snd he).trans (μ.map_mul _ _).symm⟩
  · rintro ⟨a, b, t, rfl, rfl, rfl⟩
    exact ⟨a.length, by simp, μ t, ⟨t, rfl⟩, by simp [TerminalCopy.map_append]⟩

theorem fullCovered_iff_cov (μ : Word →* H) (VA : Set H) (U : H → Set H) (w : Word) :
    FullCovered μ VA (fun h => {h}) U w ↔
      μ w ∈ VA ∨ ∃ e h, (e, h) ∈ Cov μ w ∧ h ∈ U e := by
  constructor
  · rintro (ha | ⟨e, a, b, rfl, he, hb⟩)
    · exact Or.inl ha
    · have he' : μ a = e := he
      subst e
      rcases hb with ⟨t, ht⟩ | ⟨p, hp, hpb, hper, ht⟩
      · exact Or.inr ⟨μ a, μ (b ++ t), Or.inl
          ((mem_covPr_iff μ _ _ _).mpr ⟨a, b, t, rfl, rfl, rfl⟩), ht⟩
      · refine Or.inr ⟨μ a, μ (b.take p), Or.inr ⟨a.length, p, ?_⟩, ht⟩
        simpa only [List.length_append, List.take_left, List.drop_left,
          Nat.add_sub_cancel_left] using
          (show a.length < a.length + b.length ∧ 0 < p ∧ p < b.length ∧
            HasPeriod b p ∧ (μ a, μ (b.take p)) = (μ a, μ (b.take p)) from
            ⟨by omega, hp, hpb, hper, rfl⟩)
  · rintro (ha | ⟨e, h, hp | hp, hh⟩)
    · exact Or.inl ha
    · obtain ⟨a, b, t, hw, rfl, rfl⟩ := (mem_covPr_iff μ _ _ _).mp hp
      exact Or.inr ⟨μ a, a, b, hw, rfl, Or.inl ⟨t, hh⟩⟩
    · obtain ⟨s, p, _, hp, hlen, hper, he⟩ := hp
      have he' := Prod.mk.inj he
      rcases he' with ⟨rfl, rfl⟩
      exact Or.inr ⟨μ (w.take s), w.take s, w.drop s,
        (List.take_append_drop s w).symm, rfl,
        Or.inr ⟨p, hp, by simpa using hlen, hper, hh⟩⟩

theorem dominates_refl (μ : Word →* H) (w : Word) : Dominates μ w w :=
  ⟨rfl, Set.Subset.refl _⟩

end DeciNSSE.Dominance
