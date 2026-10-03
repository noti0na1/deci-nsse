import DeciNSSE.Coverage.FullCoverage

/-! # Realised periodic roots

Periodic roots can be restricted to images of words. This normalisation
preserves full coverage and prepares the transition-image formulation.
-/

namespace DeciNSSE.RealizedRoots

open Words CapInflation FullCoverage
open scoped TerminalCopy

variable {H ι : Type*} [Monoid H] [Fintype H] [DecidableEq H]

section Normalization
variable (μ : Word →* H) (V U : ι → Set H)

def realizedRoots (a : H) : Set H :=
  {b | (∃ e, a ∈ V e ∧ b ∈ U e) ∧ b ∈ imageReach μ (Fintype.card H)}

theorem mem_realizedRoots (a : H) (r : Word) :
    μ r ∈ realizedRoots μ V U a ↔ ∃ e, a ∈ V e ∧ μ r ∈ U e := by
  constructor
  · exact And.left
  · intro h
    obtain ⟨v, hv, he⟩ := short_image μ r
    exact ⟨h, (mem_imageReach μ _ _).mpr ⟨v, hv.le, he⟩⟩

theorem realizedRoots_realized (a b : H) (hb : b ∈ realizedRoots μ V U a) :
    ∃ r : Word, μ r = b := by
  obtain ⟨r, _, hr⟩ := (mem_imageReach μ _ _).mp hb.2
  exact ⟨r, hr⟩

theorem fullCovered_realized (VA : Set H) (w : Word) :
    FullCovered μ VA (fun a => {a}) (realizedRoots μ V U) w ↔
      FullCovered μ VA V U w := by
  simp only [FullCovered, capCovered_iff]
  constructor
  · rintro (ha | ⟨a, x, y, hw, hx, r, hr, hp⟩)
    · exact Or.inl ha
    · obtain ⟨e, he, hr⟩ := (mem_realizedRoots μ V U a r).mp hr
      exact Or.inr ⟨e, x, y, hw, (Set.mem_singleton_iff.mp hx).symm ▸ he, r, hr, hp⟩
  · rintro (ha | ⟨e, x, y, hw, hx, r, hr, hp⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨μ x, x, y, hw, rfl, r,
        (mem_realizedRoots μ V U _ r).mpr ⟨e, hx, hr⟩, hp⟩

end Normalization

end DeciNSSE.RealizedRoots
