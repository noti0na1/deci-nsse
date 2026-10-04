import DeciNSSE.Holes.BoundedDepth
import DeciNSSE.RejectedTail.Image

/-! # From rejected tails to a decision procedure

A bound on rejected-tail length, together with a corresponding bound on
hierarchy depth, reduces hole existence on each side to finite search. The bridge
then decides entailment by combining the two side decisions with satisfiability.
-/

namespace DeciNSSE.Bridge
open Holes ConstructedAxioms RejectedTail LetteredHierarchy

variable {k : ℕ}

/-- Nonempty holes of the image reader with tail bound `B` belong to the class `InL depth 0`. -/
def RejectedTailDepth (ϕ : Constraint k) (x y : V k) (side : Side) (B depth : ℕ) : Prop :=
  ∀ w J, IsReaderHole (imageReader (imageμ ϕ x y side))
      (endpointRelation (imageD ϕ x y side)) (imageVA ϕ x y side)ᶜ w →
    IsFirstRejectedPrefix (imageReader (imageμ ϕ x y side)) (imageVA ϕ x y side)ᶜ w J →
    w.length - J ≤ B → w ≠ [] → InL depth 0 w

/-- Tail and depth bounds reduce hole existence to the empty word or a hole of bounded depth. -/
theorem side_hole_iff_bounded_depth (ϕ : Constraint k) (x y : V k) (side : Side)
    (B depth : ℕ)
    (hB : BoundedRejectedTail (imageReader (imageμ ϕ x y side))
      (endpointRelation (imageD ϕ x y side)) (imageVA ϕ x y side)ᶜ B)
    (hdepth : RejectedTailDepth ϕ x y side B depth) :
    (∃ w, IsReaderHole (monitor ϕ x y side) relation (target ϕ x y side) w) ↔
      IsReaderHole (monitor ϕ x y side) relation (target ϕ x y side) [] ∨
      ∃ w, w ≠ [] ∧ IsReaderHole (monitor ϕ x y side) relation (target ϕ x y side) w ∧
        InL depth 0 w := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨v, J, hv, hJ, hb⟩ := hB ⟨w, (nsse_image_hole_iff w).mpr hw⟩
    by_cases hnil : v = []
    · exact Or.inl (hnil ▸ (nsse_image_hole_iff v).mp hv)
    · exact Or.inr ⟨v, hnil, (nsse_image_hole_iff v).mp hv, hdepth v J hv hJ hb hnil⟩
  · rintro (h | ⟨w, _, h, _⟩)
    · exact ⟨[], h⟩
    · exact ⟨w, h⟩

/-- Decide hole existence on one side using bounds on rejected-tail length and hierarchy depth. -/
def decideSideHolesOfRejectedTail (ϕ : Constraint k) (x y : V k) (side : Side)
    (B depth : ℕ)
    (hB : BoundedRejectedTail (imageReader (imageμ ϕ x y side))
      (endpointRelation (imageD ϕ x y side)) (imageVA ϕ x y side)ᶜ B)
    (hdepth : RejectedTailDepth ϕ x y side B depth) :
    Decidable (∃ w, IsReaderHole (monitor ϕ x y side) relation (target ϕ x y side) w) :=
  decidable_of_iff _ (side_hole_iff_bounded_depth ϕ x y side B depth hB hdepth).symm

/-- Decide entailment using bounds on rejected-tail length and hierarchy depth for both sides. -/
def decideEntailsOfRejectedTail (ϕ : Constraint k) (x y : V k)
    (B depth : Side → ℕ)
    (hB : ∀ side, BoundedRejectedTail (imageReader (imageμ ϕ x y side))
      (endpointRelation (imageD ϕ x y side)) (imageVA ϕ x y side)ᶜ (B side))
    (hdepth : ∀ side, RejectedTailDepth ϕ x y side (B side) (depth side)) :
    Decidable (Entails ϕ x y) := by
  letI := decideSideHolesOfRejectedTail ϕ x y .l (B .l) (depth .l) (hB .l) (hdepth .l)
  letI := decideSideHolesOfRejectedTail ϕ x y .r (B .r) (depth .r) (hB .r) (hdepth .r)
  apply decidable_of_iff (satInfB ϕ = false ∨
    ((¬ ∃ w, IsReaderHole (monitor ϕ x y .l) relation (target ϕ x y .l) w) ∧
     (¬ ∃ w, IsReaderHole (monitor ϕ x y .r) relation (target ϕ x y .r) w)))
  rw [Language.entails_iff_universal', universal_iff_no_holes, universal_iff_no_holes]
end DeciNSSE.Bridge
