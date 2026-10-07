import DeciNSSE.Holes.CoreOccurrences
import DeciNSSE.RejectedTail.DepthCount
import DeciNSSE.RejectedTail.ReturnGap

/-! # From rejected tails to hierarchy depth

The return-gap bound limits the duration of equal nonempty supports in the
canonical hierarchy. Counting strict support decreases then bounds depth
by the number of reader states and the rejected-tail length.
-/

section

set_option autoImplicit false
namespace DeciNSSE.RejectedTail
open LetteredHierarchy Supports HierarchyDepth Cores CoreOccurrences

section Geometry
variable {α : Type*} [DecidableEq α] [Inhabited α] {w : List α}

/-- Ordinary cores nest. -/
theorem cores_succ_subset (hw : w ≠ []) (j : ℕ) :
    ordinaryCores w (j+1) ⊆ ordinaryCores w j := by
  intro p hp
  obtain ⟨x,hx,_,hp⟩ := (corePos_succ_iff hw j p).mp hp
  exact ⟨x,by omega,hp⟩

/-- Nesting over arbitrary spans. -/
theorem cores_anti (hw : w ≠ []) {a b : ℕ} (hab : a ≤ b) :
    ordinaryCores w b ⊆ ordinaryCores w a := by
  induction b, hab using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ b hab ih => exact (cores_succ_subset hw b).trans ih

/-- Every nonempty core set has an actual greatest original position. -/
theorem cores_greatest (hw : w ≠ []) (j : ℕ) (hne : (ordinaryCores w j).Nonempty) :
    ∃ f, IsGreatest (ordinaryCores w j) f := by
  have hf : (ordinaryCores w j).Finite := (Set.finite_Iio w.length).subset (by
    rintro p ⟨x,hx,hp⟩
    exact corePos_lt hw j x hx p hp)
  obtain ⟨f,hf,hm⟩ := Set.exists_max_image (ordinaryCores w j) id hf hne
  exact ⟨f,hf,hm⟩

/-- Successor cores are strict earlier occurrences of the terminal suffix. -/
theorem core_occurrence (hw : w ≠ []) {j f p : ℕ}
    (hf : IsGreatest (ordinaryCores w j) f) (hp : p ∈ ordinaryCores w (j+1)) :
    p < f ∧ w.drop f <+: w.drop p := by
  obtain ⟨r,hr,hl,hpre⟩ := (corePos_succ_iff_occurrence hw j p).mp hp
  have he : r = w.drop f := Option.some.inj (hr.symm.trans (rho_at_greatest hw hf))
  subst r
  simp only [List.length_drop] at hl
  exact ⟨by omega,hpre⟩

/-- Each hierarchy step consumes at least one original core position. -/
theorem core_distance (hw : w ≠ []) {a b fa p : ℕ} (hab : a ≤ b)
    (hfa : IsGreatest (ordinaryCores w a) fa) (hp : p ∈ ordinaryCores w b) :
    p + (b-a) ≤ fa := by
  induction b, hab using Nat.le_induction generalizing p with
  | base => simpa using hfa.2 hp
  | succ b hab ih =>
    obtain ⟨f,hf⟩ := cores_greatest hw b ⟨p, cores_succ_subset hw b hp⟩
    have hd := ih hf.1
    have hh := (core_occurrence hw hf hp).1
    omega

/-- Reader support is precisely the state image of ordinary cores. -/
theorem mem_support_iff {Q : Type*} [DecidableEq Q] (M : DFA α Q)
    (R : Q → Q → Prop) (T : Set Q) (hw : w ≠ []) (j : ℕ) (q : Q) :
    q ∈ supp (ofReader M R T) w j ↔
      ∃ p ∈ ordinaryCores w j, M.eval (w.take p) = q := by
  rw [mem_supp_iff_corePos _ hw]
  constructor
  · rintro ⟨x,hx,p,hp,hq⟩; exact ⟨p,⟨x,hx,hp⟩,hq⟩
  · rintro ⟨p,⟨x,hx,hp⟩,hq⟩; exact ⟨x,hx,p,hp,hq⟩
end Geometry

end DeciNSSE.RejectedTail

end

section

set_option autoImplicit false
namespace DeciNSSE.RejectedTail

open Refinement
open LetteredHierarchy Supports HierarchyDepth Cores CoreOccurrences
variable {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q] [DecidableEq Q]
variable (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (hgap : ReturnGap M T)
local notation "E" => ofReader M R T
include R hgap

omit [Fintype Q] in
/-- Equal nonempty supports force a strict return inside the rejected tail. -/
theorem equal_support_gap {w : List α} {J a b fa fb : ℕ}
    (hw : w ≠ []) (hr : M.eval w ∈ T) (hJ : IsFirstRejectedPrefix M T w J)
    (hab : a < b) (hs : supp E w a = supp E w b) (_hne : (supp E w a).Nonempty)
    (hfa : IsGreatest (ordinaryCores w a) fa) (hfb : IsGreatest (ordinaryCores w b) fb) :
    b-a ≤ fa-fb ∧ fa-fb ≤ (w.length-J)-1 := by
  have hd := core_distance hw hab.le hfa hfb.1
  have hmem : (M).eval (w.take fa) ∈ supp E w b := by
    rw [← hs]
    exact (mem_support_iff _ _ _ hw a _).mpr ⟨fa,hfa.1,rfl⟩
  obtain ⟨t,ht,he⟩ := (mem_support_iff _ _ _ hw b _).mp hmem
  have hocc := core_occurrence hw hfa (cores_anti hw (by omega : a+1 ≤ b) ht)
  obtain ⟨i,hi,hp⟩ := hfa.1
  have hlen := corePos_lt hw a i hi fa hp
  have hg := hgap w J _ _ hr hJ hocc.1 (by omega) hocc.2 he
  have ht_le := hfb.2 ht
  exact ⟨by omega,by omega⟩

omit [Fintype Q] in
/-- Inclusive constant-support width, including tails zero and one. -/
theorem equal_support_width {w : List α} {J a b : ℕ}
    (hw : w ≠ []) (hr : M.eval w ∈ T) (hJ : IsFirstRejectedPrefix M T w J)
    (hab : a ≤ b) (hs : supp E w a = supp E w b) (hne : (supp E w a).Nonempty) :
    b+1-a ≤ max 1 (w.length-J) := by
  by_cases he : a = b
  · subst b; omega
  · obtain ⟨q,hq⟩ := hne
    obtain ⟨p,hp,_⟩ := (mem_support_iff _ _ _ hw a q).mp hq
    obtain ⟨fa,hfa⟩ := cores_greatest hw a ⟨p,hp⟩
    obtain ⟨t,ht,_⟩ := (mem_support_iff _ _ _ hw b q).mp (hs ▸ hq)
    obtain ⟨fb,hfb⟩ := cores_greatest hw b ⟨t,ht⟩
    obtain ⟨h1,h2⟩ := equal_support_gap M R T hgap hw hr hJ (by omega) hs ⟨q,hq⟩ hfa hfb
    omega

/-- Any ordinarily rejected nonempty word satisfies the explicit depth bound. -/
theorem rejected_depth {w : List α} {J : ℕ} (hw : w ≠ []) (hr : M.eval w ∈ T)
    (hJ : IsFirstRejectedPrefix M T w J) :
    depth w ≤ 2 * Fintype.card Q * max 1 (w.length-J) - 1 := by
  apply depth_le_of_support_width E hw (by omega)
  intro a b hab _ hs hn
  exact equal_support_width M R T hgap hw hr hJ hab hs hn

end DeciNSSE.RejectedTail

end
