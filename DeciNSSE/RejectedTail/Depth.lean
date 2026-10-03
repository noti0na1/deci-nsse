import Mathlib.Data.Set.Finite.Lemmas
import DeciNSSE.Holes.CoreOccurrences
import DeciNSSE.RejectedTail.ReturnGap
import DeciNSSE.RejectedTail.Decision
import DeciNSSE.RejectedTail.DepthCount

/-! # Hierarchy depth from the rejected tail

Equal nonempty supports give a comparison between equal monitor states.
The return-gap bound limits such supports to max(1, r) levels, where r is
the rejected-tail length. With N monitor states the canonical depth is
at most 2N·max(1, r) − 1, supplying the depth bound for finite search.
-/

namespace DeciNSSE.RejectedTail
open LetteredHierarchy Supports HierarchyDepth Cores CoreOccurrences Words ConstructedAxioms

section Geometry
variable {α : Type*} [DecidableEq α] [Inhabited α] {w : List α}

/-- Ordinary original positions can only disappear on passing to the next hierarchy level. -/
theorem cores_succ_subset (hw : w ≠ []) (j : ℕ) :
    ordinaryCores w (j+1) ⊆ ordinaryCores w j := by
  intro p hp
  obtain ⟨x,hx,_,hp⟩ := (corePos_succ_iff hw j p).mp hp
  exact ⟨x,by omega,hp⟩

/-- The sets of ordinary core positions decrease with hierarchy level. -/
theorem cores_anti (hw : w ≠ []) {a b : ℕ} (hab : a ≤ b) :
    ordinaryCores w b ⊆ ordinaryCores w a := by
  induction b, hab using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ b hab ih => exact (cores_succ_subset hw b).trans ih

/-- Every nonempty set of ordinary core positions has a greatest position. -/
theorem cores_greatest (hw : w ≠ []) (j : ℕ) (hne : (ordinaryCores w j).Nonempty) :
    ∃ f, IsGreatest (ordinaryCores w j) f := by
  have hf : (ordinaryCores w j).Finite := (Set.finite_Iio w.length).subset (by
    rintro p ⟨x,hx,hp⟩
    exact corePos_lt hw j x hx p hp)
  obtain ⟨f,hf,hm⟩ := Set.exists_max_image (ordinaryCores w j) id hf hne
  exact ⟨f,hf,hm⟩

/-- Each ordinary core position begins with the suffix at the greatest such position. -/
theorem core_occurrence (hw : w ≠ []) {j f p : ℕ}
    (hf : IsGreatest (ordinaryCores w j) f) (hp : p ∈ ordinaryCores w (j+1)) :
    p < f ∧ w.drop f <+: w.drop p := by
  obtain ⟨r,hr,hl,hpre⟩ := (corePos_succ_iff_occurrence hw j p).mp hp
  have he : r = w.drop f := Option.some.inj (hr.symm.trans (rho_at_greatest hw hf))
  subst r
  simp only [List.length_drop] at hl
  exact ⟨by omega,hpre⟩

/-- Retained ordinary positions are separated by at least the number of intervening levels. -/
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

/-- Support membership is witnessed by an original reader state at an ordinary core position. -/
theorem mem_support_iff {Q : Type*} [DecidableEq Q] (M : DFA α Q)
    (R : Q → Q → Prop) (T : Set Q) (hw : w ≠ []) (j : ℕ) (q : Q) :
    q ∈ supp (ofReader M R T) w j ↔
      ∃ p ∈ ordinaryCores w j, M.eval (w.take p) = q := by
  rw [mem_supp_iff_corePos _ hw]
  constructor
  · rintro ⟨x,hx,p,hp,hq⟩; exact ⟨p,⟨x,hx,hp⟩,hq⟩
  · rintro ⟨p,⟨x,hx,hp⟩,hq⟩; exact ⟨x,hx,p,hp,hq⟩
end Geometry

section NSSE
variable {k : ℕ} {ϕ : Constraint k} {x y : V k} {side : Side}
local notation "M" => Bridge.monitor ϕ x y side
local notation "E" => ofReader M Bridge.relation (Bridge.target ϕ x y side)
local notation "ν" => imageμ ϕ x y side
local notation "VA" => imageVA ϕ x y side

/-- Equal supports yield a state repetition whose level distance is bounded by the return gap. -/
theorem equal_support_gap {w : Word} {J a b fa fb : ℕ}
    (hw : w ≠ []) (hr : ν w ∉ VA) (hJ : IsFirstCut (imageReader ν) VAᶜ w J)
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
  have hgap := literal_return_gap hr hJ hocc.1 (by omega) hocc.2 he
  have ht_le := hfb.2 ht
  exact ⟨by omega,by omega⟩

/--
Equal nonempty supports persist for at most `max 1 r` levels when the rejected tail has length
`r`.
-/
theorem equal_support_width {w : Word} {J a b : ℕ}
    (hw : w ≠ []) (hr : ν w ∉ VA) (hJ : IsFirstCut (imageReader ν) VAᶜ w J)
    (hab : a ≤ b) (hs : supp E w a = supp E w b) (hne : (supp E w a).Nonempty) :
    b+1-a ≤ max 1 (w.length-J) := by
  by_cases he : a = b
  · subst b; omega
  · obtain ⟨q,hq⟩ := hne
    obtain ⟨p,hp,_⟩ := (mem_support_iff _ _ _ hw a q).mp hq
    obtain ⟨fa,hfa⟩ := cores_greatest hw a ⟨p,hp⟩
    obtain ⟨t,ht,_⟩ := (mem_support_iff _ _ _ hw b q).mp (hs ▸ hq)
    obtain ⟨fb,hfb⟩ := cores_greatest hw b ⟨t,ht⟩
    obtain ⟨h1,h2⟩ := equal_support_gap hw hr hJ (by omega) hs ⟨q,hq⟩ hfa hfb
    omega

/-- A rejected word has canonical depth at most `2N·max(1, r) − 1`. -/
theorem rejected_depth {w : Word} {J : ℕ} (hw : w ≠ []) (hr : ν w ∉ VA)
    (hJ : IsFirstCut (imageReader ν) VAᶜ w J) :
    depth w ≤ 2 * Fintype.card (Bridge.State ϕ x y side) * max 1 (w.length-J) - 1 := by
  apply depth_le_of_support_width E hw (by omega)
  intro a b hab _ hs hn
  exact equal_support_width hw hr hJ hab hs hn

/-- A bound on rejected-tail length supplies the depth bound needed for finite hole search. -/
theorem rejectedTailDepth (ϕ : Constraint k) (x y : V k) (side : Side) (B : ℕ) :
    Bridge.RejectedTailDepth ϕ x y side B
      (2 * Fintype.card (Bridge.State ϕ x y side) * max 1 B - 1) := by
  intro w J hh hJ hb hw
  have hr : imageμ ϕ x y side w ∉ imageVA ϕ x y side := by
    simpa only [imageReader_eval, Set.mem_compl_iff] using ((hole_iff_cuts _ _ _ _).mp hh).1
  refine ⟨depth w, (rejected_depth hw hr hJ).trans ?_, Or.inl (isUnary_depth w)⟩
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (max_le_max_left 1 hb)) 1
end NSSE
end DeciNSSE.RejectedTail
