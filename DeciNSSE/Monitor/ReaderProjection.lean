import DeciNSSE.Monitor.ConstructedAxioms
import DeciNSSE.Monitor.Transport

/-! # Projection to variable readers

A transition image determines two sets of reachable variables. Admission
depends only on their intersections, so coverage pairs project to these
smaller readers without changing accepted words.
-/

namespace DeciNSSE.ReaderProjection
open Words Dominance ConstructedAxioms
open scoped TerminalCopy

/-- Apply a reader map to both components of a pair of monoid images. -/
def ProjectPair {H S : Type*} [Monoid H]
    (f : H → S) (q : H × H) : S × S :=
  (f q.1, f (q.1 * q.2))

theorem project_covPer {H S : Type*} [Monoid H]
    (ν : Word →* H) (f : H → S) (w : Word) :
    ProjectPair f '' CovPer ν w =
      {AB | ∃ s p, 0 < p ∧ p < w.length - s ∧
        HasPeriod (w.drop s) p ∧
        AB = (f (ν (w.take s)), f (ν (w.take (s + p))))} := by
  ext AB
  constructor
  · rintro ⟨_, ⟨s, p, _, hp, hl, hper, rfl⟩, rfl⟩
    refine ⟨s, p, hp, hl, hper, ?_⟩
    simp only [ProjectPair, Transport.prefix_product]
  · rintro ⟨s, p, hp, hl, hper, rfl⟩
    refine ⟨(ν (w.take s), ν ((w.drop s).take p)),
      ⟨s, p, by omega, hp, hl, hper, rfl⟩, ?_⟩
    simp only [ProjectPair, Transport.prefix_product]

theorem project_covPr {H S : Type*} [Monoid H]
    (ν : Word →* H) (f : H → S) (w : Word) :
    ProjectPair f '' CovPr ν w =
      {AB | ∃ a b t : Word, w = a ++ b ∧
        AB = (f (ν a), f (ν (w ++ t)))} := by
  ext AB
  constructor
  · rintro ⟨⟨e, h⟩, hc, rfl⟩
    obtain ⟨a, b, t, rfl, rfl, rfl⟩ := (mem_covPr_iff ν w e h).mp hc
    refine ⟨a, b, t, rfl, ?_⟩
    simp only [ProjectPair, TerminalCopy.map_append, mul_assoc]
  · rintro ⟨a, b, t, rfl, rfl⟩
    refine ⟨(ν a, ν (b ++ t)),
      (mem_covPr_iff ν _ _ _).mpr ⟨a, b, t, rfl, rfl, rfl⟩, ?_⟩
    simp only [ProjectPair, TerminalCopy.map_append, mul_assoc]

theorem project_covPr_eq_prod {H S : Type*} [Monoid H]
    (ν : Word →* H) (f : H → S) (w : Word) :
    ProjectPair f '' CovPr ν w =
      Set.prod {A | ∃ s, s ≤ w.length ∧ A = f (ν (w.take s))}
        {B | ∃ t : Word, B = f (ν (w ++ t))} := by
  rw [project_covPr]
  ext ⟨A, B⟩
  constructor
  · rintro ⟨a, b, t, rfl, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨⟨a.length, by simp, by simp⟩, ⟨t, rfl⟩⟩
  · rintro ⟨⟨s, _, rfl⟩, ⟨t, rfl⟩⟩
    exact ⟨w.take s, w.drop s, t, (List.take_append_drop s w).symm, rfl⟩

section Constructed
variable {k : ℕ} {ϕ : Constraint k} {x y : V k} {d : Side}

/-- The upper and lower sets of variables reachable through a transition image. -/
def reader (h : Image ϕ x y d) : Set (V k) × Set (V k) :=
  ({b | P h.val x b}, {b | Q h.val y b})

/--
Left-side admission by intersection of the first reader’s lower and second reader’s upper sets.
-/
def Adm (A B : Set (V k) × Set (V k)) : Prop := (A.2 ∩ B.1).Nonempty

/--
Right-side admission by intersection of the first reader’s upper and second reader’s lower sets.
-/
def AdmRight (A B : Set (V k) × Set (V k)) : Prop := (A.1 ∩ B.2).Nonempty

/-- Choose the reader intersection appropriate to the side of the comparison. -/
def SideAdm (d : Side) (A B : Set (V k) × Set (V k)) : Prop :=
  match d with
  | .l => Adm A B
  | .r => AdmRight A B

/-- The pairs of readers obtained by projecting coverage pairs of a word. -/
def Xi (ϕ : Constraint k) (x y : V k) (d : Side) (w : Word) :
    Set ((Set (V k) × Set (V k)) × (Set (V k) × Set (V k))) :=
  ProjectPair reader '' Cov (imageμ ϕ x y d) w

theorem pair_admitted_iff_adm_left (e h : Image ϕ x y .l) :
    (e, h) ∈ imageD ϕ x y .l ↔ Adm (reader e) (reader (e * h)) := by
  change (e.val, h.val) ∈ D ϕ x y .l ↔ ∃ b, Q e.val y b ∧ P (e.val * h.val) x b
  rw [endpoint_left_image e.property h.property]
  exact exists_congr fun _ => and_comm

theorem pair_admitted_iff_adm_right (e h : Image ϕ x y .r) :
    (e, h) ∈ imageD ϕ x y .r ↔ AdmRight (reader e) (reader (e * h)) := by
  exact endpoint_right_image e.property h.property

theorem pair_admitted_iff_adm (e h : Image ϕ x y d) :
    (e, h) ∈ imageD ϕ x y d ↔ SideAdm d (reader e) (reader (e * h)) := by
  cases d
  · exact pair_admitted_iff_adm_left e h
  · exact pair_admitted_iff_adm_right e h

theorem cov_admitted_iff_adm (w : Word) :
    (Cov (imageμ ϕ x y d) w ∩ imageD ϕ x y d).Nonempty ↔
      (Xi ϕ x y d w ∩ {AB | SideAdm d AB.1 AB.2}).Nonempty := by
  constructor
  · rintro ⟨⟨e, h⟩, hc, hd⟩
    exact ⟨ProjectPair reader (e, h), ⟨(e, h), hc, rfl⟩,
      (pair_admitted_iff_adm e h).mp hd⟩
  · rintro ⟨_, ⟨⟨e, h⟩, hc, rfl⟩, hd⟩
    exact ⟨(e, h), hc, (pair_admitted_iff_adm e h).mpr hd⟩

theorem mem_lang_iff_proj (w : Word) :
    w ∈ (construct ϕ x y d).Lang ↔
      imageμ ϕ x y d w ∈ imageVA ϕ x y d ∨
      (Xi ϕ x y d w ∩ {AB | SideAdm d AB.1 AB.2}).Nonempty := by
  rw [mem_lang_iff_image_fullCovered, fullCovered_iff_cov, ← cov_admitted_iff_adm]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨e, h, hc, hd⟩
    exact ⟨(e, h), hc, hd⟩
  · rintro ⟨⟨e, h⟩, hc, hd⟩
    exact ⟨e, h, hc, hd⟩

end Constructed

end DeciNSSE.ReaderProjection
