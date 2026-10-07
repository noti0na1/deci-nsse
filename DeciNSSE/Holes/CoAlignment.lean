import DeciNSSE.Holes.Basic

/-! # Lettered monitors and comparison alignment

Lettered monitors distinguish current cores and letters. A letter map that
introduces no new boundary comparison preserves the hole condition.
-/

set_option autoImplicit false

namespace DeciNSSE.CoAlignment
open DeciNSSE.Holes
open scoped List

section Comparisons
variable {α β : Type*}

/-- A comparison `(s,e)` of `u`: `s < e ≤ |u|` and `u[e:] ⪯ u[s:]`. -/
def IsComp (u : List α) (s e : ℕ) : Prop := s < e ∧ e ≤ u.length ∧ u.drop e <+: u.drop s

/-- One step to the left: for `a < b < |u|`, `u[b:] ⪯ u[a:]` iff the letters agree and
`u[b+1:] ⪯ u[a+1:]`. -/
theorem drop_prefix_iff_succ (u : List α) {a b : ℕ} (hab : a < b) (hb : b < u.length) :
    u.drop b <+: u.drop a ↔ u[b] = u[a] ∧ u.drop (b + 1) <+: u.drop (a + 1) := by
  rw [List.drop_eq_getElem_cons hb, List.drop_eq_getElem_cons (by omega : a < u.length),
    List.cons_prefix_cons]

/-- Letter maps preserve comparisons. -/
theorem IsComp.map (f : α → β) {u : List α} {s e : ℕ} (h : IsComp u s e) :
    IsComp (u.map f) s e := by
  obtain ⟨hse, he, hc⟩ := h
  refine ⟨hse, by simpa using he, ?_⟩
  rw [← List.map_drop, ← List.map_drop]
  exact hc.map f

/-- Collapse. A comparison of `f(u)` that is not a comparison of `u` extends to a
left-maximal comparison `(s+1, e+1)` of `u` whose boundary letters are distinct with
equal `f`-images (the rightmost mismatch). -/
theorem exists_collapse (f : α → β) (u : List α) :
    ∀ k a b, u.length - b = k → a < b → b ≤ u.length →
      (u.map f).drop b <+: (u.map f).drop a → ¬ u.drop b <+: u.drop a →
      ∃ s e, ∃ (hs : s < u.length) (he : e < u.length), s < e ∧
        IsComp u (s + 1) (e + 1) ∧ u[s] ≠ u[e] ∧ f u[s] = f u[e] := by
  intro k
  induction k with
  | zero =>
    intro a b hk hab hb _ hn
    exact absurd (by rw [show b = u.length by omega]; simp) hn
  | succ k ih =>
    intro a b hk hab hb hm hn
    have hb' : b < u.length := by omega
    have hmb : b < (u.map f).length := by simpa using hb'
    rw [drop_prefix_iff_succ (u.map f) hab hmb] at hm
    simp only [List.getElem_map] at hm
    obtain ⟨hfe, hm⟩ := hm
    by_cases hc : u.drop (b + 1) <+: u.drop (a + 1)
    · refine ⟨a, b, by omega, hb', hab, ⟨by omega, by omega, hc⟩, ?_, hfe.symm⟩
      intro hab'
      exact hn ((drop_prefix_iff_succ u hab hb').mpr ⟨hab'.symm, hc⟩)
    · exact ih (a + 1) (b + 1) (by omega) (by omega) (by omega) hm hc

/-- General identification lemma. If a letter map `f` collapses no boundary pair of a
left-maximal comparison of `u`, then `f(u)` has exactly the comparisons of `u`. -/
theorem isComp_map_iff (f : α → β) (u : List α)
    (hf : ∀ s e (hs : s < u.length) (he : e < u.length), s < e →
      IsComp u (s + 1) (e + 1) → f u[s] = f u[e] → u[s] = u[e])
    (s e : ℕ) : IsComp (u.map f) s e ↔ IsComp u s e := by
  refine ⟨fun h => ?_, IsComp.map f⟩
  obtain ⟨hse, he, hc⟩ := h
  have he' : e ≤ u.length := by simpa using he
  refine ⟨hse, he', ?_⟩
  by_contra hn
  obtain ⟨s', e', hs', he'', hlt, hcomp, hne, hfe⟩ :=
    exists_collapse f u _ s e rfl hse he' hc hn
  exact hne (hf s' e' hs' he'' hlt hcomp hfe)

variable [DecidableEq α]

end Comparisons

/-- Labels: `none` is the label `S` of cut 0; `some (c, a)` is the letter `a` read from
core `c`. -/
abbrev Lab (Γ C : Type*) := Option (C × Γ)

/-- A monitor with core transitions, interior and terminal admissions, and a final target. -/
structure Lettered (Γ C : Type*) where
  /-- The initial core. -/
  start : C
  /-- The core transition on a letter. -/
  κ : Γ → C → C
  /-- Admission for comparisons ending before the terminal cut. -/
  Λ : Lab Γ C → Lab Γ C → Prop
  /-- Admission for comparisons ending at the terminal cut. -/
  Λf : Lab Γ C → Lab Γ C → Prop
  /-- The target condition on the final core and letter. -/
  Tf : C → Γ → Prop

namespace Lettered
variable {Γ C : Type*} (D : Lettered Γ C)

/-- The core reader. -/
def coreDFA : DFA Γ C where
  step c a := D.κ a c
  start := D.start
  accept := ∅

/-- The core run: `c_0 = ⋆`, `c_{x+1} = κ(v_x, c_x)`. -/
def core (v : List Γ) (x : ℕ) : C := runPrefix D.coreDFA v x

/-- The label of cut `x`: `L_0 = S`, `L_{x+1} = (c_x, v_x)`. -/
def label (v : List Γ) : ℕ → Lab Γ C
  | 0 => none
  | x + 1 => (v[x]?).map fun a => (D.core v x, a)

theorem label_succ (v : List Γ) {x : ℕ} (hx : x < v.length) :
    D.label v (x + 1) = some (D.core v x, v[x]) := by
  simp [label, List.getElem?_eq_getElem hx]

/-- The final label is a target and no interior or terminal comparison is admitted. -/
def IsHole (v : List Γ) : Prop :=
  (∃ c a, D.label v v.length = some (c, a) ∧ D.Tf c a) ∧
    (∀ s, s < v.length → ¬ D.Λf (D.label v s) (D.label v v.length)) ∧
    (∀ s e, IsComp v s e → e < v.length → ¬ D.Λ (D.label v s) (D.label v e))

theorem IsHole.ne_nil {D : Lettered Γ C} {v : List Γ} (h : D.IsHole v) : v ≠ [] := by
  rintro rfl
  obtain ⟨⟨c, a, hl, -⟩, -⟩ := h
  simp [label] at hl

variable [DecidableEq Γ]

end Lettered

end DeciNSSE.CoAlignment
