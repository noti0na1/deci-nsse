import DeciNSSE.Holes.Hierarchy.Derived

/-! # Lettered monitors of readers

A reader `(M, R, T)` is the lettered monitor `𝔇_0 = ofReader M R T` over its
own states: a label stands for the state reached after it, both admissions are
`R` on these states, and the target condition is `T`. Its holes are the
nonempty reader holes.

## Main declarations

- `stOf`, `readerΛ`, `ofReader`: the lettered monitor of a reader.
- `isHole_ofReader_iff`: its holes are the nonempty reader holes.

The declarations are in the namespace `DeciNSSE.LetteredHierarchy`.
-/

namespace DeciNSSE.LetteredHierarchy
open DeciNSSE.CoAlignment DeciNSSE.Desubstitution DeciNSSE.Holes
open scoped List

section Reader
universe u v
variable {α : Type u} {Q : Type v}

/-- The state of a label: `st(S) = q0`, `st(c, a) = δ(c, a)`. -/
def stOf (M : DFA α Q) : Lab α Q → Q
  | none => M.start
  | some (c, a) => M.step c a

/-- `Λ(L, L') = Λ^f(L, L') = [(st L, st L') ∈ R]` for `L' ≠ S` (false if `L' = S`). -/
def readerΛ (M : DFA α Q) (R : Q → Q → Prop) : Lab α Q → Lab α Q → Prop
  | _, none => False
  | L, some p => R (stOf M L) (stOf M (some p))

/-- `𝔇_0` of a reader `(M, R, T)`: `Γ = α`, `C = Q`, `⋆ = q0`, `κ(a, c) = δ(c, a)`,
`Λ = Λ^f` as above, `Tf(c, a) = [δ(c, a) ∈ T]`. -/
def ofReader (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) : Lettered α Q where
  start := M.start
  κ a c := M.step c a
  Λ := readerΛ M R
  Λf := readerΛ M R
  Tf c a := M.step c a ∈ T

/-- The interior admission of `ofReader M R T`. -/
@[simp] theorem ofReader_Λ (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) :
    (ofReader M R T).Λ = readerΛ M R := rfl
/-- The terminal admission of `ofReader M R T`. -/
@[simp] theorem ofReader_Λf (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) :
    (ofReader M R T).Λf = readerΛ M R := rfl
/-- The target condition of `ofReader M R T`. -/
@[simp] theorem ofReader_Tf (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (c : Q) (a : α) :
    (ofReader M R T).Tf c a = (M.step c a ∈ T) := rfl

/-- The core run of `ofReader M R T` is the run of `M`. -/
theorem core_ofReader (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) (x : ℕ) :
    (ofReader M R T).core w x = runPrefix M w x := rfl

/-- The state of the label of cut `x` is the state after `x` letters. -/
theorem stOf_label (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) :
    ∀ x ≤ w.length, stOf M ((ofReader M R T).label w x) = runPrefix M w x
  | 0, _ => rfl
  | x + 1, hx => by
      rw [Lettered.label_succ _ _ (by omega), stOf, core_ofReader, runPrefix, runPrefix,
        List.take_succ_eq_append_getElem (by omega), DFA.eval_append_singleton]

/-- A nonempty word is a hole of `ofReader M R T` iff it is a reader hole of `(M, R, T)`. -/
theorem isHole_ofReader_iff (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) {w : List α}
    (hw : w ≠ []) : (ofReader M R T).IsHole w ↔ IsReaderHole M R T w := by
  obtain ⟨j, hlen⟩ : ∃ j, w.length = j + 1 :=
    ⟨w.length - 1, by have := List.length_pos_iff.mpr hw; omega⟩
  have hst := stOf_label M R T w
  have hlab : (ofReader M R T).label w w.length = some (runPrefix M w j, w[j]) := by
    rw [← core_ofReader M R T]; simp only [hlen]; exact Lettered.label_succ _ w (by omega)
  have hfin : M.step (runPrefix M w j) w[j] = runPrefix M w w.length := by
    have := hst _ le_rfl
    rw [hlab] at this
    exact this
  have hfin' : stOf M (some (runPrefix M w j, w[j])) = runPrefix M w w.length := hfin
  rw [isReaderHole_iff_split]
  unfold Lettered.IsHole
  rw [hlab, exists_some_eq_iff]
  refine and_congr (by rw [ofReader_Tf, hfin]) (and_congr ?_ ?_)
  · constructor
    · rintro h ⟨p, ⟨i, hi, hp⟩, hr⟩
      refine h i hi ?_
      rw [ofReader_Λf]
      show R (stOf M ((ofReader M R T).label w i)) (stOf M (some (runPrefix M w j, w[j])))
      rw [hst i hi.le, hfin']
      have : runPrefix M w i = p := hp
      rw [this]; exact hr
    · intro h s hs hr
      rw [ofReader_Λf] at hr
      change R (stOf M ((ofReader M R T).label w s)) (stOf M (some (runPrefix M w j, w[j]))) at hr
      rw [hst s hs.le, hfin'] at hr
      exact h ⟨_, ⟨s, hs, rfl⟩, hr⟩
  · constructor
    · intro h s e hse he hc hr
      refine h s e ⟨hse, he.le, hc⟩ he ?_
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      rw [ofReader_Λ, Lettered.label_succ _ _ (by omega)]
      show R (stOf M ((ofReader M R T).label w s))
        (stOf M (some ((ofReader M R T).core w e', w[e'])))
      rw [← Lettered.label_succ _ _ (by omega), hst s (by omega), hst _ (by omega)]
      exact hr
    · intro h s e hc he hr
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by have := hc.1; omega⟩
      rw [ofReader_Λ, Lettered.label_succ _ _ (by omega)] at hr
      change R (stOf M ((ofReader M R T).label w s))
        (stOf M (some ((ofReader M R T).core w e', w[e']))) at hr
      rw [← Lettered.label_succ _ _ (by omega), hst s (by have := hc.1; omega),
        hst _ (by omega)] at hr
      exact h s (e' + 1) hc.1 he hc.2.2 hr

end Reader

end DeciNSSE.LetteredHierarchy
