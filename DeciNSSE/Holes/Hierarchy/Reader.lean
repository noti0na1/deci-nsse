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
open DeciNSSE.CoAlignment DeciNSSE.Holes
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
  have hrel (s e : ℕ) (hs : s ≤ w.length) (he : 0 < e) (hen : e ≤ w.length) :
      readerΛ M R ((ofReader M R T).label w s) ((ofReader M R T).label w e) ↔
        R (runPrefix M w s) (runPrefix M w e) := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [Lettered.label_succ _ _ (by omega)]
    change R (stOf M ((ofReader M R T).label w s))
      (stOf M (some ((ofReader M R T).core w e', w[e']))) ↔ _
    rw [← Lettered.label_succ _ _ (by omega), hst s hs, hst _ hen]
  unfold Lettered.IsHole IsReaderHole
  rw [hlab, exists_some_eq_iff]
  refine and_congr (by rw [ofReader_Tf, hfin]) ?_
  constructor
  · rintro ⟨hE, hI⟩ s e hc
    rcases lt_or_eq_of_le hc.2.1 with he | rfl
    · exact fun hr => hI s e hc he ((hrel s e (by have := hc.1; omega)
        (by have := hc.1; omega) hc.2.1).mpr hr)
    · intro hr
      apply hE s hc.1
      change R (stOf M ((ofReader M R T).label w s))
        (stOf M (some (runPrefix M w j, w[j])))
      rwa [hst s hc.1.le, hfin']
  · intro h
    refine ⟨?_, fun s e hc _ hr => h s e hc ((hrel s e (by have := hc.1; omega)
      (by have := hc.1; omega) hc.2.1).mp hr)⟩
    intro s hs hr
    apply h s w.length ⟨hs, le_rfl, by simp⟩
    change R (stOf M ((ofReader M R T).label w s))
      (stOf M (some (runPrefix M w j, w[j]))) at hr
    rwa [hst s hs.le, hfin'] at hr

end Reader

end DeciNSSE.LetteredHierarchy
