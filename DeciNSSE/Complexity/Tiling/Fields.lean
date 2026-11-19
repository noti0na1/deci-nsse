import DeciNSSE.Holes.Hierarchy.Expansion
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Infix

/-! # Comparisons between delimited fields

## Main declarations

- `clear_fields_iff` characterizes the absence of mismatched predecessor
  colors in two fields with a common delimiter and compatible continuations.
-/

namespace DeciNSSE.Complexity.Tiling
open CoAlignment LetteredHierarchy
open scoped List
variable {α : Type*}

/-- The color of a cut is the preceding letter, with `none` as the sentinel at the start of the
field. -/
def cutColor (w : List α) : ℕ → Option α
  | 0 => none
  | j + 1 => w[j]?

/-- A comparison between cuts in two specified fields with different preceding
colors. At cut zero of either field the color is the start sentinel. -/
def mismatch (w : List α) (s e : ℕ) (a b : List α) (skipStart : Bool) : Prop :=
  ∃ i ≤ a.length, ∃ j ≤ b.length, (skipStart = true → 0 < i) ∧
    IsComp w (s + i) (e + j) ∧ cutColor a i ≠ cutColor b j

private def Aligned (a b : List α) (skip : Bool) : Prop :=
  ∀ x y z, x ++ z = a → y ++ z = b → (skip = true → x ≠ []) → x.getLast? = y.getLast?

private theorem aligned_iff (a b : List α) (skip : Bool) :
    Aligned a b skip ↔ if skip then a <:+ b else a = b := by
  classical
  constructor
  · intro clear
    let S := a.tails.toFinset.filter fun z => z <:+ b
    have hn : [] ∈ S := by simp [S, List.mem_tails]
    obtain ⟨z, hz, hm⟩ := Finset.exists_max_image S List.length ⟨_, hn⟩
    obtain ⟨sa, sb⟩ : z <:+ a ∧ z <:+ b := by simpa [S, List.mem_tails] using hz
    obtain ⟨x, hx⟩ := sa
    obtain ⟨y, hy⟩ := sb
    have empty : x = [] := by
      by_contra ne
      have he := clear x y z hx hy (fun _ => ne)
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (by simpa using ne : x.getLast? ≠ none)
      obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp hc
      obtain ⟨r, hr⟩ := List.getLast?_eq_some_iff.mp (he ▸ hc)
      have ha' : c :: z <:+ a := ⟨l, by simpa [hl, List.append_assoc] using hx⟩
      have hb' : c :: z <:+ b := ⟨r, by simpa [hr, List.append_assoc] using hy⟩
      have hz' : c :: z ∈ S := by simpa [S, List.mem_tails] using And.intro ha' hb'
      have := hm _ hz'; simp at this
    subst x
    cases skip with
    | true => simpa using (show a <:+ b by simpa using hx ▸ (show [] ++ z <:+ b from ⟨y,hy⟩))
    | false =>
      have he := clear [] y z hx hy (by simp)
      have ey : y = [] := List.getLast?_eq_none_iff.mp he.symm
      simpa [ey] using hx.symm.trans (ey ▸ hy)
  · cases skip with
    | false =>
      intro he; simp only [Bool.false_eq_true, ite_false] at he
      rintro x y z hx hy _
      exact congrArg _ (List.append_cancel_right ((hx.trans he).trans hy.symm))
    | true =>
      intro he
      obtain ⟨p, hp⟩ : a <:+ b := he
      intro x y z hx hy nonempty
      have hxy : p ++ x = y := List.append_cancel_right (by rw [List.append_assoc, hx, hp, hy])
      rw [← hxy, List.getLast?_append_of_ne_nil _ (nonempty rfl)]

private theorem cutColor_append (p s : List α) : cutColor (p ++ s) p.length = p.getLast? := by
  obtain rfl | ⟨q,a,rfl⟩ := List.eq_nil_or_concat' p
  · rfl
  · simp [cutColor, List.append_assoc]

/-- Clear comparisons authenticate a suffix when the earlier start cut is
excluded, and equality when both starts carry a sentinel. -/
theorem clear_fields_iff {w u v a b tail rest : List α} {d : α}
    (h₁ : w = u ++ (a ++ d :: rest)) (h₂ : w = v ++ (b ++ d :: tail))
    (order : u.length + a.length < v.length) (ha : d ∉ a) (hb : d ∉ b) (ht : tail <+: rest)
    (skip : Bool) :
    (¬ mismatch w u.length v.length a b skip) ↔ if skip then a <:+ b else a = b := by
  rw [← aligned_iff]
  have compare (i j : ℕ) (hi : i ≤ a.length) (hj : j ≤ b.length) :
      IsComp w (u.length + i) (v.length + j) ↔ a.drop i = b.drop j := by
    have hu : w.drop (u.length + i) = a.drop i ++ d :: rest := by
      rw [h₁, List.drop_length_add_append, List.drop_append_of_le_length hi]
    have hv : w.drop (v.length + j) = b.drop j ++ d :: tail := by
      rw [h₂, List.drop_length_add_append, List.drop_append_of_le_length hj]
    have hs : u.length + i < v.length + j := by omega
    have he : v.length + j ≤ w.length := by rw [h₂]; simp; omega
    simp only [IsComp, hs, he, true_and, hu, hv]
    rw [mark_prefix_iff (fun hm => hb (List.mem_of_mem_drop hm))
      (fun hm => ha (List.mem_of_mem_drop hm))]
    simp [ht, eq_comm]
  constructor
  · intro clear x y z hx hy hs
    have hi : x.length ≤ a.length := by rw [← hx]; simp
    have hj : y.length ≤ b.length := by rw [← hy]; simp
    have hc := (compare _ _ hi hj).mpr (by rw [← hx, ← hy]; simp)
    by_contra ne
    apply clear
    refine ⟨x.length, hi, y.length, hj, fun h => List.length_pos_iff.mpr (hs h), hc, ?_⟩
    simpa only [← hx, ← hy, cutColor_append] using ne
  · rintro h ⟨i, hi, j, hj, hs, hc, ne⟩
    have eq := (compare _ _ hi hj).mp hc
    let x := a.take i
    let y := b.take j
    have hx : x ++ a.drop i = a := List.take_append_drop ..
    have hy : y ++ a.drop i = b := by rw [eq]; exact List.take_append_drop ..
    have hxi : x.length = i := by simp [x, hi]
    have hyj : y.length = j := by simp [y, hj]
    have c := h x y _ hx hy (fun h => List.length_pos_iff.mp (hxi.symm ▸ hs h))
    apply ne
    calc
      cutColor a i = x.getLast? := by simpa only [hx, hxi] using cutColor_append x (a.drop i)
      _ = y.getLast? := c
      _ = cutColor b j := by simpa only [hy, hyj] using (cutColor_append y (a.drop i)).symm

end DeciNSSE.Complexity.Tiling
