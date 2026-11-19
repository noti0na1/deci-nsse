import DeciNSSE.Shortening.Dichotomy
import DeciNSSE.Monitor.Bridge

/-! # Canonical depth at a dead end

## Main declarations

- `reader_deadEnd_depth` charges distinct lower variables to the successive
  greatest ordinary cores, giving depth at most twice the label width plus one.
-/

namespace DeciNSSE.Shortening
open Monitor RejectedTail CoreOccurrences Cores Supports LetteredHierarchy HierarchyDepth
open scoped List
variable {n m : ℕ} {ψ : Constraint n m} {X Y : V m} {w : List (Fin n)}

private theorem top_successor (h : DeadEnd (reader ψ X Y) (target ψ) ((reader ψ X Y).eval w))
    (empty : ∀ a, ((reader ψ X Y).eval (w ++ [a])).U = ∅) (a : Fin n) :
    ∃ z, LowerAt ψ (w ++ [a]) z Y ∧ Lit.eqTop z ∈ ψ := by
  classical
  have hr : ¬ Accept ψ ((reader ψ X Y).eval w) := h.1
  have hready : ¬ Ready ψ ((reader ψ X Y).eval w).U ((reader ψ X Y).eval w).L :=
    fun x => hr (Or.inr (Or.inl x))
  have hb : ((reader ψ X Y).eval w).b = false := Bool.eq_false_iff.mpr (fun x => hr (Or.inl x))
  have hacc : Accept ψ ((reader ψ X Y).eval (w ++ [a])) := by
    rw [DFA.eval_append_singleton]
    exact Classical.not_not.mp (h.2 a)
  have hnext : ((reader ψ X Y).eval (w ++ [a])).b = false := by
    rw [DFA.eval_append_singleton, reader_step]; simp [hb, hready]
  unfold Accept Ready at hacc
  rw [hnext, empty a] at hacc
  simpa only [Bool.false_eq_true, Finset.notMem_empty, false_and, exists_false, false_or,
    and_false, or_false, mem_eval_L, mem_topVars] using hacc

private theorem no_top_prefix (h : (reader ψ X Y).eval w ∈ target ψ)
    {p : List (Fin n)} (hp : p <+: w) {z : V m} (hz : LowerAt ψ p z Y) (ht : Lit.eqTop z ∈ ψ) :
    False := by
  apply (mem_target_iff w).mp h
  exact Or.inl ⟨p.length, hp.length_le, by
    rw [← List.prefix_iff_eq_take.mp hp]
    exact Or.inr (Or.inl ⟨z, hz, ht⟩)⟩

private theorem separating_variable [Inhabited (Fin n)] (hw : w ≠ [])
    (h : DeadEnd (reader ψ X Y) (target ψ) ((reader ψ X Y).eval w))
    (top : ∀ a, ∃ z, LowerAt ψ (w ++ [a]) z Y ∧ Lit.eqTop z ∈ ψ)
    {i f g : ℕ} (hf : IsGreatest (ordinaryCores w i) f)
    (hg : IsGreatest (ordinaryCores w (i + 1)) g) :
    ∃ v, LowerAt ψ (w.take f) v Y ∧
      ∀ j t, i < j → IsGreatest (ordinaryCores w j) t → ¬ LowerAt ψ (w.take t) v Y := by
  obtain ⟨hgf, s, hs⟩ := core_occurrence hw hf hg.1
  have hfl : f < w.length := by
    obtain ⟨x, hx, hfx⟩ := hf.1
    exact corePos_lt hw i x hx f hfx
  cases s with
  | nil =>
    have he := congrArg List.length hs
    simp at he
    omega
  | cons a s =>
    obtain ⟨z, hz, hzT⟩ := top a
    have split : LowerAt ψ (w.take f ++ (w.drop f ++ [a])) z Y := by
      simpa [← List.append_assoc] using hz
    obtain ⟨v, hv, tail⟩ := LowerAt.factor split
    refine ⟨v, hv, ?_⟩
    intro j t hj ht hl
    have pref : w.drop g <+: w.drop t := by
      rcases Nat.eq_or_lt_of_le (show i + 1 ≤ j by omega) with he | he
      · subst j; rw [hg.unique ht]
      · exact (core_occurrence hw hg (cores_anti hw he ht.1)).2
    have prefixAt : w.drop f ++ [a] <+: w.drop t :=
      (show w.drop f ++ [a] <+: w.drop g from
        ⟨s, by simpa [List.append_assoc] using hs⟩).trans pref
    obtain ⟨rest, hrest⟩ := prefixAt
    apply no_top_prefix h.1 (p := w.take t ++ (w.drop f ++ [a])) _ (tail.comp hl) hzT
    exact ⟨rest, by rw [List.append_assoc, hrest, List.take_append_drop]⟩

/-- A nonempty word ending at a dead end has canonical depth at most `2 * m + 1` when every
one-letter continuation has empty upper image. -/
theorem reader_deadEnd_depth [Inhabited (Fin n)] (hw : w ≠ [])
    (h : DeadEnd (reader ψ X Y) (target ψ) ((reader ψ X Y).eval w))
    (empty : ∀ a, ((reader ψ X Y).eval (w ++ [a])).U = ∅) : depth w ≤ 2 * m + 1 := by
  classical
  have absent : ¬ (ordinaryCores w (m + 1)).Nonempty := by
    intro present
    have greatest (i : ℕ) (hi : i ≤ m + 1) : ∃ f, IsGreatest (ordinaryCores w i) f :=
      cores_greatest hw i (present.mono (cores_anti hw hi))
    let f (i : ℕ) := if hi : i ≤ m + 1 then (greatest i hi).choose else 0
    have spec (i) (hi : i ≤ m + 1) : IsGreatest (ordinaryCores w i) (f i) := by
      simpa [f, hi] using (greatest i hi).choose_spec
    have separate (i : Fin (m + 1)) := separating_variable hw h (top_successor h empty)
      (spec i i.isLt.le) (spec (i.val + 1) i.isLt)
    let var (i : Fin (m + 1)) : V m := (separate i).choose
    have distinct {i j : Fin (m + 1)} (hlt : i < j) : var i ≠ var j := by
      intro he
      apply (separate i).choose_spec.2 j (f j) hlt (spec _ j.isLt.le)
      change LowerAt ψ (w.take (f j)) (var i) Y
      rw [he]; exact (separate j).choose_spec.1
    have inj : Function.Injective var := by
      intro i j he
      rcases lt_trichotomy i j with hlt | heq | hgt
      exacts [(distinct hlt he).elim, heq, (distinct hgt he.symm).elim]
    have := Fintype.card_le_of_injective var inj
    simp [V] at this
  let M := reader ψ X Y
  let E := ofReader M (fun _ _ => False) (target ψ)
  have hem : supp E w (m + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨p, hp, _⟩ := (mem_support_iff M (fun _ _ => False) (target ψ) hw _ _).mp hq
    exact absent ⟨p, hp⟩
  have := depth_le_of_empty_support E hw hem
  omega

end DeciNSSE.Shortening
