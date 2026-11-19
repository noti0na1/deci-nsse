import DeciNSSE.Complexity.Tiling.Tables
import Mathlib.Data.Fintype.BigOperators

/-! # Counting numbered controller states

## Main declarations

- `StoppingTable.ofStates_size` and `StoppingTable.decode_size` count the permanent sink.
- `discover_spec` gives distinctness and preservation of a state invariant under enumeration.
-/

namespace DeciNSSE.Complexity.Tiling
variable {α β σ : Type*}

/-- Numbering a list that already contains the start adds exactly one index for the sink. -/
theorem StoppingTable.ofStates_size [DecidableEq σ] (states : List σ) (initial : σ)
    (go : σ → α → Option σ) (final : σ → Bool)
    (rel : σ → σ → Bool) (hi : final initial = false)
    (hin : initial ∈ states) :
    (ofStates states initial go final rel hi).size = states.length + 1 := by
  change (initial :: states.erase initial).length + 1 = _
  rw [List.length_cons, List.length_erase_of_mem hin]
  have := List.length_pos_of_mem hin
  omega

/-- A decoder with a positive number of phases has one state per table-state and phase pair,
plus the sink. -/
theorem StoppingTable.decode_size (M : StoppingTable α) (phases : ℕ) (hp : 0 < phases)
    (parse : ℕ → β → Option (ℕ ⊕ α)) :
    (M.decode phases parse).size = M.size * phases + 1 := by
  unfold decode
  rw [ofStates_size]
  · simp [List.length_flatMap, List.map_const', Nat.mul_comm]
  · exact List.mem_flatMap.mpr
      ⟨M.start, List.mem_finRange _, List.mem_map.mpr ⟨0, by simpa, rfl⟩⟩

private theorem nodup_eraseDups [DecidableEq σ] (l : List σ) : l.eraseDups.Nodup := by
  have go (l acc : List σ) (h : acc.Nodup) : (List.eraseDupsBy.loop (· == ·) l acc).Nodup := by
    induction l generalizing acc with
    | nil => simpa [List.eraseDupsBy.loop] using h
    | cons x l ih =>
      unfold List.eraseDupsBy.loop
      split
      · exact ih _ h
      · next hx =>
        apply ih
        simp_all [beq_iff_eq]; exact fun hm => hx _ hm rfl
  exact go l [] (by simp)

/-- The discovered list contains the start, has distinct entries, and preserves every invariant
closed under successful transitions. -/
theorem discover_spec [DecidableEq σ] (alphabet : List α)
    (go : σ → α → Option σ) (fuel : ℕ)
    (start : σ) (P : σ → Prop) (hi : P start)
    (step : ∀ s, P s → ∀ a ∈ alphabet, ∀ r, go s a = some r → P r) :
    let xs := discover alphabet go fuel start
    start ∈ xs ∧ xs.Nodup ∧ ∀ s ∈ xs, P s := by
  have run (k) (todo seen : List σ) (ht : todo ⊆ seen) (hs : start ∈ seen)
      (hn : seen.Nodup) (hP : ∀ s ∈ seen, P s) :
      let xs := discover.visit alphabet go k todo seen
      start ∈ xs ∧ xs.Nodup ∧ ∀ s ∈ xs, P s := by
    induction k generalizing todo seen with
    | zero => exact ⟨hs, hn, hP⟩
    | succ k ih =>
      cases todo with
      | nil => exact ⟨hs, hn, hP⟩
      | cons s todo =>
        let fresh := ((alphabet.filterMap (go s)).eraseDups).filter (· ∉ seen)
        change let xs := discover.visit alphabet go k (todo ++ fresh) (fresh ++ seen); _
        apply ih
        · intro q h
          rcases List.mem_append.mp h with h | h
          · exact List.mem_append_right _ (ht (List.mem_cons_of_mem s h))
          · exact List.mem_append_left _ h
        · exact List.mem_append_right _ hs
        · apply List.nodup_append.mpr
          exact ⟨(nodup_eraseDups _).filter _, hn,
            fun x hx y hy he => of_decide_eq_true (List.mem_filter.mp hx).2 (he ▸ hy)⟩
        · intro r hr
          rcases List.mem_append.mp hr with h | h
          · obtain ⟨a, ha, he⟩ :=
              List.mem_filterMap.mp (List.mem_eraseDups.mp (List.mem_filter.mp h).1)
            exact step s (hP s (ht List.mem_cons_self)) a ha r he
          · exact hP r h
  exact run fuel [start] [start] (fun _ h => h) (by simp) (by simp) (by simpa using hi)

/-- Once the processing allowance covers all distinct invariant states, every
successful successor of a discovered state has a number. -/
theorem discover_closed [DecidableEq σ] (alphabet : List α)
    (go : σ → α → Option σ) (fuel : ℕ)
    (start : σ) (P : σ → Prop) (hi : P start)
    (step : ∀ q, P q → ∀ a ∈ alphabet, ∀ r, go q a = some r → P r)
    (bound : ∀ xs : List σ, xs.Nodup → (∀ x ∈ xs, P x) → xs.length ≤ fuel) :
    let xs := discover alphabet go fuel start
    ∀ q ∈ xs, ∀ a ∈ alphabet, ∀ r, go q a = some r → r ∈ xs := by
  have run (k : ℕ) (todo seen : List σ) (sub : todo ⊆ seen) (nd : seen.Nodup)
      (inv : ∀ q ∈ seen, P q) (len : seen.length + k = fuel + todo.length)
      (done : ∀ q ∈ seen, q ∉ todo →
        ∀ a ∈ alphabet, ∀ r, go q a = some r → r ∈ seen) :
      let xs := discover.visit alphabet go k todo seen
      ∀ q ∈ xs, ∀ a ∈ alphabet, ∀ r, go q a = some r → r ∈ xs := by
    induction k generalizing todo seen with
    | zero =>
      have hl := bound seen nd inv
      have he : todo = [] := List.length_eq_zero_iff.mp (by omega)
      exact fun q hq => done q hq (by simp [he])
    | succ k ih =>
      cases todo with
      | nil => exact fun q hq => done q hq (by simp)
      | cons q qs =>
        let fresh := ((alphabet.filterMap (go q)).eraseDups).filter (· ∉ seen)
        have mem (r) : r ∈ fresh ↔ (∃ a ∈ alphabet, go q a = some r) ∧ r ∉ seen := by
          simp [fresh,List.mem_filterMap]
        refine ih (qs ++ fresh) (fresh ++ seen) ?_ ?_ ?_ ?_ ?_
        · intro r h
          rcases List.mem_append.mp h with h | h
          · exact List.mem_append_right _ (sub (List.mem_cons_of_mem q h))
          · exact List.mem_append_left _ h
        · exact List.nodup_append.mpr ⟨(nodup_eraseDups _).filter _,nd,
            fun _ hx _ hy e => ((mem _).mp hx).2 (e ▸ hy)⟩
        · intro r hr
          rcases List.mem_append.mp hr with h | h
          · obtain ⟨a,ha,he⟩ := ((mem _).mp h).1
            exact step q (inv _ (sub List.mem_cons_self)) a ha r he
          · exact inv _ h
        · simp only [List.length_append, List.length_cons] at len ⊢; omega
        · intro r hr notTodo a ha t hgo
          by_cases ht : t ∈ seen
          · exact List.mem_append_right _ ht
          by_cases eq : r = q
          · subst r; exact List.mem_append_left _ ((mem _).mpr ⟨⟨a,ha,hgo⟩,ht⟩)
          · simp only [List.mem_append, not_or] at notTodo
            have hr' := (List.mem_append.mp hr).resolve_left notTodo.2
            exact List.mem_append_right _ (done r hr' (by simp [eq,notTodo.1]) a ha t hgo)
  exact run fuel [start] [start] (fun _ h => h) (by simp) (by simpa using hi)
    (by simp [Nat.add_comm])
    (by simp)

end DeciNSSE.Complexity.Tiling
