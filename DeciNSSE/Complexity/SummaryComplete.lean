import DeciNSSE.Complexity.SummaryGraph
import DeciNSSE.Holes.ElementaryBound

/-! # Completeness of the summary search

A hole of depth at most `d` can be replaced by a hole `v` of the same depth whose
canonical dictionaries have at most `dictionaryBound N d` letters below the top.
The search follows the canonical hierarchy of `v`. At level `j` it holds a table
over the letters of a word `x` with an injective map `φ` from `x` onto the level-`j`
word of `v`, and the table agrees with the level-`j` monitor of the tower along `φ`.
To reach level `j + 1`, the search takes the marker letter, numbers the distinct
blocks of the next level, lifts them to words over the table's letters, and reads
their convolution column by column. The final summary declares the blocks pairwise
distinct, and the derived table agrees with the next monitor along the numbering.
At the first unary level, the lifted word is unary and is a hole of the table, so
the configuration accepts.

## Main declarations

- `Summary.reaches_columns`: reading a valid column word that avoids the marker.
- `Summary.LevelReached`: the invariant at level `j` of the canonical hierarchy.
- `Summary.summarySearch_complete`: a hole of depth at most `d` makes the search
  succeed when `g` is at least the dictionary bound.
-/

set_option autoImplicit false

namespace DeciNSSE.Complexity.Summary
open CoAlignment LetteredHierarchy BoundedDepth Packets HierarchyDepth NormalForm
  ElementaryBound
open scoped List

universe u

/-- A word whose letters have preimages in `S` is the image of a word over `S`. -/
theorem exists_map_eq {β γ : Type*} {f : β → γ} {S : List β} :
    ∀ {u : List γ}, (∀ y ∈ u, ∃ b ∈ S, f b = y) → ∃ x : List β, x.map f = u ∧ ∀ b ∈ x, b ∈ S
  | [], _ => ⟨[], rfl, by simp⟩
  | y :: u, h => by
    obtain ⟨b, hb, rfl⟩ := h y List.mem_cons_self
    obtain ⟨x, hx, hxS⟩ := exists_map_eq fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact ⟨b :: x, by rw [List.map_cons, hx], by simpa [hb] using hxS⟩

section Columns
variable {Q : Type u} [Fintype Q] [DecidableEq Q] {n d g : ℕ} {j : Fin (d + 1)}
  {h₀ : Fin (max n g + 1)} {T : Table (Fin h₀) (Cores Q j)} {ℓ : Fin h₀} {h : Fin (g + 1)}

/-- Reading a valid column word that avoids the marker, one column at a time. The
configuration stores the summary of the columns read and the tracks that have started. -/
theorem reaches_columns (p : List (Fin h → Option (Fin h₀))) :
    ∀ w : List (Fin h → Option (Fin h₀)), Valid (p ++ w) → (∀ col ∈ w, ∀ a, col a ≠ some ℓ) →
      Relation.ReflTransGen (fun a b => b ∈ Config.next a)
        (⟨j, h₀, T, some ⟨ℓ, h, p.foldl (Summ.step T ℓ) (Summ.start T ℓ h), started p⟩⟩ :
          Config Q n d g)
        ⟨j, h₀, T, some ⟨ℓ, h, (p ++ w).foldl (Summ.step T ℓ) (Summ.start T ℓ h),
          started (p ++ w)⟩⟩
  | [], _, _ => by rw [List.append_nil]
  | col :: w, hw, hℓ => by
    rw [List.append_cons] at hw ⊢
    have hv : Valid (p ++ [col]) := hw.sublist (List.sublist_append_left _ _)
    have hc : ColOK ℓ (started p) col := fun a =>
      ⟨hℓ col List.mem_cons_self a,
        (valid_snoc_iff (hv.sublist (List.sublist_append_left _ _)) col).mp hv a⟩
    have h1 := mem_next_iff.mpr (Step.column (j := j) (h₀ := h₀) (T := T) (ℓ := ℓ) (h := h)
      (s := p.foldl (Summ.step T ℓ) (Summ.start T ℓ h)) col hc)
    rw [show Summ.step T ℓ (p.foldl (Summ.step T ℓ) (Summ.start T ℓ h)) col =
        (p ++ [col]).foldl (Summ.step T ℓ) (Summ.start T ℓ h) by simp,
      show (fun a => started p a || (col a).isSome) = started (p ++ [col]) from
        funext fun a => (started_snoc p col a).symm] at h1
    exact .head h1 (reaches_columns (p ++ [col]) w hw
      fun c hc => hℓ c (List.mem_cons_of_mem _ hc))

end Columns

section Levels
variable {Q : Type u} [Fintype Q] [DecidableEq Q] {n : ℕ} [NeZero n]
  (T₀ : Table (Fin n) Q) (d g : ℕ) (v : List (Fin n))

/-- Level `j` of the canonical hierarchy of `v` is reached: a configuration at level `j`
without a derivation is reachable, and its table agrees with the level-`j` monitor of the
tower along a map `φ` that carries a word `x` over the table's letters to `hierOf v j`. -/
def LevelReached (j : ℕ) (hj : j < d + 1) : Prop :=
  ∃ (h₀ : Fin (max n g + 1)) (T : Table (Fin h₀) (Cores Q j)) (φ : Fin h₀ → Alph (Fin n) j)
    (x E : List (Fin h₀)),
    Relation.ReflTransGen (fun a b => b ∈ Config.next a) (Config.init T₀ : Config Q n d g)
      ⟨⟨j, hj⟩, h₀, T, none⟩ ∧
    x.map φ = hierOf v j ∧ (∀ a ∈ x, a ∈ E) ∧
    Agree T.toLettered (tower T₀.toLettered (markOf v) j) φ E

/-- The initial configuration reaches level `0`. -/
theorem levelReached_zero : LevelReached T₀ d g v 0 (Nat.succ_pos d) :=
  ⟨⟨n, Nat.lt_succ_of_le (le_max_left n g)⟩, T₀, id, v, v, .refl, List.map_id v,
    fun _ h => h, Agree.refl _ _⟩

variable {T₀ d g v}

/-- One derivation leads from level `j` to level `j + 1` when the next dictionary has at
most `g` letters. -/
theorem levelReached_succ (hv : T₀.toLettered.IsHole v) {j : ℕ} (hj : j < depth v)
    (hd : depth v ≤ d) (hk : alphCard v (j + 1) ≤ g) (hr : LevelReached T₀ d g v j (by omega)) :
    LevelReached T₀ d g v (j + 1) (by omega) := by
  obtain ⟨h₀, T, φ, x, E, hreach, hx, hxE, hag⟩ := hr
  have hv0 := hv.ne_nil
  have hBg : (hierOf v (j + 1)).dedup.length < g + 1 := by
    unfold alphCard at hk
    rw [List.card_toFinset] at hk
    omega
  set B := (hierOf v (j + 1)).dedup
  set K : Fin (g + 1) := ⟨B.length, hBg⟩
  obtain ⟨ℓ, hℓx, hℓ⟩ : ∃ ℓ ∈ x, φ ℓ = markOf v j :=
    List.mem_map.mp (hx ▸ markOf_mem hv0 j)
  have hB (a : Fin K) : B[a] ∈ hierOf v (j + 1) := List.mem_dedup.mp (List.getElem_mem _)
  have hlift (a : Fin K) : ∃ Y : List (Fin h₀), Y.map φ = B[a] ∧ ∀ b ∈ Y, b ∈ x := by
    refine exists_map_eq fun y hy => List.mem_map.mp (hx ▸ ?_)
    rw [← expand_hierOf hv0 j]
    exact mem_expand.mpr ⟨_, hB a, List.mem_append_left _ hy⟩
  choose Ys hYs hYx using hlift
  have hYℓ (a : Fin K) : ℓ ∉ Ys a := fun ha => avoid_hierOf j _ (hB a)
    (by rw [← hYs a, ← hℓ]; exact List.mem_map_of_mem ha)
  have hcols : ∀ col ∈ conv Ys, ∀ a, col a ≠ some ℓ := fun col hcol a hca =>
    hYℓ a (dec_conv Ys ▸ mem_dec.mpr ⟨col, hcol, hca⟩)
  have hjd : j < d := by omega
  have h1 := mem_next_iff.mpr (Step.start (Q := Q) (n := n) (j := ⟨j, by omega⟩) (h₀ := h₀)
    (T := T) ℓ K hjd)
  have h2 := reaches_columns (Q := Q) (d := d) (j := ⟨j, by omega⟩) (T := T) (ℓ := ℓ) (h := K)
    [] (conv Ys) (by simpa using valid_conv Ys) hcols
  simp only [List.nil_append] at h2
  set s := (conv Ys).foldl (Summ.step T ℓ) (Summ.start T ℓ K)
  have hs : s.toProp = summ T.toLettered ℓ K Ys := by
    rw [Summ.toProp_eval, colEval T.toLettered ℓ K _ (valid_conv Ys), dec_conv]
  have hdist : ∀ a b, s.2.2.1 a b = true → a = b := by
    intro a b hab
    have heq : Ys a = Ys b :=
      (Iff.of_eq (congrFun (congrFun (congrArg (fun s => s.2.2.1) hs) a) b)).mp hab
    have := congrArg (List.map φ) heq
    rw [hYs, hYs] at this
    exact Fin.ext ((List.nodup_dedup _).getElem_inj_iff.mp this)
  have h3 := mem_next_iff.mpr (Step.finish (j := ⟨j, by omega⟩) (h₀ := h₀) (T := T) (ℓ := ℓ)
    (h := K) (s := s) (st := started (conv Ys)) hjd hdist)
  obtain ⟨x', hx', hx'E⟩ : ∃ x' : List (Fin K), x'.map (fun a => B[a]) = hierOf v (j + 1) ∧
      ∀ b ∈ x', b ∈ List.finRange K := by
    refine exists_map_eq fun Y hY => ?_
    obtain ⟨i, hi, hiY⟩ := List.getElem_of_mem (List.mem_dedup.mpr hY)
    exact ⟨⟨i, hi⟩, List.mem_finRange _, hiY⟩
  have hA := (derTable_agree T ℓ hs hdist).comp (hag.derive (hxE ℓ hℓx)
    ((List.finRange K).map Ys) fun X hX a ha => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hX
      exact hxE a (hYx b a ha))
  rw [show (List.map φ ∘ Ys) = fun a => B[a] from funext hYs, hℓ] at hA
  exact ⟨⟨K, lt_max_succ_of_lt_succ K⟩, derTable T ℓ s, fun a => B[a], x', List.finRange K,
    hreach.tail h1 |>.trans h2 |>.tail h3, hx', hx'E, hA⟩

/-- At the first unary level the lifted word is a unary hole of the table, so the
configuration accepts. -/
theorem summarySearch_of_levelReached (hv : T₀.toLettered.IsHole v) (hd : depth v ≤ d)
    (hr : LevelReached T₀ d g v (depth v) (by omega)) : summarySearch T₀ d g = true := by
  obtain ⟨h₀, T, φ, x, E, hreach, hx, hxE, hag⟩ := hr
  have hhole : T.toLettered.IsHole x := by
    rw [← hag.isHole_iff hxE, hx]
    exact (isHole_hierOf_iff hv.ne_nil _ _).mpr hv
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil x hhole.ne_nil
  have hmem {b : Fin h₀} (hb : b ∈ x) : φ b ∈ hierOf v (depth v) :=
    hx ▸ List.mem_map_of_mem hb
  have hrep : x = List.replicate x.length z := List.eq_replicate_iff.mpr ⟨rfl, fun b hb =>
    hag.inj b (hxE b hb) z (hxE z hz) (isUnary_depth v _ (hmem hb) _ (hmem hz))⟩
  obtain ⟨m, hm1, hm2, hm⟩ := (exists_unary_hole_iff T.toLettered z).mp
    ⟨x.length, hrep ▸ hhole⟩
  rw [card_cores] at hm2
  exact (summarySearch_iff_reachable T₀ d g).mpr
    ⟨_, hreach, accepting_iff.mpr ⟨z, m, hm1, hm2, hm⟩⟩

/-- Completeness of the summary search. If the table has a hole of depth at most `d` and
`g` is at least the dictionary bound, the search succeeds. -/
theorem summarySearch_complete {w : List (Fin n)}
    (hg : dictionaryBound (Fintype.card Q) d ≤ g) (hw : T₀.toLettered.IsHole w)
    (hd : depth w ≤ d) : summarySearch T₀ d g = true := by
  obtain ⟨v, hv, hdepth, -, hdict⟩ := exists_bounded_dictionary_hole hw hd
  have hvd : depth v ≤ d := hdepth ▸ hd
  have key : ∀ j (hj : j ≤ depth v), LevelReached T₀ d g v j (by omega) := by
    intro j
    induction j with
    | zero => exact fun _ => levelReached_zero T₀ d g v
    | succ j ih =>
      exact fun hj => levelReached_succ hv (by omega) hvd
        ((hdict (j + 1) (by omega) hj).trans hg) (ih (by omega))
  exact summarySearch_of_levelReached hv hvd (key _ le_rfl)

end Levels

end DeciNSSE.Complexity.Summary
