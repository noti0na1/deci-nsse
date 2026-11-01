import DeciNSSE.Complexity.SummaryGraph
import DeciNSSE.Holes.Depth

/-! # Soundness of the summary search

Every reachable configuration is realized by the hierarchy of a word. There are
markers `ℓ` and an injective map `ρ` from the current letters to admissible
level-`j` letters along which the current table agrees with the tower of the
reader's table. A derivation in progress holds the summary of a valid column word
over the letters without the marker, and the tracks it has started.

Finishing a derivation spells pairwise distinct blocks `Y_a` that avoid the
marker. The derived table agrees with `Der(T, ℓ)` along the blocks, and the old
agreement passes through `Der`, so the new table agrees with the next tower level
along `a ↦ ρ(Y_a)`, for the marker `ρ(ℓ)` at level `j`. If the search accepts
with `z^m`, then `ρ(z)^m` is an admissible hole at level `j`. Its expansion is a
hole of the reader's table, and the canonical hierarchy of that hole recovers the
unary word at level `j`, so its depth is at most `j ≤ d`.

## Main declarations

- `Summary.Realized`, `Summary.ColumnsRead`: the invariant of reachable
  configurations.
- `Summary.realized_derive`: finishing a derivation keeps the table realized.
- `Summary.exists_hole_of_realized`: a unary hole of a realized table yields a
  hole of the reader's table of depth at most the level.
- `Summary.summarySearch_sound`: if the summary search accepts, the reader's table
  has a hole of depth at most `d`.
-/

namespace DeciNSSE.Complexity.Summary
open CoAlignment LetteredHierarchy BoundedDepth Packets

universe u

section Invariant
variable {Q : Type u} {n : ℕ} (T₀ : Table (Fin n) Q)

/-- A table at level `j` is realized when it agrees with the tower of `T₀` along some
markers `ℓ`, through an injective map `ρ` onto admissible level-`j` letters. -/
def Realized (j : ℕ) {h₀ : ℕ} (T : Table (Fin h₀) (Cores Q j)) : Prop :=
  ∃ (ℓ : (i : ℕ) → Alph (Fin n) i) (ρ : Fin h₀ → Alph (Fin n) j),
    Agree T.toLettered (tower T₀.toLettered ℓ j) ρ (List.finRange h₀) ∧
      Admissible ℓ j (List.ofFn ρ)

/-- A derivation in progress holds the summary of a valid column word over the letters
without the marker, and the tracks the word has started. -/
def ColumnsRead {C : Type u} {h₀ g : ℕ} (T : Table (Fin h₀) C) :
    Option (Derivation C h₀ g) → Prop
  | none => True
  | some ⟨ℓ, h, s, st⟩ => ∃ w : List (Fin h → Option (Fin h₀)), Valid w ∧
      (∀ col ∈ w, ∀ a, col a ≠ some ℓ) ∧
      w.foldl (ColumnSummary.step T ℓ) (ColumnSummary.start T ℓ h) = s ∧ st = started w

/-- Finishing a derivation keeps the table realized: the derived table on pairwise distinct
blocks that avoid the marker is realized at the next level. -/
theorem realized_derive {j h₀ h : ℕ} {T : Table (Fin h₀) (Cores Q j)} (hT : Realized T₀ j T)
    {ℓ : Fin h₀} {s : ColumnSummary (Cores Q j) h} {w : List (Fin h → Option (Fin h₀))}
    (hw : Valid w) (hav : ∀ col ∈ w, ∀ a, col a ≠ some ℓ)
    (hs : w.foldl (ColumnSummary.step T ℓ) (ColumnSummary.start T ℓ h) = s)
    (hd : ∀ a b, s.equalTracks a b = true → a = b) : Realized T₀ (j + 1) (derivedTable T ℓ s) := by
  obtain ⟨ℓ₀, ρ, hA, hadm⟩ := hT
  have hsum : s.toProp = summ T.toLettered ℓ h (dec w) := by
    rw [← hs, ColumnSummary.toProp_eval, colEval _ _ _ _ hw]
  have hA₂ := hA.derive (List.mem_finRange ℓ) ((List.finRange h).map (dec w))
    (fun _ _ a _ => List.mem_finRange a)
  set ℓ' : (i : ℕ) → Alph (Fin n) i := Function.update ℓ₀ j (ρ ℓ)
  have hℓ'j : ℓ' j = ρ ℓ := Function.update_self _ _ _
  have hlt : ∀ t < j, ℓ' t = ℓ₀ t := fun t ht => Function.update_of_ne (by omega) _ _
  have htw : tower T₀.toLettered ℓ' (j + 1) = der (tower T₀.toLettered ℓ₀ j) (ρ ℓ) := by
    show der (tower T₀.toLettered ℓ' j) (ℓ' j) = _
    rw [tower_congr _ j hlt, hℓ'j]
  have hne : List.ofFn ρ ≠ [] := List.ne_nil_of_mem (List.mem_ofFn.mpr ⟨ℓ, rfl⟩)
  refine ⟨ℓ', fun a => (dec w a).map ρ, ?_, ?_, ?_⟩
  · rw [htw]
    exact (derivedTable_agree T ℓ hsum hd).comp hA₂
  · intro X hX hmem
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hX
    rw [hℓ'j] at hmem
    obtain ⟨z, hz, hzρ⟩ := List.mem_map.mp hmem
    obtain rfl := hA.inj z (List.mem_finRange z) ℓ (List.mem_finRange ℓ) hzρ
    obtain ⟨col, hcol, hca⟩ := mem_dec.mp hz
    exact hav col hcol a hca
  · rw [hℓ'j, admissible_congr j hlt]
    refine admissible_of_subset ℓ₀ j _ _ hadm hne fun x hx => ?_
    obtain ⟨Y, hY, hxY⟩ := mem_expand.mp hx
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hY
    rcases List.mem_append.mp hxY with hx | hx
    · obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx
      exact List.mem_ofFn.mpr ⟨z, rfl⟩
    · rw [List.mem_singleton.mp hx]
      exact List.mem_ofFn.mpr ⟨ℓ, rfl⟩

variable [NeZero n]

theorem realized_init : Realized T₀ 0 T₀ :=
  ⟨fun _ => default, id, Agree.refl _ _, trivial⟩

/-- A unary hole of a realized table at level `j` yields a hole of the reader's table of
depth at most `j`. -/
theorem exists_hole_of_realized {j h₀ : ℕ} {T : Table (Fin h₀) (Cores Q j)}
    (hT : Realized T₀ j T) {z : Fin h₀} {m : ℕ} (hm : T.toLettered.IsHole (List.replicate m z)) :
    ∃ w, T₀.toLettered.IsHole w ∧ HierarchyDepth.depth w ≤ j := by
  obtain ⟨ℓ, ρ, hA, hadm⟩ := hT
  have hv := (hA.isHole_iff (v := List.replicate m z) fun a _ => List.mem_finRange a).mpr hm
  rw [List.map_replicate] at hv
  have hne : List.replicate m (ρ z) ≠ [] := by simpa using hm.ne_nil
  have hadm' : Admissible ℓ j (List.replicate m (ρ z)) :=
    admissible_of_subset ℓ j _ _ hadm (List.ne_nil_of_mem (List.mem_ofFn.mpr ⟨z, rfl⟩))
      fun a ha => by rw [List.eq_of_mem_replicate ha]; exact List.mem_ofFn.mpr ⟨z, rfl⟩
  refine ⟨expandTo ℓ j (List.replicate m (ρ z)),
    (isHole_tower_iff T₀.toLettered ℓ j _ hadm' hne).mp hv,
    HierarchyDepth.depth_le_of_isUnary ?_⟩
  rw [(hierOf_expandTo ℓ j _ hadm' hne).1]
  intro a ha b hb
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]

end Invariant

section Sound
variable {Q : Type u} [Fintype Q] [DecidableEq Q] {n d g : ℕ} [NeZero n]

/-- Every configuration reachable from `T₀` has a realized table and reads its columns
correctly. -/
theorem realized_of_reachable {T₀ : Table (Fin n) Q} {c : Config Q n d g}
    (hc : Relation.ReflTransGen (fun a b => b ∈ Config.next a) (Config.init T₀) c) :
    Realized T₀ c.level c.table ∧ ColumnsRead c.table c.derivation := by
  induction hc with
  | refl => exact ⟨realized_init T₀, trivial⟩
  | tail _ hstep ih =>
    rcases Config.mem_next_iff.mp hstep with ⟨ℓ, h, -⟩ | ⟨col, hcol⟩ | ⟨-, hd⟩
    · exact ⟨ih.1, [], fun _ => ⟨0, [], rfl⟩, by simp, rfl, rfl⟩
    · obtain ⟨hR, w, hw, hav, hs, hst⟩ := ih
      refine ⟨hR, w ++ [col], (valid_snoc_iff hw col).mpr fun a ha => (hcol a).2 (hst ▸ ha),
        ?_, ?_, ?_⟩
      · intro col' hcol' a
        rcases List.mem_append.mp hcol' with h' | h'
        · exact hav col' h' a
        · rw [List.mem_singleton.mp h']; exact (hcol a).1
      · rw [List.foldl_append, hs]; rfl
      · funext a; rw [started_snoc, hst]
    · obtain ⟨hR, w, hw, hav, hs, -⟩ := ih
      exact ⟨realized_derive T₀ hR hw hav hs hd, trivial⟩

/-- Soundness of the summary search: if it accepts, the reader's table has a hole of
depth at most `d`. -/
theorem summarySearch_sound {T₀ : Table (Fin n) Q} (h : summarySearch T₀ d g = true) :
    ∃ w, T₀.toLettered.IsHole w ∧ HierarchyDepth.depth w ≤ d := by
  obtain ⟨⟨j, h₀, T, o⟩, hc, hacc⟩ := (summarySearch_iff_reachable T₀ d g).mp h
  obtain ⟨z, m, -, -, hm⟩ := Config.accepting_iff.mp hacc
  obtain ⟨w, hw, hwd⟩ := exists_hole_of_realized T₀ (realized_of_reachable hc).1 hm
  exact ⟨w, hw, hwd.trans (Nat.lt_succ_iff.mp j.2)⟩

/-- The hypothesis of `summarySearch_sound` is satisfiable: the search accepts the one-letter
table whose words are all targets. -/
example : summarySearch
    (⟨0, fun _ c => c, fun _ _ => false, fun _ _ => false, fun _ _ => true⟩ :
      Table (Fin 1) (Fin 1)) 0 0 = true :=
  (summarySearch_iff_reachable _ 0 0).mpr ⟨Config.init _, .refl,
    Config.accepting_iff.mpr ⟨0, 1, le_rfl, by simp, (Table.holeB_iff _ _).mp (by decide)⟩⟩

end Sound

end DeciNSSE.Complexity.Summary
