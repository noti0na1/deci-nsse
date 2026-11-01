import DeciNSSE.Complexity.SummaryColumns
import DeciNSSE.Complexity.Reach
import DeciNSSE.Holes.Exchange

/-! # The summary search graph

The summary search builds the canonical hierarchy from the bottom, one level at a
time, and stores only the table of the current level, never the word. A
configuration holds a level `j ≤ d`, the table of the current monitor on `h₀`
letters, with the `N + j` cores of level `j`, and possibly a derivation in
progress. A derivation fixes a marker and a number `h ≤ g` of blocks, reads a
valid column word over the letters without the marker one column at a time, and
keeps only the Boolean summary of the columns read and the tracks that have
started. When the summary declares the blocks pairwise distinct, the derived
table on the blocks replaces the current table at level `j + 1`. A configuration
accepts when its table has a unary hole `z^m` with `1 ≤ m ≤ N + j`.

The search graph is finite, and the search decides reachability of an accepting
configuration by saturation.

## Main declarations

- `Summary.Config`: configurations, with the projections `Config.level`,
  `Config.letters`, `Config.table` and `Config.derivation`, and `Config.init`,
  `Config.next` and `Config.accepting`.
- `Summary.Config.Step`, `Summary.Config.mem_next_iff`: the three moves of the search.
- `Summary.summarySearch`: the summary search, and
  `Summary.summarySearch_iff_reachable`, its reachability characterization.
-/

namespace DeciNSSE.Complexity.Summary
open CoAlignment LetteredHierarchy BoundedDepth

universe u

section Config
variable (Q : Type u) [Fintype Q] [DecidableEq Q] (n d g : ℕ)

/-- A derivation in progress over `h₀` letters with cores `C`: the marker, the number of
blocks, the summary of the columns read so far, and the tracks that have started. -/
abbrev Derivation (C : Type u) (h₀ g : ℕ) : Type u :=
  Σ _ : Fin h₀, Σ h : Fin (g + 1), ColumnSummary C h × (Fin h → Bool)

/-- Configurations of the summary search: a level `j ≤ d`, a number `h₀ ≤ max n g` of
letters, the current table over them with the cores of level `j`, and possibly a derivation
in progress. -/
abbrev Config : Type u :=
  Σ j : Fin (d + 1), Σ h₀ : Fin (max n g + 1),
    Table (Fin h₀) (Cores Q j) × Option (Derivation (Cores Q j) h₀ g)

instance instFintypeDerivation (C : Type u) [Fintype C] [DecidableEq C] (h₀ : ℕ) :
    Fintype (Derivation C h₀ g) :=
  inferInstance

instance instDecEqDerivation (C : Type u) [Fintype C] [DecidableEq C] (h₀ : ℕ) :
    DecidableEq (Derivation C h₀ g) :=
  inferInstance

instance instFintypeConfig : Fintype (Config Q n d g) :=
  inferInstance

instance instDecEqConfig : DecidableEq (Config Q n d g) :=
  inferInstance

end Config

section Projections
variable {Q : Type u} [Fintype Q] [DecidableEq Q] {n d g : ℕ}

/-- The level of a configuration. -/
abbrev Config.level (c : Config Q n d g) : Fin (d + 1) := c.1

/-- The number of letters of the current table. -/
abbrev Config.letters (c : Config Q n d g) : Fin (max n g + 1) := c.2.1

/-- The current table, over the letters `Fin c.letters` with the cores of the level. -/
abbrev Config.table (c : Config Q n d g) : Table (Fin c.letters) (Cores Q c.level) := c.2.2.1

/-- The derivation in progress, if any. -/
abbrev Config.derivation (c : Config Q n d g) :
    Option (Derivation (Cores Q c.level) c.letters g) :=
  c.2.2.2

end Projections

section Moves
variable {Q : Type u} [Fintype Q] [DecidableEq Q] {n d g : ℕ}

/-- The initial configuration: level `0`, the reader's table on its `n` letters. -/
def Config.init (T₀ : Table (Fin n) Q) : Config Q n d g :=
  ⟨⟨0, Nat.succ_pos d⟩, ⟨n, Nat.lt_succ_of_le (le_max_left n g)⟩, T₀, none⟩

/-- A column may extend the column word read so far: it avoids the marker and carries a
letter on every started track. -/
def ColumnAllowed {h₀ h : ℕ} (ℓ : Fin h₀) (st : Fin h → Bool) (col : Fin h → Option (Fin h₀)) :
    Prop :=
  ∀ a, col a ≠ some ℓ ∧ (st a = true → (col a).isSome)

instance {h₀ h : ℕ} (ℓ : Fin h₀) (st : Fin h → Bool) : DecidablePred (ColumnAllowed ℓ st) :=
  fun _ => Fintype.decidableForallFintype

/-- A number of blocks is a possible number of letters of the next table. -/
theorem lt_max_succ_of_lt_succ (h : Fin (g + 1)) : h.1 < max n g + 1 :=
  Nat.lt_of_lt_of_le h.2 (Nat.succ_le_succ (le_max_right n g))

/-- The successor configurations: start a derivation with a marker and a number of blocks,
read one more column, or finish the derivation at the next level if the blocks are pairwise
distinct. -/
def Config.next : Config Q n d g → Finset (Config Q n d g)
  | ⟨j, h₀, T, none⟩ =>
      if j.1 < d then
        Finset.univ.image fun p : Fin h₀ × Fin (g + 1) =>
          ⟨j, h₀, T, some ⟨p.1, p.2, ColumnSummary.start T p.1 p.2, fun _ => false⟩⟩
      else ∅
  | ⟨j, h₀, T, some ⟨ℓ, h, s, st⟩⟩ =>
      ((Finset.univ.filter (ColumnAllowed ℓ st)).image fun col =>
          ⟨j, h₀, T,
            some ⟨ℓ, h, ColumnSummary.step T ℓ s col, fun a => st a || (col a).isSome⟩⟩) ∪
      if hj : j.1 < d ∧ ∀ a b, s.equalTracks a b = true → a = b then
        {⟨⟨j.1 + 1, Nat.succ_lt_succ hj.1⟩, ⟨h.1, lt_max_succ_of_lt_succ h⟩, derivedTable T ℓ s,
          none⟩}
      else ∅

variable (Q n d g) in
/-- The moves of the summary search. -/
inductive Config.Step : Config Q n d g → Config Q n d g → Prop
  /-- Start a derivation with marker `ℓ` and `h` blocks. -/
  | start {j : Fin (d + 1)} {h₀ : Fin (max n g + 1)} {T : Table (Fin h₀) (Cores Q j)}
      (ℓ : Fin h₀) (h : Fin (g + 1)) (hj : j.1 < d) :
      Step ⟨j, h₀, T, none⟩ ⟨j, h₀, T, some ⟨ℓ, h, ColumnSummary.start T ℓ h, fun _ => false⟩⟩
  /-- Read one more column. -/
  | column {j : Fin (d + 1)} {h₀ : Fin (max n g + 1)} {T : Table (Fin h₀) (Cores Q j)}
      {ℓ : Fin h₀} {h : Fin (g + 1)} {s : ColumnSummary (Cores Q j) h} {st : Fin h → Bool}
      (col : Fin h → Option (Fin h₀)) (hc : ColumnAllowed ℓ st col) :
      Step ⟨j, h₀, T, some ⟨ℓ, h, s, st⟩⟩
        ⟨j, h₀, T, some ⟨ℓ, h, ColumnSummary.step T ℓ s col, fun a => st a || (col a).isSome⟩⟩
  /-- Finish the derivation: the derived table on the blocks at the next level. -/
  | finish {j : Fin (d + 1)} {h₀ : Fin (max n g + 1)} {T : Table (Fin h₀) (Cores Q j)}
      {ℓ : Fin h₀} {h : Fin (g + 1)} {s : ColumnSummary (Cores Q j) h} {st : Fin h → Bool}
      (hj : j.1 < d) (hd : ∀ a b, s.equalTracks a b = true → a = b) :
      Step ⟨j, h₀, T, some ⟨ℓ, h, s, st⟩⟩
        ⟨⟨j.1 + 1, Nat.succ_lt_succ hj⟩, ⟨h.1, lt_max_succ_of_lt_succ h⟩, derivedTable T ℓ s,
          none⟩

/-- The successors are exactly the moves. -/
theorem Config.mem_next_iff {c c' : Config Q n d g} :
    c' ∈ c.next ↔ Config.Step Q n d g c c' := by
  rcases c with ⟨j, h₀, T, _ | ⟨ℓ, h, s, st⟩⟩
  · constructor
    · intro hc
      simp only [Config.next] at hc
      split_ifs at hc with hj
      · obtain ⟨⟨ℓ, h⟩, -, rfl⟩ := Finset.mem_image.mp hc
        exact Config.Step.start ℓ h hj
      · simp at hc
    · rintro ⟨ℓ, h, hj⟩
      simp only [Config.next, hj, ↓reduceIte]
      exact Finset.mem_image.mpr ⟨(ℓ, h), Finset.mem_univ _, rfl⟩
  · constructor
    · intro hc
      simp only [Config.next] at hc
      rcases Finset.mem_union.mp hc with hc | hc
      · obtain ⟨col, hcol, rfl⟩ := Finset.mem_image.mp hc
        exact Config.Step.column col (Finset.mem_filter.mp hcol).2
      · split_ifs at hc with hj
        · rw [Finset.mem_singleton.mp hc]
          exact Config.Step.finish hj.1 hj.2
        · simp at hc
    · rintro (_ | ⟨col, hcol⟩ | ⟨hj, hd⟩)
      · simp only [Config.next]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨col, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol⟩, rfl⟩)
      · simp only [Config.next, dite_eq_left (And.intro hj hd)]
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- A configuration accepts when its table has a unary hole `z^m` with
`1 ≤ m ≤ N + j`. -/
def Config.accepting : Config Q n d g → Bool
  | ⟨j, h₀, T, _⟩ => decide (∃ z : Fin h₀, ∃ m : Fin (Fintype.card Q + j.1),
      T.holeB (List.replicate (m.1 + 1) z) = true)

omit [DecidableEq Q] in
theorem Config.accepting_iff {j : Fin (d + 1)} {h₀ : Fin (max n g + 1)}
    {T : Table (Fin h₀) (Cores Q j)} {o : Option (Derivation (Cores Q j) h₀ g)} :
    Config.accepting (⟨j, h₀, T, o⟩ : Config Q n d g) = true ↔
      ∃ (z : Fin h₀) (m : ℕ), 1 ≤ m ∧ m ≤ Fintype.card Q + j.1 ∧
        T.toLettered.IsHole (List.replicate m z) := by
  simp only [Config.accepting, decide_eq_true_eq, Table.holeB_iff]
  constructor
  · rintro ⟨z, m, hm⟩
    exact ⟨z, m.1 + 1, by omega, m.2, hm⟩
  · rintro ⟨z, m, h1, h2, hm⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact ⟨z, ⟨m', by omega⟩, hm⟩

end Moves

section Search
variable {Q : Type u} [Fintype Q] [DecidableEq Q] {n : ℕ}

/-- The summary search: some accepting configuration is reachable from the reader's table,
with levels up to `d` and at most `g` blocks per level. The test runs over the reachable
set only, never over all configurations. -/
def summarySearch (T₀ : Table (Fin n) Q) (d g : ℕ) : Bool :=
  decide ((reachSet Config.next (Config.init T₀ : Config Q n d g)).filter
    fun c => c.accepting = true).Nonempty

/-- The summary search decides reachability of an accepting configuration. -/
theorem summarySearch_iff_reachable (T₀ : Table (Fin n) Q) (d g : ℕ) :
    summarySearch T₀ d g = true ↔
      ∃ c, Relation.ReflTransGen (fun a b => b ∈ Config.next a)
        (Config.init T₀ : Config Q n d g) c ∧
        c.accepting = true := by
  simp only [summarySearch, decide_eq_true_eq, Finset.filter_nonempty_iff, mem_reachSet]

end Search

end DeciNSSE.Complexity.Summary
