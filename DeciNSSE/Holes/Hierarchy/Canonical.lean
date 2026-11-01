import DeciNSSE.Holes.Hierarchy.Derived

/-! # The canonical hierarchy

Cutting a word after every occurrence of a marker inverts expansion. Along a
marker sequence `ℓ`, the tower of derived monitors `𝔇_{i+1} = Der(𝔇_i, ℓ_i)`
reads level-`i` words, whose letters are level-`(i-1)` words. The canonical
hierarchy of a nonempty word `w` cuts each level at its last letter. A word is
a hole of `𝔇_0` iff each level of its canonical hierarchy is a hole of the
corresponding derived monitor.

## Main declarations

- `cutAt`, `cutAt_expand`, `expand_cutAt`: cutting at a marker inverts expansion.
- `Alph`, `Cores`: the letters and cores of level `i`.
- `tower`, `expandTo`, `Admissible`: the derived monitors along a marker
  sequence, expansion to level `0`, and the words whose expansions are marker
  parses.
- `isHole_tower_iff`: holes of `𝔇_j` are the admissible words whose expansions
  are holes of `𝔇_0`.
- `hierOf`, `markOf`: the canonical hierarchy `u_i` and its markers `ℓ_i`.
- `isHole_hierOf_iff`: `u_i` is a hole of `𝔇_i` iff `w` is a hole of `𝔇_0`.
- `hierOf_expandTo`: the canonical hierarchy of an expansion.

The declarations are in the namespace `DeciNSSE.LetteredHierarchy`.
-/

namespace DeciNSSE.LetteredHierarchy
open DeciNSSE.CoAlignment
open scoped List

section Cut
variable {Γ : Type*} [DecidableEq Γ]

/-- `cutAt ℓ u`: cut `u` after every `ℓ`, dropping what follows the last `ℓ`
(`u = X_0 ℓ ⋯ X_{k-1} ℓ t ↦ X_0 ⋯ X_{k-1}`). -/
def cutAt (ℓ : Γ) : List Γ → List (List Γ)
  | [] => []
  | a :: u => if a = ℓ then [] :: cutAt ℓ u else
      match cutAt ℓ u with
      | [] => []
      | X :: rest => (a :: X) :: rest

/-- A word without `ℓ` has no complete block. -/
theorem cutAt_of_not_mem {ℓ : Γ} : ∀ {t : List Γ}, ℓ ∉ t → cutAt ℓ t = []
  | [], _ => rfl
  | a :: t, h => by
      have ha : a ≠ ℓ := fun h' => h (h' ▸ List.mem_cons_self)
      have ht : ℓ ∉ t := fun h' => h (List.mem_cons_of_mem _ h')
      simp [cutAt, ha, cutAt_of_not_mem ht]

/-- Cutting reads off a first block that ends at `ℓ`. -/
theorem cutAt_block {ℓ : Γ} (w : List Γ) : ∀ {X : List Γ}, ℓ ∉ X →
    cutAt ℓ (X ++ ℓ :: w) = X :: cutAt ℓ w
  | [], _ => by simp [cutAt]
  | a :: X, h => by
      have ha : a ≠ ℓ := fun h' => h (h' ▸ List.mem_cons_self)
      have hX : ℓ ∉ X := fun h' => h (List.mem_cons_of_mem _ h')
      simp [cutAt, ha, cutAt_block w hX]

/-- `cutAt ℓ (σ_ℓ(v) t) = v` for `v` avoiding `ℓ` and `ℓ ∉ t`. -/
theorem cutAt_expand_append {ℓ : Γ} {t : List Γ} (ht : ℓ ∉ t) :
    ∀ {v : List (List Γ)}, (∀ X ∈ v, ℓ ∉ X) → cutAt ℓ (expand ℓ v ++ t) = v
  | [], _ => by simpa using cutAt_of_not_mem ht
  | X :: v, h => by
      rw [expand_cons, List.append_assoc, List.cons_append,
        cutAt_block _ (h X List.mem_cons_self),
        cutAt_expand_append ht (fun Y hY => h Y (List.mem_cons_of_mem _ hY))]

/-- The canonical next level of an expansion is the word itself. -/
theorem cutAt_expand {ℓ : Γ} {v : List (List Γ)} (h : ∀ X ∈ v, ℓ ∉ X) :
    cutAt ℓ (expand ℓ v) = v := by
  simpa using cutAt_expand_append (t := []) (by simp) h

/-- Every word is `σ_ℓ(v) t` with `v` avoiding `ℓ` and `ℓ ∉ t`. -/
theorem exists_expand_append (ℓ : Γ) : ∀ u : List Γ,
    ∃ v t, u = expand ℓ v ++ t ∧ ℓ ∉ t ∧ ∀ X ∈ v, ℓ ∉ X
  | [] => ⟨[], [], rfl, by simp, by simp⟩
  | a :: u => by
      obtain ⟨v, t, rfl, ht, hv⟩ := exists_expand_append ℓ u
      by_cases ha : a = ℓ
      · subst ha
        refine ⟨[] :: v, t, by simp, ht, ?_⟩
        intro X hX
        rcases List.mem_cons.mp hX with rfl | hX
        · simp
        · exact hv X hX
      · rcases v with _ | ⟨X, v⟩
        · refine ⟨[], a :: t, by simp, ?_, by simp⟩
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm ha, ht⟩
        · refine ⟨(a :: X) :: v, t, by simp, ht, ?_⟩
          intro Y hY
          rcases List.mem_cons.mp hY with rfl | hY
          · simp only [List.mem_cons, not_or]
            exact ⟨Ne.symm ha, hv X List.mem_cons_self⟩
          · exact hv Y (List.mem_cons_of_mem _ hY)

/-- The blocks of a cut avoid the marker. -/
theorem avoid_cutAt (ℓ : Γ) (u : List Γ) : ∀ X ∈ cutAt ℓ u, ℓ ∉ X := by
  obtain ⟨v, t, rfl, ht, hv⟩ := exists_expand_append ℓ u
  rw [cutAt_expand_append ht hv]
  exact hv

/-- If `u` ends with `ℓ`, then `σ_ℓ(cutAt ℓ u) = u`. -/
theorem expand_cutAt {ℓ : Γ} {u : List Γ} (hu : u.getLast? = some ℓ) :
    expand ℓ (cutAt ℓ u) = u := by
  obtain ⟨v, t, rfl, ht, hv⟩ := exists_expand_append ℓ u
  rw [cutAt_expand_append ht hv]
  rcases List.eq_nil_or_concat t with rfl | ⟨t', b, rfl⟩
  · simp
  · rw [List.concat_eq_append, ← List.append_assoc, List.getLast?_append_of_ne_nil _
      (by simp), List.getLast?_singleton, Option.some.injEq] at hu
    exact absurd (by simp [hu]) ht

/-- A word ending with `ℓ` has at least one block. -/
theorem cutAt_ne_nil {ℓ : Γ} {u : List Γ} (hu : u.getLast? = some ℓ) : cutAt ℓ u ≠ [] := by
  intro h
  have := expand_cutAt hu
  rw [h, expand_nil] at this
  subst this
  simp at hu

omit [DecidableEq Γ] in
/-- A nonempty expansion ends with its marker. -/
theorem getLast?_expand {ℓ : Γ} {v : List (List Γ)} (hv : v ≠ []) :
    (expand ℓ v).getLast? = some ℓ := by
  rcases List.eq_nil_or_concat v with rfl | ⟨v', X, rfl⟩
  · exact absurd rfl hv
  · rw [List.concat_eq_append, expand_snoc, List.getLast?_append_of_ne_nil _ (by simp)]
    simp

end Cut

section Hierarchy
universe u v

/-- Level-`i` letters: `Γ_0 = α`, `Γ_{i+1} = Γ_i*` (packets are kept as words). -/
@[reducible] def Alph (α : Type u) : ℕ → Type u
  | 0 => α
  | i + 1 => List (Alph α i)

/-- Level-`i` cores: `C_0 = Q`, `C_{i+1} = C_i ⊎ {⋆_{i+1}}` (`none` is the new start core). -/
@[reducible] def Cores (Q : Type v) : ℕ → Type v
  | 0 => Q
  | i + 1 => Option (Cores Q i)

/-- Letters of every level have decidable equality. -/
instance instDecEqAlph {α : Type u} [DecidableEq α] : ∀ i, DecidableEq (Alph α i)
  | 0 => (inferInstance : DecidableEq α)
  | i + 1 => @instDecidableEqList (Alph α i) (instDecEqAlph i)

/-- Letters of every level are inhabited, by the empty packet above level `0`. -/
instance instInhabitedAlph {α : Type u} [Inhabited α] : ∀ i, Inhabited (Alph α i)
  | 0 => (inferInstance : Inhabited α)
  | _ + 1 => ⟨[]⟩

variable {α : Type u} {Q : Type v}

/-- The tower `𝔇_0 = D0`, `𝔇_{i+1} = Der(𝔇_i, ℓ_i)` along a marker sequence `ℓ`. -/
def tower (D0 : Lettered α Q) (ℓ : (i : ℕ) → Alph α i) :
    (i : ℕ) → Lettered (Alph α i) (Cores Q i)
  | 0 => D0
  | i + 1 => der (tower D0 ℓ i) (ℓ i)

/-- The tower at level `i` depends only on the markers below `i`. -/
theorem tower_congr (D0 : Lettered α Q) {ℓ ℓ' : (i : ℕ) → Alph α i} :
    ∀ i, (∀ k < i, ℓ k = ℓ' k) → tower D0 ℓ i = tower D0 ℓ' i
  | 0, _ => rfl
  | i + 1, h => by
      show der (tower D0 ℓ i) (ℓ i) = der (tower D0 ℓ' i) (ℓ' i)
      rw [tower_congr D0 i (fun k hk => h k (by omega)), h i (by omega)]

/-- Expansion from level `j` down to level `0`: `σ_{ℓ_0} ∘ ⋯ ∘ σ_{ℓ_{j-1}}`. -/
def expandTo (ℓ : (i : ℕ) → Alph α i) : (j : ℕ) → List (Alph α j) → List α
  | 0, v => v
  | j + 1, v => expandTo ℓ j (expand (ℓ j) v)

/-- Expansion maps the empty word to the empty word. -/
@[simp] theorem expandTo_nil (ℓ : (i : ℕ) → Alph α i) : ∀ j, expandTo ℓ j [] = []
  | 0 => rfl
  | j + 1 => expandTo_nil ℓ j

/-- Expansion from level `j` is a word morphism. -/
theorem expandTo_append (ℓ : (i : ℕ) → Alph α i) : ∀ (j : ℕ) (u u' : List (Alph α j)),
    expandTo ℓ j (u ++ u') = expandTo ℓ j u ++ expandTo ℓ j u'
  | 0, _, _ => rfl
  | j + 1, u, u' => by
      show expandTo ℓ j (expand (ℓ j) (u ++ u')) =
        expandTo ℓ j (expand (ℓ j) u) ++ expandTo ℓ j (expand (ℓ j) u')
      rw [expand_append, expandTo_append ℓ j]

/-- Expansion from level `j` depends only on the markers below `j`. -/
theorem expandTo_congr {ℓ ℓ' : (i : ℕ) → Alph α i} : ∀ (j : ℕ), (∀ t < j, ℓ t = ℓ' t) →
    ∀ v : List (Alph α j), expandTo ℓ j v = expandTo ℓ' j v
  | 0, _, _ => rfl
  | j + 1, h, v => by
      show expandTo ℓ j (expand (ℓ j) v) = expandTo ℓ' j (expand (ℓ' j) v)
      rw [h j (by omega), expandTo_congr j (fun t ht => h t (by omega))]

/-- A level-`j` word is admissible for `ℓ` when at every level its letters avoid the
marker below, so that the expansions are marker parses. -/
def Admissible (ℓ : (i : ℕ) → Alph α i) : (j : ℕ) → List (Alph α j) → Prop
  | 0, _ => True
  | j + 1, v => (∀ X ∈ v, ℓ j ∉ X) ∧ Admissible ℓ j (expand (ℓ j) v)

/-- Admissibility at level `j` depends only on the markers below `j`. -/
theorem admissible_congr {ℓ ℓ' : (i : ℕ) → Alph α i} : ∀ (j : ℕ), (∀ t < j, ℓ t = ℓ' t) →
    ∀ v : List (Alph α j), Admissible ℓ j v ↔ Admissible ℓ' j v
  | 0, _, _ => Iff.rfl
  | j + 1, h, v => by
      show ((∀ X ∈ v, ℓ j ∉ X) ∧ Admissible ℓ j (expand (ℓ j) v)) ↔
        ((∀ X ∈ v, ℓ' j ∉ X) ∧ Admissible ℓ' j (expand (ℓ' j) v))
      rw [h j (by omega), admissible_congr j (fun t ht => h t (by omega))]

/-- Admissibility only depends on the letters (for nonempty words). -/
theorem admissible_of_subset (ℓ : (i : ℕ) → Alph α i) : ∀ (j : ℕ) (v v₀ : List (Alph α j)),
    Admissible ℓ j v₀ → v₀ ≠ [] → (∀ a ∈ v, a ∈ v₀) → Admissible ℓ j v
  | 0, _, _, _, _, _ => trivial
  | j + 1, v, v₀, ⟨hav, had⟩, hv₀, hsub => by
      refine ⟨fun X hX => hav X (hsub X hX), admissible_of_subset ℓ j _ _ had
        (by simpa [expand_eq_nil] using hv₀) ?_⟩
      intro a ha
      obtain ⟨X, hX, haX⟩ := mem_expand.mp ha
      rw [List.mem_append, List.mem_singleton] at haX
      rcases haX with haX | rfl
      · exact mem_expand.mpr ⟨X, hsub X hX, List.mem_append_left _ haX⟩
      · obtain ⟨Y, hY⟩ := List.exists_mem_of_ne_nil v₀ hv₀
        exact mem_expand.mpr ⟨Y, hY, by simp⟩

/-- Expansion keeps nonempty words nonempty. -/
theorem expandTo_ne_nil (ℓ : (i : ℕ) → Alph α i) :
    ∀ (j : ℕ) (v : List (Alph α j)), v ≠ [] → expandTo ℓ j v ≠ []
  | 0, _, h => h
  | j + 1, v, h => expandTo_ne_nil ℓ j _ (by simpa [expand_eq_nil] using h)

/-- For a nonempty admissible level-`j` word `v`:
`v` is a hole of `𝔇_j` iff its expansion is a hole of `𝔇_0`. -/
theorem isHole_tower_iff (D0 : Lettered α Q) (ℓ : (i : ℕ) → Alph α i) :
    ∀ (j : ℕ) (v : List (Alph α j)), Admissible ℓ j v → v ≠ [] →
      ((tower D0 ℓ j).IsHole v ↔ D0.IsHole (expandTo ℓ j v))
  | 0, _, _, _ => Iff.rfl
  | j + 1, v, ⟨hav, had⟩, hv => by
      rw [show tower D0 ℓ (j + 1) = der (tower D0 ℓ j) (ℓ j) from rfl,
        isHole_der_iff _ _ v hv hav,
        isHole_tower_iff D0 ℓ j _ had (by simpa [expand_eq_nil] using hv)]
      rfl

variable [DecidableEq α] [Inhabited α]

/-- The canonical hierarchy obtained by cutting at the last letter of each level. -/
def hierOf (w : List α) : (i : ℕ) → List (Alph α i)
  | 0 => w
  | i + 1 => cutAt ((hierOf w i).getLastD default) (hierOf w i)

/-- The canonical markers `ℓ_i` = the last letter of `u_i`. -/
def markOf (w : List α) (i : ℕ) : Alph α i := (hierOf w i).getLastD default

/-- Level `i + 1` cuts level `i` at its marker. -/
theorem hierOf_succ (w : List α) (i : ℕ) :
    hierOf w (i + 1) = cutAt (markOf w i) (hierOf w i) := rfl

section Canonical
variable {w : List α} (hw : w ≠ [])
include hw

/-- Every level of the hierarchy of a nonempty word is nonempty. -/
theorem hierOf_ne_nil : ∀ i, hierOf w i ≠ []
  | 0 => hw
  | i + 1 => by
      rw [hierOf_succ]
      refine cutAt_ne_nil ?_
      rw [markOf, List.getLastD_eq_getLast?]
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp
        (by simpa using hierOf_ne_nil i : (hierOf w i).getLast? ≠ none)
      simp [ha]

/-- Every level of the hierarchy of a nonempty word ends with its marker. -/
theorem getLast?_hierOf (i : ℕ) : (hierOf w i).getLast? = some (markOf w i) := by
  rw [markOf, List.getLastD_eq_getLast?]
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp
    (by simpa using hierOf_ne_nil hw i : (hierOf w i).getLast? ≠ none)
  simp [ha]

/-- Expanding level `i + 1` at the marker `ℓ_i` gives level `i`. -/
theorem expand_hierOf (i : ℕ) : expand (markOf w i) (hierOf w (i + 1)) = hierOf w i := by
  rw [hierOf_succ, expand_cutAt (getLast?_hierOf hw i)]

omit hw in
/-- The letters of level `i + 1` avoid the marker `ℓ_i`. -/
theorem avoid_hierOf (i : ℕ) : ∀ X ∈ hierOf w (i + 1), markOf w i ∉ X := by
  rw [hierOf_succ]; exact avoid_cutAt _ _

/-- The marker of a level is one of its letters. -/
theorem markOf_mem (i : ℕ) : markOf w i ∈ hierOf w i :=
  List.mem_of_getLast? (getLast?_hierOf hw i)

/-- The canonical hierarchy is admissible for its markers. -/
theorem admissible_hierOf : ∀ i, Admissible (markOf w) i (hierOf w i)
  | 0 => trivial
  | i + 1 => ⟨avoid_hierOf i, by rw [expand_hierOf hw i]; exact admissible_hierOf i⟩

/-- Expanding level `i` down to level `0` gives back `w`. -/
theorem expandTo_hierOf : ∀ i, expandTo (markOf w) i (hierOf w i) = w
  | 0 => rfl
  | i + 1 => by
      rw [expandTo, expand_hierOf hw i]; exact expandTo_hierOf i

/-- Along the canonical hierarchy, `w` is a hole of `𝔇_0` iff `u_i` is a
hole of `𝔇_i = Der(⋯Der(𝔇_0, ℓ_0)⋯, ℓ_{i-1})`, for every `i`. -/
theorem isHole_hierOf_iff (D0 : Lettered α Q) (i : ℕ) :
    (tower D0 (markOf w) i).IsHole (hierOf w i) ↔ D0.IsHole w := by
  rw [isHole_tower_iff D0 (markOf w) i _ (admissible_hierOf hw i) (hierOf_ne_nil hw i),
    expandTo_hierOf hw i]

end Canonical

/-- The canonical hierarchy of an expansion. Expanding a nonempty admissible level-`j` word and
recomputing the hierarchy gives the word back at level `j`, with the same markers below `j`. -/
theorem hierOf_expandTo (ℓ : (i : ℕ) → Alph α i) : ∀ (j : ℕ) (v : List (Alph α j)),
    Admissible ℓ j v → v ≠ [] →
      hierOf (expandTo ℓ j v) j = v ∧ ∀ i < j, markOf (expandTo ℓ j v) i = ℓ i
  | 0, _, _, _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, v, ⟨hav, had⟩, hv => by
      have hv' : expand (ℓ j) v ≠ [] := by simpa [expand_eq_nil] using hv
      obtain ⟨h1, h2⟩ := hierOf_expandTo ℓ j _ had hv'
      have hm : markOf (expandTo ℓ (j + 1) v) j = ℓ j := by
        rw [markOf, expandTo, h1, List.getLastD_eq_getLast?, getLast?_expand hv]
        rfl
      refine ⟨?_, fun i hi => ?_⟩
      · rw [hierOf_succ, hm, expandTo, h1, cutAt_expand hav]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h2 i hi
        · exact hm

end Hierarchy

end DeciNSSE.LetteredHierarchy
