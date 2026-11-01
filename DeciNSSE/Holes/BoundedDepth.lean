import DeciNSSE.Holes.Hierarchy
import DeciNSSE.Holes.Columns

/-! # Finite search at bounded hierarchy depth

At a unary level `i` of the canonical hierarchy a short power of one letter is
a hole. Below it, column compression replaces the letters of a support by
short sub-words with the same derived atomic type; deduplicating the supports
keeps every compression within a bounded positive dictionary. Iterating down
to level `0` bounds the length of a witness of depth at most `d`. This does
not bound every hole of that depth.

## Main declarations

- `card_cores`: the level-`i` instance has `N + i` cores.
- `PositiveDictionaryBound`, `descentFactor`: the dictionary bound and the
  compression factor of one level.
- `shorten_level_supported`: compression of a support of level `j`, with the
  steps `length_le_of_dictionaryBound`, `admissible_update_map` and
  `length_expandTo_update_le`.
- `exists_short_hole_of_dictionary`: a hole with a bounded dictionary through a
  unary level has a witness of length at most
  `(N + d + 1) * descentFactor N d g ^ d`.

The agreement of monitors (`Holes/Agree`) and the column automaton
(`Holes/Columns`) are in their own modules, imported here. All three modules
use the namespace `DeciNSSE.BoundedDepth`.
-/

namespace DeciNSSE.BoundedDepth
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy
open scoped List

section Cores
universe v
variable {Q : Type v}

/-- The cores of every level are finite. -/
instance instFintypeCores [Fintype Q] : ∀ i, Fintype (Cores Q i)
  | 0 => (inferInstance : Fintype Q)
  | i + 1 => by haveI := instFintypeCores i; exact (inferInstance : Fintype (Option (Cores Q i)))

/-- Size of the derived instances. The level-`i` instance has
`|C_i| = N + i` cores (the reader's states and one start core per level). -/
theorem card_cores [Fintype Q] : ∀ i, Fintype.card (Cores Q i) = Fintype.card Q + i
  | 0 => rfl
  | i + 1 => by
      have e : @Fintype.card (Cores Q (i + 1)) (instFintypeCores (i + 1)) =
          Fintype.card (Cores Q i) + 1 := @Fintype.card_option (Cores Q i) (instFintypeCores i)
      rw [e, card_cores i]
      omega

end Cores

section Levels
universe u v
variable {α : Type u} {Q : Type v}

/-- A level-`j` word whose letters expand to at most `B` letters each expands to at most
`|u| B` letters. -/
theorem length_expandTo_le (ℓ : (i : ℕ) → Alph α i) (j : ℕ) {B : ℕ} :
    ∀ u : List (Alph α j), (∀ z ∈ u, (expandTo ℓ j [z]).length ≤ B) →
      (expandTo ℓ j u).length ≤ u.length * B
  | [], _ => by simp [expandTo_nil]
  | z :: u, h => by
      rw [show z :: u = [z] ++ u from rfl, expandTo_append, List.length_append,
        List.length_append, List.length_singleton, Nat.add_mul, one_mul]
      have h1 := length_expandTo_le ℓ j u (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have h2 := h z List.mem_cons_self
      omega

/-- Only positive hierarchy levels need a dictionary bound. -/
def PositiveDictionaryBound [DecidableEq α] [Inhabited α]
    (w : List α) (d g : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ d → (hierOf w i).toFinset.card ≤ g

/-- A common upper bound for one column-compression step. -/
def descentFactor (N d g : ℕ) : ℕ := colBound (N + d + 1) g

/-- Increasing the core allowance increases the column bound. -/
theorem colBound_mono_core {N M k : ℕ} (hNM : N ≤ M) (hM : 1 ≤ M) :
    colBound N k ≤ colBound M k := by
  unfold colBound
  gcongr <;> exact Nat.one_le_pow _ _ (by decide)

/-- A letter in an upper block belongs to the original lower dictionary. -/
theorem mem_lower_dictionary [DecidableEq α] [Inhabited α] {w : List α}
    (hw : w ≠ []) {j : ℕ} {X : Alph α (j + 1)}
    (hX : X ∈ hierOf w (j + 1)) {a : Alph α j} (ha : a ∈ X) :
    a ∈ hierOf w j := by
  rw [← expand_hierOf hw j]
  exact mem_expand.mpr ⟨X, hX, List.mem_append_left _ ha⟩

/-- A duplicate-free list of letters of a positive level has at most `g` entries under a
positive dictionary bound. -/
theorem length_le_of_dictionaryBound [DecidableEq α] [Inhabited α] {w : List α} {j g : ℕ}
    (hg : PositiveDictionaryBound w (j + 1) g) {E : List (Alph α (j + 1))} (hE : E.Nodup)
    (hsub : ∀ x ∈ E, x ∈ hierOf w (j + 1)) : E.length ≤ g := by
  rw [← List.toFinset_card_of_nodup hE]
  have hfin : E.toFinset ⊆ (hierOf w (j + 1)).toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (hsub x (List.mem_toFinset.mp hx))
  exact (Finset.card_le_card hfin).trans (hg _ (by omega) le_rfl)

/-- Admissibility after one compression step. Suppose `φ₀` sends no letter of a support
`F ∋ m` other than `m` to `φ₀ m`, and `F.map φ₀` is admissible for `ℓ''` at level `j`. If the
blocks `ψ X` lie over `F` and avoid `m`, then the blocks `(ψ X).map φ₀` form an admissible
level-`(j + 1)` word once the marker of level `j` is set to `φ₀ m`. -/
theorem admissible_update_map (ℓ'' : (i : ℕ) → Alph α i) {j : ℕ} (φ₀ : Alph α j → Alph α j)
    {F : List (Alph α j)} {m : Alph α j} (hm : m ∈ F) (hinj : ∀ a ∈ F, φ₀ a = φ₀ m → a = m)
    (hadm : Admissible ℓ'' j (F.map φ₀)) {E : List (Alph α (j + 1))}
    (ψ : Alph α (j + 1) → Alph α (j + 1)) (hF : ∀ X ∈ E, ∀ a ∈ ψ X, a ∈ F)
    (hav : ∀ X ∈ E, m ∉ ψ X) :
    Admissible (Function.update ℓ'' j (φ₀ m)) (j + 1) (E.map fun X => (ψ X).map φ₀) := by
  have hℓ'j : Function.update ℓ'' j (φ₀ m) j = φ₀ m := Function.update_self _ _ _
  have hℓ'lt : ∀ t < j, Function.update ℓ'' j (φ₀ m) t = ℓ'' t := fun t ht =>
    Function.update_of_ne (by omega) _ _
  refine ⟨?_, ?_⟩
  · intro Y hY hmem
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
    rw [hℓ'j] at hmem
    obtain ⟨z, hz, hzeq⟩ := List.mem_map.mp hmem
    rw [hinj z (hF X hX z hz) hzeq] at hz
    exact hav X hX hz
  · rw [hℓ'j, admissible_congr j hℓ'lt]
    refine admissible_of_subset ℓ'' j _ (F.map φ₀) hadm (by
      intro he
      have := List.mem_map_of_mem (f := φ₀) hm
      rw [he] at this
      simp at this) ?_
    intro a ha
    obtain ⟨Y, hY, haY⟩ := mem_expand.mp ha
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
    rcases List.mem_append.mp haY with h1 | h1
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h1
      exact List.mem_map_of_mem (hF X hX z hz)
    · rw [List.mem_singleton] at h1
      rw [h1]
      exact List.mem_map_of_mem hm

/-- Length after one compression step. With the marker of level `j` set to `φ₀ m`, the
letter `Y.map φ₀` of level `j + 1` expands to at most `(|Y| + 1) B` letters when `m` and every
letter of `Y` expand under `φ₀` to at most `B` letters. -/
theorem length_expandTo_update_le (ℓ'' : (i : ℕ) → Alph α i) {j : ℕ}
    (φ₀ : Alph α j → Alph α j) (m : Alph α j) (Y : List (Alph α j)) {B : ℕ}
    (hB : ∀ y ∈ Y ++ [m], (expandTo ℓ'' j [φ₀ y]).length ≤ B) :
    (expandTo (Function.update ℓ'' j (φ₀ m)) (j + 1) [Y.map φ₀]).length ≤
      (Y.length + 1) * B := by
  have hℓ'lt : ∀ t < j, Function.update ℓ'' j (φ₀ m) t = ℓ'' t := fun t ht =>
    Function.update_of_ne (by omega) _ _
  have e1 : expandTo (Function.update ℓ'' j (φ₀ m)) (j + 1) [Y.map φ₀] =
      expandTo ℓ'' j ((Y ++ [m]).map φ₀) := by
    show expandTo _ j (expand (Function.update ℓ'' j (φ₀ m) j) [Y.map φ₀]) = _
    rw [expandTo_congr j hℓ'lt, Function.update_self]
    simp [expand]
  rw [e1]
  refine (length_expandTo_le ℓ'' j (B := B) _ ?_).trans ?_
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact hB y hy
  · rw [List.length_map, List.length_append, List.length_singleton]

/-- Compression of a support of level `j` inside a fixed original hierarchy. Every
duplicate-free list `E` of letters of `u_j` has a new marker sequence `ℓ'` and a letter map `φ`
that agree with the canonical tower on `E`, keep `E` admissible, and make each letter of `E`
expand to at most `descentFactor N d g ^ j` letters. The supports of the recursive calls are
deduplicated, and the identity base case needs no bound on the level-zero alphabet. -/
theorem shorten_level_supported (D0 : Lettered α Q) [Fintype Q]
    [DecidableEq α] [Inhabited α] {w : List α} (hw : w ≠ [])
    {d g j : ℕ} (hj : j ≤ d) (hg : PositiveDictionaryBound w j g)
    (E : List (Alph α j)) (hE : E.Nodup)
    (hsub : ∀ x ∈ E, x ∈ hierOf w j) :
    ∃ (ℓ' : (i : ℕ) → Alph α i) (φ : Alph α j → Alph α j),
      Agree (tower D0 (markOf w) j) (tower D0 ℓ' j) φ E ∧
      Admissible ℓ' j (E.map φ) ∧
      ∀ x ∈ E, (expandTo ℓ' j [φ x]).length ≤
        descentFactor (Fintype.card Q) d g ^ j := by
  classical
  induction j with
  | zero =>
      exact ⟨markOf w, id, Agree.refl _ _, trivial, fun x _ => by simp [expandTo]⟩
  | succ j ih =>
      let ℓ := markOf w
      have hadm : Admissible ℓ (j + 1) E :=
        admissible_of_subset ℓ (j + 1) E _ (admissible_hierOf hw _)
          (hierOf_ne_nil hw _) hsub
      set N := Fintype.card Q with hN
      set D := tower D0 ℓ j with hD
      obtain ⟨ψ, hψA, hψ⟩ := exists_short_letters D (ℓ j) g E
        (length_le_of_dictionaryBound hg hE hsub)
      rw [card_cores j] at hψ
      set Ebig : List (Alph α j) := (ℓ j :: (E.map ψ).flatten).dedup with hEbig
      have hmemBig : ∀ X ∈ E, ∀ a ∈ ψ X, a ∈ Ebig := fun X hX a ha =>
        List.mem_dedup.mpr (List.mem_cons_of_mem _
          (List.mem_flatten.mpr ⟨ψ X, List.mem_map_of_mem hX, ha⟩))
      have hℓBig : ℓ j ∈ Ebig := List.mem_dedup.mpr List.mem_cons_self
      have hsubBig : ∀ a ∈ Ebig, a ∈ hierOf w j := by
        intro a ha
        rcases List.mem_cons.mp (List.mem_dedup.mp ha) with rfl | ha
        · exact markOf_mem hw j
        · obtain ⟨Y, hY, haY⟩ := List.mem_flatten.mp ha
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
          exact mem_lower_dictionary hw (hsub X hX) ((hψ X hX).1.subset haY)
      obtain ⟨ℓ'', φ₀, hA, hadm'', hsize⟩ :=
        ih (by omega) (fun t ht htd => hg t ht (by omega)) Ebig
          (List.nodup_dedup _) hsubBig
      set ℓ' : (i : ℕ) → Alph α i := Function.update ℓ'' j (φ₀ (ℓ j)) with hℓ'
      have hℓ'j : ℓ' j = φ₀ (ℓ j) := Function.update_self _ _ _
      have hℓ'lt : ∀ t < j, ℓ' t = ℓ'' t := fun t ht =>
        Function.update_of_ne (by omega) _ _
      have htw : tower D0 ℓ' j = tower D0 ℓ'' j := tower_congr D0 j hℓ'lt
      have htw1 : tower D0 ℓ' (j + 1) = der (tower D0 ℓ'' j) (φ₀ (ℓ j)) := by
        show der (tower D0 ℓ' j) (ℓ' j) = _
        rw [htw, hℓ'j]
      refine ⟨ℓ', fun X => (ψ X).map φ₀, ?_, ?_, ?_⟩
      · rw [htw1]
        exact hψA.comp (hA.derive hℓBig (E.map ψ) (by
          intro Y hY a ha
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
          exact hmemBig X hX a ha))
      · exact admissible_update_map ℓ'' φ₀ hℓBig (fun a ha h => hA.inj a ha (ℓ j) hℓBig h)
          hadm'' ψ hmemBig (fun X hX h => hadm.1 X hX ((hψ X hX).1.subset h))
      · intro X hX
        refine (length_expandTo_update_le ℓ'' φ₀ (ℓ j) (ψ X)
          (B := descentFactor N d g ^ j) fun y hy => hsize y ?_).trans ?_
        · rcases List.mem_append.mp hy with h1 | h1
          · exact hmemBig X hX y h1
          · rw [List.mem_singleton.mp h1]
            exact hℓBig
        · rw [pow_succ']
          apply Nat.mul_le_mul_right
          exact (hψ X hX).2.trans_le (colBound_mono_core (by omega) (by omega))

end Levels

section Final
universe u v
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

/-- A hole with a bounded dictionary through a unary level has a short witness.
The unary level is explicit so this theorem does not depend on canonical depth. -/
theorem exists_short_hole_of_dictionary (D0 : Lettered α Q) [Fintype Q]
    {w : List α} {i d g : ℕ} (hw : D0.IsHole w) (hi : i ≤ d)
    (hu : IsUnary (hierOf w i)) (hg : PositiveDictionaryBound w i g) :
    ∃ v, D0.IsHole v ∧ InL d v ∧
      v.length ≤ (Fintype.card Q + d + 1) * descentFactor (Fintype.card Q) d g ^ d := by
  classical
  have hw0 : w ≠ [] := hw.ne_nil
  set N := Fintype.card Q with hN
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hierOf_ne_nil hw0 i)
  have hrep : hierOf w i = List.replicate (hierOf w i).length x :=
    List.eq_replicate_iff.mpr ⟨rfl, fun b hb => hu b hb x hx⟩
  have hv : (tower D0 (markOf w) i).IsHole (hierOf w i) := (isHole_hierOf_iff hw0 D0 i).mpr hw
  obtain ⟨m, -, hmN, hm⟩ := (exists_unary_hole_iff (tower D0 (markOf w) i) x).mp
    ⟨(hierOf w i).length, by rw [← hrep]; exact hv⟩
  rw [card_cores i] at hmN
  obtain ⟨ℓ', φ, hA, hadm', hsize⟩ :=
    shorten_level_supported D0 hw0 hi hg [x] (by simp)
      (fun a ha => by rw [List.mem_singleton.mp ha]; exact hx)
  have hv' : (tower D0 ℓ' i).IsHole (List.replicate m (φ x)) := by
    rw [← List.map_replicate]
    exact (hA.isHole_iff fun a ha => List.mem_singleton.mpr (List.eq_of_mem_replicate ha)).mpr hm
  have hadm₂ : Admissible ℓ' i (List.replicate m (φ x)) :=
    admissible_of_subset ℓ' i _ _ hadm' (by simp) fun a ha => by
      rw [List.eq_of_mem_replicate ha]; exact List.mem_map_of_mem (List.mem_singleton_self x)
  refine ⟨expandTo ℓ' i (List.replicate m (φ x)),
    (isHole_tower_iff D0 ℓ' i _ hadm₂ hv'.ne_nil).mp hv', ⟨i, hi, ?_⟩, ?_⟩
  · rw [(hierOf_expandTo ℓ' i _ hadm₂ hv'.ne_nil).1]
    intro a ha b hb
    rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  · calc (expandTo ℓ' i (List.replicate m (φ x))).length
          ≤ (List.replicate m (φ x)).length * descentFactor N d g ^ i :=
          length_expandTo_le ℓ' i _ fun z hz => by
            rw [List.eq_of_mem_replicate hz]; exact hsize x (List.mem_singleton_self x)
      _ ≤ (N + i) * descentFactor N d g ^ i := by
          rw [List.length_replicate]; exact Nat.mul_le_mul_right _ hmN
      _ ≤ (N + d + 1) * descentFactor N d g ^ d := by
          apply Nat.mul_le_mul (by omega)
          apply Nat.pow_le_pow_right
          · unfold descentFactor colBound
            positivity
          · exact hi

end Final

section Decidable

/-- Unary words are decidable. -/
instance decIsUnary {β : Type*} [DecidableEq β] (u : List β) : Decidable (IsUnary u) :=
  inferInstanceAs (Decidable (∀ a ∈ u, ∀ b ∈ u, a = b))

end Decidable

end DeciNSSE.BoundedDepth
