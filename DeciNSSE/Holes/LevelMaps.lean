import DeciNSSE.Holes.Exchange
import DeciNSSE.Holes.Depth

/-! # Shape preservation under level maps

Comparison-preserving maps with images in the original dictionary preserve
canonical depth and cannot increase any dictionary.

## Main declarations

- `NoCollapse`: maps that identify no boundary pair.
- `hierOf_add_of_map`, `isUnary_add_iff_of_map`: the hierarchy above a mapped level.
- `LevelMapResult`, `levelMap_spec`: holehood, dictionary containment, and canonical shape.

The declarations are in the namespace `DeciNSSE.LevelMaps`.
-/
namespace DeciNSSE.LevelMaps
open DeciNSSE.Holes DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy
open DeciNSSE.BoundedDepth DeciNSSE.HierarchyDepth DeciNSSE.Exchange
open scoped List
universe u v
section NoCollapse
variable {β γ : Type*}

/-- The map identifies no unequal predecessor pair of a comparison. -/
def NoCollapse (F : β → γ) (u : List β) : Prop :=
  ∀ s e (hs : s < u.length) (he : e < u.length), s < e → IsComp u (s + 1) (e + 1) →
    F u[s] = F u[e] → u[s] = u[e]

/-- A map that collapses no boundary pair preserves and reflects comparisons. -/
theorem NoCollapse.isComp_iff {F : β → γ} {u : List β} (h : NoCollapse F u) (s e : ℕ) :
    IsComp (u.map F) s e ↔ IsComp u s e :=
  isComp_map_iff F u h s e

/-- A map that preserves and reflects comparisons collapses no boundary pair. -/
theorem noCollapse_of_isComp_iff {F : β → γ} {u : List β}
    (h : ∀ s e, IsComp (u.map F) s e ↔ IsComp u s e) : NoCollapse F u := by
  intro s e hs he hse hc hF
  have h1 : IsComp (u.map F) s e := by
    refine ⟨hse, by simp; omega, ?_⟩
    rw [drop_prefix_iff_succ (u.map F) hse (by simpa using he)]
    simp only [List.getElem_map]
    exact ⟨hF.symm, by rw [← List.map_drop, ← List.map_drop]; exact hc.2.2.map F⟩
  have h2 := ((h s e).mp h1).2.2
  rw [drop_prefix_iff_succ u hse he] at h2
  exact h2.1.symm

/-- A comparison-preserving map reflects the final marker on the word alphabet. -/
theorem NoCollapse.reflect_last {F : β → γ} {u : List β} (h : NoCollapse F u) {ℓ : β}
    (hℓ : u.getLast? = some ℓ) : ∀ a ∈ u, F a = F ℓ → a = ℓ := by
  intro a ha hFa
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem ha
  have hn : 0 < u.length := by omega
  have hlast : u[u.length - 1]'(by omega) = ℓ := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hℓ
    exact Option.some.inj hℓ
  by_cases hse : s = u.length - 1
  · subst hse; exact hlast
  · have hlt : s < u.length - 1 := by omega
    have hc : IsComp u (s + 1) (u.length - 1 + 1) := by
      rw [show u.length - 1 + 1 = u.length by omega]
      exact isComp_end u (by omega)
    rw [h s (u.length - 1) hs (by omega) hlt hc (by rw [hlast]; exact hFa), hlast]

end NoCollapse

section Cut
variable {Γ : Type*} [DecidableEq Γ]

/-- Reflecting the marker suffices for cutting to commute with a letter map. -/
theorem cutAt_map_reflect {Γ' : Type*} [DecidableEq Γ'] (f : Γ → Γ') {ℓ : Γ} {u : List Γ}
    (hf : ∀ a ∈ u, f a = f ℓ → a = ℓ) :
    cutAt (f ℓ) (u.map f) = (cutAt ℓ u).map (List.map f) := by
  obtain ⟨v, t, rfl, ht, hv⟩ := exists_expand_append ℓ u
  have hmap : (expand ℓ v ++ t).map f = expand (f ℓ) (v.map (List.map f)) ++ t.map f := by
    simp only [expand, List.map_append, List.map_flatMap, List.flatMap_map]
    rfl
  rw [cutAt_expand_append ht hv, hmap, cutAt_expand_append]
  · simp only [List.mem_map, not_exists, not_and]
    intro a ha hfa
    have := hf a (by simp [ha]) hfa
    exact ht (this ▸ ha)
  · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rintro X hX ⟨a, ha, hfa⟩
    have hXu : X ⊆ expand ℓ v ++ t := by
      intro b hb
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨X, hX, by simp [hb]⟩)
    have := hf a (hXu ha) hfa
    exact hv X hX (this ▸ ha)

omit [DecidableEq Γ] in
/-- `σ_ℓ(V)[P_k:] = σ_ℓ(V[k:])`. -/
theorem drop_expand_cutP (ℓ : Γ) (V : List (List Γ)) (k : ℕ) :
    (expand ℓ V).drop (cutP ℓ V k) = expand ℓ (V.drop k) := by
  have h : expand ℓ V = expand ℓ (V.take k) ++ expand ℓ (V.drop k) := by
    rw [← expand_append, List.take_append_drop]
  rw [h]; exact List.drop_left' rfl

/-- Comparison preservation passes to the next packet alphabet. -/
theorem noCollapse_cutAt {Γ' : Type*} {F : Γ → Γ'} {ℓ : Γ} {u : List Γ}
    (hu : u.getLast? = some ℓ) (h : NoCollapse F u) : NoCollapse (List.map F) (cutAt ℓ u) := by
  intro s e hs he hse hc hFe
  set V := cutAt ℓ u with hV
  have hexp : expand ℓ V = u := expand_cutAt hu
  have hav : ∀ X ∈ V, ℓ ∉ X := avoid_cutAt ℓ u
  have hlt : cutP ℓ V s < cutP ℓ V e := by
    have h1 := cutP_succ ℓ V s hs
    have h2 := cutP_mono ℓ V (show s + 1 ≤ e by omega)
    omega
  have hle : cutP ℓ V e ≤ u.length := by rw [← hexp]; exact cutP_le_length ℓ V e
  have hdrop : ∀ k (hk : k < V.length),
      u.drop (cutP ℓ V k) = V[k] ++ ℓ :: expand ℓ (V.drop (k + 1)) := by
    intro k hk
    rw [← hexp, drop_expand_cutP, List.drop_eq_getElem_cons hk, expand_cons]
  have hcF : IsComp (u.map F) (cutP ℓ V s) (cutP ℓ V e) := by
    refine ⟨hlt, by simpa using hle, ?_⟩
    rw [← List.map_drop, ← List.map_drop, hdrop e he, hdrop s hs]
    simp only [List.map_append, List.map_cons]
    rw [hFe]
    refine (List.prefix_append_right_inj _).mpr ((List.prefix_cons_inj _).mpr ?_)
    obtain ⟨t, ht⟩ := hc.2.2
    refine ⟨(expand ℓ t).map F, ?_⟩
    rw [← List.map_append, ← expand_append, ht]
  have hcu := ((h.isComp_iff _ _).mp hcF).2.2
  rw [hdrop e he, hdrop s hs] at hcu
  exact ((mark_prefix_iff (hav _ (List.getElem_mem _))
    (hav _ (List.getElem_mem _))).mp hcu).1.symm

/-- Cutting a power of the marker gives empty blocks. -/
theorem cutAt_replicate (ℓ : Γ) : ∀ n, cutAt ℓ (List.replicate n ℓ) = List.replicate n []
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, cutAt, cutAt_replicate ℓ n]

end Cut

section
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

/-- Unary levels stay unary after cutting. -/
theorem isUnary_hierOf_succ {w : List α} {k : ℕ} (h : IsUnary (hierOf w k)) :
    IsUnary (hierOf w (k + 1)) := by
  rw [hierOf_succ]
  by_cases hn : hierOf w k = []
  · rw [hn]; intro a ha; simp [cutAt] at ha
  · have hm := List.mem_of_getLast? (getLast?_hierOf_of_ne_nil hn)
    have hrep : hierOf w k = List.replicate (hierOf w k).length (markOf w k) :=
      List.eq_replicate_iff.mpr ⟨rfl, fun b hb => h b hb _ hm⟩
    rw [hrep, cutAt_replicate]
    intro a ha b hb
    rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]

/-- Unary levels stay unary above. -/
theorem isUnary_hierOf_of_le {w : List α} {k : ℕ} (h : IsUnary (hierOf w k)) :
    ∀ k', k ≤ k' → IsUnary (hierOf w k') := by
  intro k' hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => exact h
  | succ d ih => exact isUnary_hierOf_succ (ih (by omega))

/-- Part of the API: a level is unary exactly from the canonical depth on. -/
theorem isUnary_iff_depth_le (w : List α) (k : ℕ) : IsUnary (hierOf w k) ↔ depth w ≤ k :=
  ⟨depth_le_of_isUnary, fun h => isUnary_hierOf_of_le (isUnary_depth w) k h⟩

/-- Words with the same unary levels have the same canonical depth. -/
theorem depth_eq_of_isUnary_iff {w w' : List α}
    (h : ∀ k, IsUnary (hierOf w' k) ↔ IsUnary (hierOf w k)) : depth w' = depth w := by
  refine le_antisymm (depth_le_of_isUnary ((h _).mpr (isUnary_depth w)))
    (depth_le_of_isUnary ((h _).mp (isUnary_depth w')))

/-- Iterate a letter map through the nested packet alphabets. -/
def liftMap {j j' : ℕ} (φ : Alph α j' → Alph α j) : (r : ℕ) → Alph α (j' + r) → Alph α (j + r)
  | 0 => φ
  | r + 1 => List.map (liftMap φ r)

end
section LevelMap
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

/-- Alphabet containment descends through common markers. -/
theorem mem_hierOf_sub {w₁ w₀ : List α} (h₁ : w₁ ≠ []) (h₀ : w₀ ≠ []) (j : ℕ)
    (hm : ∀ i < j, markOf w₁ i = markOf w₀ i)
    (htop : ∀ a ∈ hierOf w₁ j, a ∈ hierOf w₀ j) :
    ∀ i ≤ j, ∀ a ∈ hierOf w₁ i, a ∈ hierOf w₀ i := by
  suffices H : ∀ d i, i + d = j → ∀ a ∈ hierOf w₁ i, a ∈ hierOf w₀ i from
    fun i hi => H (j - i) i (by omega)
  intro d
  induction d with
  | zero =>
    intro i hi
    obtain rfl : i = j := by omega
    exact htop
  | succ d ih =>
    intro i hi a ha
    have hup := ih (i + 1) (by omega)
    rw [← expand_hierOf h₁ i] at ha
    rw [← expand_hierOf h₀ i, ← hm i (by omega)]
    obtain ⟨X, hX, haX⟩ := mem_expand.mp ha
    rw [List.mem_append, List.mem_singleton] at haX
    rcases haX with haX | rfl
    · exact mem_expand.mpr ⟨X, hup X hX, List.mem_append_left _ haX⟩
    · obtain ⟨Y, hY⟩ := List.exists_mem_of_ne_nil _ (hierOf_ne_nil h₀ (i + 1))
      exact mem_expand.mpr ⟨Y, hY, by simp⟩

omit [DecidableEq α] [Inhabited α] in

/-- Decoded length is the sum of the decoded lengths of individual letters. -/
theorem length_expandTo_eq_sum (ℓ : (i : ℕ) → Alph α i) (j : ℕ) :
    ∀ u : List (Alph α j),
      (expandTo ℓ j u).length = (u.map fun a => (expandTo ℓ j [a]).length).sum
  | [] => by simp [expandTo_nil]
  | a :: u => by
      rw [show a :: u = [a] ++ u from rfl, expandTo_append, List.length_append,
        length_expandTo_eq_sum ℓ j u]
      simp

/-- Holehood, dictionary containment, and canonical shape preserved by a level map. -/
structure LevelMapResult (D0 : Lettered α Q) (w : List α) (i : ℕ) (f : Alph α i → Alph α i)
    (w' : List α) : Prop where
  /-- The decoded word is a hole. -/
  hole : D0.IsHole w'
  /-- Lower alphabets only lose letters. -/
  mem_le : ∀ k ≤ i, ∀ a ∈ hierOf w' k, a ∈ hierOf w k
  /-- Higher level words are images under iterated letter maps. -/
  level : ∀ r, hierOf w' (i + r) = (hierOf w (i + r)).map (liftMap f r)
  /-- Exactly the same levels are unary. -/
  unary_iff : ∀ k, IsUnary (hierOf w' k) ↔ IsUnary (hierOf w k)

/-- Above the mapped level, the hierarchy of `w'` is the image of that of `w` under the
iterated maps, none of which collapses a boundary pair. -/
theorem hierOf_add_of_map {w w' : List α} (hw0 : w ≠ []) {i : ℕ} {f : Alph α i → Alph α i}
    (hlev : hierOf w' i = (hierOf w i).map f) (hcol : NoCollapse f (hierOf w i)) :
    ∀ r, hierOf w' (i + r) = (hierOf w (i + r)).map (liftMap f r) ∧
      NoCollapse (liftMap f r) (hierOf w (i + r)) := by
  intro r
  induction r with
  | zero => exact ⟨hlev, hcol⟩
  | succ r ih =>
    obtain ⟨hr, hc⟩ := ih
    have hlast := getLast?_hierOf hw0 (i + r)
    have hmr : markOf w' (i + r) = liftMap f r (markOf w (i + r)) := by
      rw [markOf, hr, List.getLastD_eq_getLast?, List.getLast?_map, hlast]
      rfl
    refine ⟨?_, noCollapse_cutAt hlast hc⟩
    show cutAt (markOf w' (i + r)) (hierOf w' (i + r)) =
      (cutAt (markOf w (i + r)) (hierOf w (i + r))).map (List.map (liftMap f r))
    rw [hmr, hr, cutAt_map_reflect _ (hc.reflect_last hlast)]

/-- Above the mapped level, exactly the same levels of `w'` and `w` are unary. -/
theorem isUnary_add_iff_of_map {w w' : List α} (hw0 : w ≠ []) {i : ℕ}
    {f : Alph α i → Alph α i}
    (hup : ∀ r, hierOf w' (i + r) = (hierOf w (i + r)).map (liftMap f r) ∧
      NoCollapse (liftMap f r) (hierOf w (i + r))) (r : ℕ) :
    IsUnary (hierOf w' (i + r)) ↔ IsUnary (hierOf w (i + r)) := by
  rw [(hup r).1]
  constructor
  · intro h a ha b hb
    have hl := getLast?_hierOf hw0 (i + r)
    have hm := markOf_mem hw0 (i + r)
    have hF : ∀ c ∈ hierOf w (i + r), c = markOf w (i + r) := fun c hc =>
      (hup r).2.reflect_last hl c hc
        (h _ (List.mem_map_of_mem hc) _ (List.mem_map_of_mem hm))
    rw [hF a ha, hF b hb]
  · intro h a ha b hb
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    rw [h a' ha' b' hb']

/-- A comparison-preserving level map within the dictionary preserves canonical shape. -/
theorem levelMap_spec (D0 : Lettered α Q) {w : List α} (hw : D0.IsHole w) (i : ℕ)
    (f : Alph α i → Alph α i) (hcol : NoCollapse f (hierOf w i))
    (hhole : (tower D0 (markOf w) i).IsHole ((hierOf w i).map f))
    (hsub : ∀ a ∈ hierOf w i, f a ∈ hierOf w i) :
    LevelMapResult D0 w i f (expandTo (markOf w) i ((hierOf w i).map f)) := by
  have hw0 : w ≠ [] := hw.ne_nil
  have hvne : (hierOf w i).map f ≠ [] := by simpa using hierOf_ne_nil hw0 i
  have hadm : Admissible (markOf w) i ((hierOf w i).map f) :=
    admissible_of_subset _ i _ (hierOf w i) (admissible_hierOf hw0 i) (hierOf_ne_nil hw0 i)
      (fun a ha => by obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; exact hsub b hb)
  have hhole' : D0.IsHole (expandTo (markOf w) i ((hierOf w i).map f)) :=
    (isHole_tower_iff D0 (markOf w) i _ hadm hvne).mp hhole
  set w' := expandTo (markOf w) i ((hierOf w i).map f) with hw'
  have hw'0 : w' ≠ [] := hhole'.ne_nil
  obtain ⟨hlev, hmk⟩ := hierOf_expandTo (markOf w) i ((hierOf w i).map f) hadm hvne
  rw [← hw'] at hlev hmk
  have hup := hierOf_add_of_map hw0 hlev hcol
  have hunary : ∀ k, IsUnary (hierOf w' k) ↔ IsUnary (hierOf w k) := by
    intro k
    rcases Nat.lt_or_ge k i with hk | hk
    · by_cases hi : IsUnary (hierOf w i)
      · -- `f` is the identity on the letters of a unary `u_i`, so `w' = w`
        have hm := markOf_mem hw0 i
        have hfm : f (markOf w i) = markOf w i := hi _ (hsub _ hm) _ hm
        have hid : (hierOf w i).map f = hierOf w i := by
          conv_rhs => rw [← List.map_id (hierOf w i)]
          exact List.map_congr_left (fun a ha => by rw [hi a ha _ hm, hfm]; rfl)
        have : w' = w := by rw [hw', hid, expandTo_hierOf hw0 i]
        rw [this]
      · have h1 : ¬ IsUnary (hierOf w k) := fun h => hi (isUnary_hierOf_of_le h i hk.le)
        have h2 : ¬ IsUnary (hierOf w' k) := fun h =>
          hi ((isUnary_add_iff_of_map hw0 hup 0).mp (isUnary_hierOf_of_le h i hk.le))
        exact iff_of_false h2 h1
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact isUnary_add_iff_of_map hw0 hup r
  have hmem : ∀ k ≤ i, ∀ a ∈ hierOf w' k, a ∈ hierOf w k := by
    refine mem_hierOf_sub hw'0 hw0 i hmk ?_
    rw [hlev]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hsub b hb
  exact ⟨hhole', hmem, fun r => (hup r).1, hunary⟩

/-- Preserving all unary levels preserves canonical depth. -/
theorem LevelMapResult.depth_eq {D0 : Lettered α Q} {w w' : List α} {i : ℕ}
    {f : Alph α i → Alph α i} (h : LevelMapResult D0 w i f w') : depth w' = depth w :=
  depth_eq_of_isUnary_iff h.unary_iff

end LevelMap
end DeciNSSE.LevelMaps
