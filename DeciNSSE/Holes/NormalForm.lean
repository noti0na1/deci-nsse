import DeciNSSE.Holes.LevelMaps
import DeciNSSE.Holes.BoundaryPairs

/-! # Normal forms obtained by isolated-letter merging

Merging equal-type isolated letters decreases the sum of dictionary sizes.
Choosing the shorter expansion as representative also preserves the length bound.
-/

set_option autoImplicit false

namespace DeciNSSE.NormalForm
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.BoundedDepth
open DeciNSSE.HierarchyDepth DeciNSSE.Exchange DeciNSSE.LevelMaps
open DeciNSSE.BoundaryPairs DeciNSSE.StartCores
open scoped List

universe u v
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

/-- The number of distinct letters at a canonical level. -/
def alphCard (w : List α) (i : ℕ) : ℕ := (hierOf w i).toFinset.card

/-- The base length represented by a single level letter. -/
def letterWeight (w : List α) (i : ℕ) (x : Alph α i) : ℕ :=
  (expandTo (markOf w) i [x]).length

/-- A level map never increases any canonical dictionary. -/
theorem alphCard_le_of_levelMap {D0 : Lettered α Q} {w w' : List α} {i : ℕ}
    {f : Alph α i → Alph α i} (h : LevelMapResult D0 w i f w') (j : ℕ) :
    alphCard w' j ≤ alphCard w j := by
  rcases Nat.lt_or_ge j i with hj | hj
  · exact Finset.card_le_card (fun a ha => List.mem_toFinset.mpr
      (h.mem_le j hj.le a (List.mem_toFinset.mp ha)))
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
    unfold alphCard
    rw [h.level r]
    have heq : ((hierOf w (i + r)).map (liftMap f r)).toFinset =
        (hierOf w (i + r)).toFinset.image (liftMap f r) := by ext a; simp
    rw [heq]
    exact Finset.card_image_le

variable [Fintype Q] [DecidableEq Q]

/-- An isolated merge preserves shape, decreases its dictionary, and can preserve length. -/
theorem isolated_merge_spec {D0 : Lettered α Q} {w : List α} {i : ℕ} {x y : Alph α i}
    (hw : D0.IsHole w) (_hi : 1 ≤ i) (_hid : i < depth w)
    (hx : Isolated (hierOf w i) (Pset D0 w i) x)
    (hy : Isolated (hierOf w i) (Pset D0 w i) y) (hxy : x ≠ y)
    (ht : exType D0 w i (Pset D0 w i) x = exType D0 w i (Pset D0 w i) y)
    (hlen : letterWeight w i y ≤ letterWeight w i x) :
    let w' := expandTo (markOf w) i ((hierOf w i).map (identify x y))
    LevelMapResult D0 w i (identify x y) w' ∧
    w'.length ≤ w.length ∧ (∀ j, alphCard w' j ≤ alphCard w j) ∧
      alphCard w' i < alphCard w i := by
  dsimp only
  obtain ⟨hhole, hcore⟩ := isolated_merge D0 hw hx hy.2.1 ht
  have hcomp : ∀ s e, IsComp ((hierOf w i).map (identify x y)) s e ↔
      IsComp (hierOf w i) s e :=
    isComp_identify_iff (fun h => hx.partners_protected hw.ne_nil D0 y hy.2.1 h.symm)
  have hsub : ∀ a ∈ hierOf w i, identify x y a ∈ hierOf w i := by
    intro a ha
    by_cases hax : a = x
    · rw [hax, identify_self_left]; exact hy.1
    · rw [identify_of_ne hax]; exact ha
  have hpre : ∀ a ∈ (hierOf w i).take (sCount D0 w i), identify x y a = a := by
    intro a ha
    apply identify_of_ne
    intro he
    apply hx.2.1
    rw [← he]
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr ha)
  have hres := levelMap_spec D0 hw i (identify x y) (noCollapse_of_isComp_iff hcomp)
    hhole hsub hpre hcore
  refine ⟨hres, ?_, alphCard_le_of_levelMap hres, ?_⟩
  · rw [length_expandTo_eq_sum]
    have h := Lettered.sum_map_identify_le (letterWeight w i) hlen (hierOf w i)
    have hlenw : ((hierOf w i).map (letterWeight w i)).sum = w.length := by
      unfold letterWeight
      rw [← length_expandTo_eq_sum (markOf w) i, expandTo_hierOf hw.ne_nil i]
    exact h.trans_eq hlenw
  · unfold alphCard
    have hlev : hierOf (expandTo (markOf w) i ((hierOf w i).map (identify x y))) i =
        (hierOf w i).map (identify x y) := hres.level 0
    rw [hlev]
    have hsub' := Lettered.toFinset_identify_subset hxy hy.1
    have hlt := Finset.card_erase_lt_of_mem (List.mem_toFinset.mpr hx.1)
    exact lt_of_le_of_lt (Finset.card_le_card hsub') hlt

/-- At this level, distinct isolated letters have distinct protected exchange types. -/
def NormalAt (D0 : Lettered α Q) (w : List α) (i : ℕ) : Prop :=
  ∀ x y, Isolated (hierOf w i) (Pset D0 w i) x →
    Isolated (hierOf w i) (Pset D0 w i) y →
    exType D0 w i (Pset D0 w i) x = exType D0 w i (Pset D0 w i) y → x = y

/-- Every positive non-unary level is normal. -/
def Normal (D0 : Lettered α Q) (w : List α) : Prop :=
  ∀ i, 1 ≤ i → i < depth w → NormalAt D0 w i

/-- The total dictionary size through the first unary level. -/
def dictionaryPotential (w : List α) : ℕ :=
  ∑ i ∈ Finset.range (depth w + 1), alphCard w i

/-- Shrinking one dictionary while preserving depth strictly decreases the potential. -/
theorem dictionaryPotential_lt {w w' : List α} (hd : depth w' = depth w)
    (hle : ∀ j, alphCard w' j ≤ alphCard w j) {i : ℕ} (hi : i ≤ depth w)
    (hlt : alphCard w' i < alphCard w i) : dictionaryPotential w' < dictionaryPotential w := by
  unfold dictionaryPotential
  rw [hd]
  exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_range.mpr (by omega), hlt⟩

/-- Every hole has a normal form of the same depth, with no larger length or dictionary. -/
theorem exists_normal_form {D0 : Lettered α Q} {w : List α} (hw : D0.IsHole w) :
    ∃ w', D0.IsHole w' ∧ depth w' = depth w ∧ w'.length ≤ w.length ∧
      (∀ i, sCount D0 w' i = sCount D0 w i) ∧
      (∀ i, alphCard w' i ≤ alphCard w i) ∧ Normal D0 w' := by
  classical
  suffices H : ∀ n (v : List α), dictionaryPotential v = n → D0.IsHole v →
      ∃ v', D0.IsHole v' ∧ depth v' = depth v ∧ v'.length ≤ v.length ∧
        (∀ i, sCount D0 v' i = sCount D0 v i) ∧
        (∀ i, alphCard v' i ≤ alphCard v i) ∧ Normal D0 v' from H _ w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hvn hv
    by_cases hn : Normal D0 v
    · exact ⟨v, hv, rfl, le_rfl, fun _ => rfl, fun _ => le_rfl, hn⟩
    · simp only [Normal, NormalAt, not_forall] at hn
      obtain ⟨i, hn⟩ := hn
      push Not at hn
      obtain ⟨hi, hid, x, y, hx, hy, ht, hxy⟩ := hn
      have step : ∀ x y : Alph α i,
          Isolated (hierOf v i) (Pset D0 v i) x →
          Isolated (hierOf v i) (Pset D0 v i) y → x ≠ y →
          exType D0 v i (Pset D0 v i) x = exType D0 v i (Pset D0 v i) y →
          letterWeight v i y ≤ letterWeight v i x →
          ∃ v', D0.IsHole v' ∧ depth v' = depth v ∧ v'.length ≤ v.length ∧
            (∀ j, sCount D0 v' j = sCount D0 v j) ∧
            (∀ j, alphCard v' j ≤ alphCard v j) ∧ Normal D0 v' := by
        intro x y hx hy hxy ht hlen
        obtain ⟨hr, hl, hc, hlt⟩ := isolated_merge_spec hv hi hid hx hy hxy ht hlen
        have hp := dictionaryPotential_lt hr.depth_eq hc hid.le hlt
        rw [hvn] at hp
        obtain ⟨v', hv', hd', hl', hs', hc', hn'⟩ := ih _ hp _ rfl hr.hole
        exact ⟨v', hv', hd'.trans hr.depth_eq, hl'.trans hl,
          fun j => (hs' j).trans (hr.sCount_eq j), fun j => (hc' j).trans (hc j), hn'⟩
      rcases le_total (letterWeight v i y) (letterWeight v i x) with hlen | hlen
      · exact step x y hx hy hxy ht hlen
      · exact step y x hy hx hxy.symm ht.symm hlen


/-- The closed exchange-type allowance at depth at most `d`. -/
def normalTypeBound (N d : ℕ) : ℕ := typeBound N (N + d) (d + 1)

/-- Protected letters and isolated types contribute this many letters. -/
def normalAllowance (N d : ℕ) : ℕ := d + 1 + normalTypeBound N d

/-- Normality bounds isolated letters by types, and all remaining letters by boundary endpoints. -/
theorem normalAt_alphCard_le_types {D0 : Lettered α Q} {w : List α} {i : ℕ}
    (hn : NormalAt D0 w i) :
    alphCard w i ≤ (Pset D0 w i).card +
      Fintype.card (ClosedType (Qset Q i) (Uset D0 w i) (Pset D0 w i)) +
      2 * (boundaryPairs (hierOf w i)).card := by
  classical
  let v := hierOf w i
  let P := Pset D0 w i
  let S := v.toFinset.filter (Isolated v P)
  let B := boundaryPairs v
  let E := B.image Prod.fst ∪ B.image Prod.snd
  have hS : S.card ≤ Fintype.card (ClosedType (Qset Q i) (Uset D0 w i) P) := by
    let τ := exType D0 w i P
    have hinj : Set.InjOn τ (S : Set (Alph α i)) := by
      intro x hx y hy he
      exact hn x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 he
    calc
      S.card = (S.image τ).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Fintype.card (ClosedType (Qset Q i) (Uset D0 w i) P) := Finset.card_le_univ _
  have hE : E.card ≤ 2 * B.card := by
    have hu := Finset.card_union_le (B.image Prod.fst) (B.image Prod.snd)
    have h1 : (B.image Prod.fst).card ≤ B.card := Finset.card_image_le
    have h2 : (B.image Prod.snd).card ≤ B.card := Finset.card_image_le
    dsimp only [E]
    omega
  have hsub : v.toFinset ⊆ P ∪ S ∪ E := by
    intro x hx
    have hxv := List.mem_toFinset.mp hx
    by_cases hxp : x ∈ P
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxp)
    by_cases hxi : Isolated v P x
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxi⟩))
    have hh : ¬ ∀ y, y ∈ v → y ∉ P → ¬ CoAlignedNT v x y :=
      fun h => hxi ⟨hxv, hxp, h⟩
    push Not at hh
    obtain ⟨y, _, _, hco⟩ := hh
    apply Finset.mem_union_right
    rcases coAlignedNT_iff.mp hco with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(x, y), h, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(y, x), h, rfl⟩)
  have hcard := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (P ∪ S) E
  have hu2 := Finset.card_union_le P S
  change v.toFinset.card ≤ P.card +
    Fintype.card (ClosedType (Qset Q i) (Uset D0 w i) P) + 2 * B.card
  omega

/-- The dictionary bound charges non-isolated letters additively to boundary pairs. -/
theorem normalAt_alphCard_le {D0 : Lettered α Q} {w : List α} {i d : ℕ}
    (hw : D0.IsHole w) (hn : NormalAt D0 w i) (_hi : 1 ≤ i)
    (hid : i < depth w) (hd : depth w ≤ d) :
    alphCard w i ≤ normalAllowance (Fintype.card Q) d +
      2 * (boundaryPairs (hierOf w i)).card := by
  have hs : sCount D0 w i ≤ d := (sCount_le_level D0 hw.ne_nil i).trans (by omega)
  have hp : (Pset D0 w i).card ≤ d + 1 := (card_Pset_le D0 w i).trans (by omega)
  have ht := card_exType_le D0 w i (Pset D0 w i)
  have htype : Fintype.card (ClosedType (Qset Q i) (Uset D0 w i) (Pset D0 w i)) ≤
      normalTypeBound (Fintype.card Q) d := by
    refine ht.trans ?_
    unfold normalTypeBound typeBound
    gcongr
  have h := normalAt_alphCard_le_types hn
  unfold normalAllowance
  omega

end DeciNSSE.NormalForm
