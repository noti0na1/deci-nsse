import DeciNSSE.Holes.BoundedDepth
import DeciNSSE.Holes.StartCores

/-! # Protected-letter exchange and finite types

Equal closed types permit identifying a letter whose co-alignment partners are protected.
-/
set_option autoImplicit false

namespace DeciNSSE.CoAlignment
open DeciNSSE.Holes
open scoped List
namespace Lettered
variable {Γ C : Type*} (D : Lettered Γ C)

/-- Agreement of self, protected-partner, and initial-label admission rows. -/
structure PairRows (P : Lab Γ C → Lab Γ C → Prop) (Qo U : Set C) (Z : Set Γ) (x y : Γ) :
    Prop where
  self : ∀ q ∈ Qo, ∀ q' ∈ Qo, P (some (q, x)) (some (q', x)) ↔ P (some (q, y)) (some (q', y))
  left : ∀ q ∈ Qo, ∀ c ∈ U, ∀ z ∈ Z, P (some (q, x)) (some (c, z)) ↔ P (some (q, y)) (some (c, z))
  right : ∀ q ∈ Qo, ∀ c ∈ U, ∀ z ∈ Z,
    P (some (c, z)) (some (q, x)) ↔ P (some (c, z)) (some (q, y))
  start : ∀ q ∈ Qo, P none (some (q, x)) ↔ P none (some (q, y))

/-- Equal transitions, target predicates, and both admission tables on the recorded cores. -/
structure SameType (Qo U : Set C) (Z : Set Γ) (x y : Γ) : Prop where
  κ_eq : ∀ q ∈ Qo, D.κ x q = D.κ y q
  tf : ∀ q ∈ Qo, D.Tf q x ↔ D.Tf q y
  rowsΛ : PairRows D.Λ Qo U Z x y
  rowsΛf : PairRows D.Λf Qo U Z x y

variable [DecidableEq Γ]

/-- Equal transitions at source occurrences preserve the full core run. -/
theorem core_identify {Qo : Set C} {v : List Γ} {x y : Γ} (hκ : ∀ q ∈ Qo, D.κ x q = D.κ y q)
    (hQo : ∀ j (hj : j < v.length), v[j] = x → D.core v j ∈ Qo) (j : ℕ) :
    D.core (v.map (identify x y)) j = D.core v j :=
  runPrefix_identify D.coreDFA v x y (fun i hi hx => hκ _ (hQo i hi hx)) j

/-- Identification changes only the letter component of each label. -/
theorem label_identify {v : List Γ} {x y : Γ}
    (hcore : ∀ j, D.core (v.map (identify x y)) j = D.core v j) {j : ℕ} (hj : j < v.length) :
    D.label (v.map (identify x y)) (j + 1) = some (D.core v j, identify x y v[j]) := by
  rw [D.label_succ _ (by simpa using hj), hcore]
  simp

/-- Protected partners ensure that the recorded rows cover every changed comparison. -/
theorem pair_iff {P : Lab Γ C → Lab Γ C → Prop} {Qo U : Set C} {Z : Set Γ} {v : List Γ}
    {x y : Γ} (hP : PairRows P Qo U Z x y) (hpart : ∀ b, b ∉ Z → ¬ CoAligned v x b)
    (hQo : ∀ j (hj : j < v.length), v[j] = x → D.core v j ∈ Qo)
    (hU : ∀ j (hj : j < v.length), v[j] ∈ Z → D.core v j ∈ U)
    (hcore : ∀ j, D.core (v.map (identify x y)) j = D.core v j)
    {s t : ℕ} (hc : IsComp v s t) :
    P (D.label (v.map (identify x y)) s) (D.label (v.map (identify x y)) t) ↔
      P (D.label v s) (D.label v t) := by
  have hst := hc.1
  have ht := hc.2.1
  obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
  have hj : j < v.length := by omega
  rw [D.label_identify hcore hj, D.label_succ v hj]
  rcases s with _ | i
  · simp only [label]
    by_cases hx : v[j] = x
    · have hq := hQo j hj hx
      rw [hx, identify_self_left]
      exact (hP.start _ hq).symm
    · rw [identify_of_ne hx]
  · have hi : i < v.length := by omega
    rw [D.label_identify hcore hi, D.label_succ v hi]
    by_cases hxi : v[i] = x <;> by_cases hxj : v[j] = x
    · have hqi := hQo i hi hxi
      have hqj := hQo j hj hxj
      rw [hxi, hxj, identify_self_left]
      exact (hP.self _ hqi _ hqj).symm
    · have hz : v[j] ∈ Z := by
        by_contra hz
        have hco := coAligned_of_comp hi hj hc (by rw [hxi]; exact Ne.symm hxj)
        rw [hxi] at hco
        exact hpart _ hz hco
      have hqi := hQo i hi hxi
      rw [hxi, identify_self_left, identify_of_ne hxj]
      exact (hP.left _ hqi _ (hU j hj hz) _ hz).symm
    · have hz : v[i] ∈ Z := by
        by_contra hz
        have hco := coAligned_of_comp hi hj hc (by rw [hxj]; exact hxi)
        rw [hxj] at hco
        exact hpart _ hz hco.symm
      have hqj := hQo j hj hxj
      rw [hxj, identify_self_left, identify_of_ne hxi]
      exact (hP.right _ hqj _ (hU i hi hz) _ hz).symm
    · rw [identify_of_ne hxi, identify_of_ne hxj]

/-- Same-type identification preserves holehood when every source partner is protected. -/
theorem isHole_identify {Qo U : Set C} {Z : Set Γ} {v : List Γ} {x y : Γ}
    (hT : D.SameType Qo U Z x y) (hy : y ∉ Z) (hpart : ∀ b, b ∉ Z → ¬ CoAligned v x b)
    (hQo : ∀ j (hj : j < v.length), v[j] = x → D.core v j ∈ Qo)
    (hU : ∀ j (hj : j < v.length), v[j] ∈ Z → D.core v j ∈ U)
    (hv : D.IsHole v) : D.IsHole (v.map (identify x y)) := by
  have hcore := D.core_identify hT.κ_eq hQo
  have hcomp : ∀ s e, IsComp (v.map (identify x y)) s e ↔ IsComp v s e :=
    isComp_identify_iff (fun h => hpart y hy h.symm)
  obtain ⟨⟨c, a, hl, hTf⟩, hE, hI⟩ := hv
  have hn : v ≠ [] := by rintro rfl; simp [label] at hl
  obtain ⟨j, hlen⟩ : ∃ j, v.length = j + 1 :=
    ⟨v.length - 1, by have := List.length_pos_iff.mpr hn; omega⟩
  have hj : j < v.length := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_map, hlen, D.label_identify hcore hj]
    rw [hlen, D.label_succ v hj, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨_, _, rfl, ?_⟩
    by_cases hx : v[j] = x
    · have hq := hQo j hj hx
      rw [hx] at hTf
      rw [hx, identify_self_left]
      exact (hT.tf _ hq).mp hTf
    · rw [identify_of_ne hx]
      exact hTf
  · intro s hs
    rw [List.length_map] at hs ⊢
    rw [D.pair_iff hT.rowsΛf hpart hQo hU hcore (isComp_end v hs)]
    exact hE s hs
  · intro s e hc he
    rw [List.length_map] at he
    have hc' := (hcomp s e).mp hc
    rw [D.pair_iff hT.rowsΛ hpart hQo hU hcore hc']
    exact hI s e hc' he

end Lettered
namespace Lettered
variable {Γ C : Type*} (D : Lettered Γ C)

/-- The four admission tables recorded for one letter and one pair predicate. -/
abbrev RowType (Qo U : Finset C) (Z : Finset Γ) : Type _ :=
  (Qo → Qo → Prop) × (Qo → U → Z → Prop) × (Qo → U → Z → Prop) × (Qo → Prop)

/-- The admission tables of a letter against itself and protected labels. -/
def rowsOf (P : Lab Γ C → Lab Γ C → Prop) (Qo U : Finset C) (Z : Finset Γ) (x : Γ) :
    RowType Qo U Z :=
  (fun q q' => P (some (q.1, x)) (some (q'.1, x)),
    fun q c z => P (some (q.1, x)) (some (c.1, z.1)),
    fun q c z => P (some (c.1, z.1)) (some (q.1, x)),
    fun q => P none (some (q.1, x)))

theorem pairRows_of_rowsOf_eq {P : Lab Γ C → Lab Γ C → Prop} {Qo U : Finset C}
    {Z : Finset Γ} {x y : Γ} (h : rowsOf P Qo U Z x = rowsOf P Qo U Z y) :
    PairRows P (Qo : Set C) (U : Set C) (Z : Set Γ) x y := by
  simp only [rowsOf, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq q' hq' => ?_, fun q hq c hc z hz => ?_, fun q hq c hc z hz => ?_,
    fun q hq => ?_⟩
  · exact Iff.of_eq (congrFun (congrFun h1 ⟨q, hq⟩) ⟨q', hq'⟩)
  · exact Iff.of_eq (congrFun (congrFun (congrFun h2 ⟨q, hq⟩) ⟨c, hc⟩) ⟨z, hz⟩)
  · exact Iff.of_eq (congrFun (congrFun (congrFun h3 ⟨q, hq⟩) ⟨c, hc⟩) ⟨z, hz⟩)
  · exact Iff.of_eq (congrFun h4 ⟨q, hq⟩)

variable [DecidableEq Γ]
/-- Replacing a letter by one of no greater weight cannot increase total weight. -/
theorem sum_map_identify_le (wt : Γ → ℕ) {a b : Γ} (h : wt b ≤ wt a) :
    ∀ v : List Γ, ((v.map (identify a b)).map wt).sum ≤ (v.map wt).sum
  | [] => le_rfl
  | c :: v => by
      simp only [List.map_cons, List.sum_cons]
      have := sum_map_identify_le wt h v
      by_cases hc : c = a
      · subst hc; rw [identify_self_left]; omega
      · rw [identify_of_ne hc]; omega

theorem toFinset_identify_subset {v : List Γ} {a b : Γ} (hab : a ≠ b) (hb : b ∈ v) :
    (v.map (identify a b)).toFinset ⊆ v.toFinset.erase a := by
  intro z hz
  simp only [List.mem_toFinset, List.mem_map] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  by_cases hca : c = a
  · subst hca
    rw [identify_self_left]
    exact Finset.mem_erase.mpr ⟨Ne.symm hab, List.mem_toFinset.mpr hb⟩
  · rw [identify_of_ne hca]
    exact Finset.mem_erase.mpr ⟨hca, List.mem_toFinset.mpr hc⟩

end Lettered
end DeciNSSE.CoAlignment

namespace DeciNSSE.Exchange
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.BoundedDepth
open scoped List
universe u v

section Closed
variable {Γ C : Type*} (D : Lettered Γ C)

/-- Closed ordinary-core transitions, targets, and both sets of admission tables. -/
abbrev ClosedType (Qo U : Finset C) (Z : Finset Γ) : Type _ :=
  (Qo → Qo) × (Qo → Prop) × Lettered.RowType Qo U Z × Lettered.RowType Qo U Z

/-- The type of a letter, with ordinary-core closure recorded in its transition component. -/
def closedType (Qo U : Finset C) (Z : Finset Γ) (hcl : ∀ a, ∀ q ∈ Qo, D.κ a q ∈ Qo) (x : Γ) :
    ClosedType Qo U Z :=
  (fun q => ⟨D.κ x q.1, hcl x q.1 q.2⟩, fun q => D.Tf q.1 x,
    Lettered.rowsOf D.Λ Qo U Z x, Lettered.rowsOf D.Λf Qo U Z x)

theorem sameType_of_closedType_eq {Qo U : Finset C} {Z : Finset Γ}
    {hcl : ∀ a, ∀ q ∈ Qo, D.κ a q ∈ Qo} {x y : Γ}
    (h : closedType D Qo U Z hcl x = closedType D Qo U Z hcl y) :
    D.SameType (Qo : Set C) (U : Set C) (Z : Set Γ) x y := by
  simp only [closedType, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun q hq => congrArg Subtype.val (congrFun h1 ⟨q, hq⟩),
    fun q hq => Iff.of_eq (congrFun h2 ⟨q, hq⟩),
    Lettered.pairRows_of_rowsOf_eq h3, Lettered.pairRows_of_rowsOf_eq h4⟩

instance instFintypeRowType' [DecidableEq C] [DecidableEq Γ] (Qo U : Finset C) (Z : Finset Γ) :
    Fintype (Lettered.RowType Qo U Z) :=
  inferInstance

instance instFintypeClosedType [DecidableEq C] [DecidableEq Γ] (Qo U : Finset C)
    (Z : Finset Γ) : Fintype (ClosedType Qo U Z) :=
  @instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
    (@instFintypeProd _ _ (instFintypeRowType' Qo U Z) (instFintypeRowType' Qo U Z)))

/-- Closed transitions give the factor `|Qo| ^ |Qo|` in the exact type count. -/
theorem card_closedType [DecidableEq C] [DecidableEq Γ] (Qo U : Finset C) (Z : Finset Γ) :
    Fintype.card (ClosedType Qo U Z) = Qo.card ^ Qo.card *
      2 ^ (2 * Qo.card ^ 2 + 4 * Qo.card * U.card * Z.card + 3 * Qo.card) := by
  simp only [ClosedType, Lettered.RowType, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_prop, Fintype.card_coe]
  ring

end Closed

section CoresSets
variable {Q : Type v}

instance instDecEqCores [DecidableEq Q] : ∀ i, DecidableEq (Cores Q i)
  | 0 => (inferInstance : DecidableEq Q)
  | i + 1 => by haveI := instDecEqCores i; exact (inferInstance : DecidableEq (Option (Cores Q i)))

variable [Fintype Q] [DecidableEq Q]

variable (Q) in

/-- The ordinary cores at a hierarchy level. -/
def Qset (i : ℕ) : Finset (Cores Q i) := Finset.univ.filter fun c => isStart i c = false

omit [DecidableEq Q] in
theorem mem_Qset {i : ℕ} {c : Cores Q i} : c ∈ Qset Q i ↔ isStart i c = false := by
  simp [Qset]

omit [DecidableEq Q] in

/-- Every level has exactly as many ordinary cores as the base monitor. -/
theorem card_Qset : ∀ i, (Qset Q i).card = Fintype.card Q
  | 0 => by
      have : Qset Q 0 = Finset.univ := by
        ext c; simp [Qset, isStart]
      rw [this, Finset.card_univ]
  | i + 1 => by
      have h : Qset Q (i + 1) = (Qset Q i).map Function.Embedding.some := by
        ext c
        rw [Finset.mem_map, mem_Qset]
        rcases c with _ | c
        · simp only [isStart, stLift, Bool.true_eq_false, false_iff, not_exists, not_and]
          intro a _ h
          simp at h
        · simp only [isStart, stLift, Function.Embedding.some_apply, Option.some.injEq,
            exists_eq_right, mem_Qset]
      rw [h, Finset.card_map, card_Qset i]

end CoresSets

section Exchange
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

omit [DecidableEq α] [Inhabited α] in

/-- Transitions at every derived level preserve the ordinary cores. -/
theorem isStart_κ_tower (D0 : Lettered α Q) (ℓ : (i : ℕ) → Alph α i) :
    ∀ j (c : Cores Q j) (a : Alph α j), isStart j c = false →
      isStart j ((tower D0 ℓ j).κ a c) = false
  | 0, _, _, _ => rfl
  | j + 1, c, a, h => stLift_closed (tower D0 ℓ j) (ℓ j) (isStart j) (isStart_κ_tower D0 ℓ j) c a h

variable [Fintype Q] [DecidableEq Q]

/-- All ordinary cores together with the start cores used by the level word. -/
def Uset (D0 : Lettered α Q) (w : List α) (i : ℕ) : Finset (Cores Q i) :=
  Qset Q i ∪ (Finset.range (sCount D0 w i)).image ((tower D0 (markOf w) i).core (hierOf w i))

theorem card_Uset_le (D0 : Lettered α Q) (w : List α) (i : ℕ) :
    (Uset D0 w i).card ≤ Fintype.card Q + sCount D0 w i := by
  refine (Finset.card_union_le _ _).trans ?_
  rw [card_Qset]
  exact Nat.add_le_add_left (Finset.card_image_le.trans (by simp)) _

/-- The closed exchange type relative to a protected dictionary. -/
def exType (D0 : Lettered α Q) (w : List α) (i : ℕ) (Z : Finset (Alph α i)) (x : Alph α i) :
    ClosedType (Qset Q i) (Uset D0 w i) Z :=
  closedType (tower D0 (markOf w) i) (Qset Q i) (Uset D0 w i) Z
    (fun a q hq => mem_Qset.mpr (isStart_κ_tower D0 (markOf w) i q a (mem_Qset.mp hq))) x

theorem sameType_of_exType_eq (D0 : Lettered α Q) {w : List α} {i : ℕ} {Z : Finset (Alph α i)}
    {x y : Alph α i} (h : exType D0 w i Z x = exType D0 w i Z y) :
    (tower D0 (markOf w) i).SameType (Qset Q i : Set (Cores Q i)) (Uset D0 w i : Set (Cores Q i))
      (Z : Set (Alph α i)) x y :=
  sameType_of_closedType_eq _ h

/-- The finite number of types with `N` ordinary cores, `m` used cores, and `z` protected letters. -/
def typeBound (N m z : ℕ) : ℕ := N ^ N * 2 ^ (2 * N ^ 2 + 4 * N * m * z + 3 * N)

/-- The number of exchange types depends only on the ordinary, used, and protected counts. -/
theorem card_exType_le (D0 : Lettered α Q) (w : List α) (i : ℕ) (Z : Finset (Alph α i)) :
    Fintype.card (ClosedType (Qset Q i) (Uset D0 w i) Z) ≤
      typeBound (Fintype.card Q) (Fintype.card Q + sCount D0 w i) Z.card := by
  rw [card_closedType, card_Qset, typeBound]
  have hU := card_Uset_le D0 w i
  gcongr

/-- The final marker and the letters in the start prefix are protected. -/
def Pset {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α] (D0 : Lettered α Q)
    (w : List α) (j : ℕ) : Finset (Alph α j) :=
  insert (markOf w j) ((hierOf w j).take (sCount D0 w j)).toFinset

/-- An occurring unprotected letter with no unprotected nonterminal partner. -/
def Isolated {Γ : Type*} (v : List Γ) (P : Finset Γ) (x : Γ) : Prop :=
  x ∈ v ∧ x ∉ P ∧ ∀ y, y ∈ v → y ∉ P → ¬ CoAlignedNT v x y

omit [Fintype Q] [DecidableEq Q] in
/-- The protected alphabet has at most one letter beyond the start prefix. -/
theorem card_Pset_le (D0 : Lettered α Q) (w : List α) (j : ℕ) :
    (Pset D0 w j).card ≤ 1 + sCount D0 w j := by
  unfold Pset
  refine (Finset.card_insert_le _ _).trans ?_
  have h1 := List.toFinset_card_le ((hierOf w j).take (sCount D0 w j))
  have h2 : ((hierOf w j).take (sCount D0 w j)).length ≤ sCount D0 w j := by simp
  omega

omit [DecidableEq Q] in
/-- Every occurrence outside the protected prefix is read from an ordinary core. -/
theorem core_mem_Qset_of_not_mem_Pset (D0 : Lettered α Q) {w : List α}
    (hw : w ≠ []) (i j : ℕ) (hj : j < (hierOf w i).length)
    (hx : (hierOf w i)[j] ∉ Pset D0 w i) :
    (tower D0 (markOf w) i).core (hierOf w i) j ∈ Qset Q i := by
  rw [mem_Qset]
  by_contra h
  rw [Bool.not_eq_false] at h
  have hs := ((startCore_invariants D0 hw i).1 j hj).mp h
  apply hx
  apply Finset.mem_insert_of_mem
  apply List.mem_toFinset.mpr
  have hj' : j < ((hierOf w i).take (sCount D0 w i)).length := by simp; omega
  have := List.getElem_mem hj'
  rwa [List.getElem_take] at this

/-- All cores used at letter positions belong to the used-core set. -/
theorem core_mem_Uset (D0 : Lettered α Q) {w : List α} (hw : w ≠ [])
    (i j : ℕ) (hj : j < (hierOf w i).length) :
    (tower D0 (markOf w) i).core (hierOf w i) j ∈ Uset D0 w i := by
  apply Finset.mem_union.mpr
  rcases Nat.lt_or_ge j (sCount D0 w i) with h | h
  · exact Or.inr (Finset.mem_image_of_mem _ (Finset.mem_range.mpr h))
  · apply Or.inl
    rw [mem_Qset]
    by_contra hs
    rw [Bool.not_eq_false] at hs
    have := ((startCore_invariants D0 hw i).1 j hj).mp hs
    omega

omit [Fintype Q] [DecidableEq Q] in
/-- Protecting the final marker turns isolation into protection of every partner. -/
theorem Isolated.partners_protected {w : List α} (hw : w ≠ []) (D0 : Lettered α Q)
    {i : ℕ} {x : Alph α i} (hx : Isolated (hierOf w i) (Pset D0 w i) x) :
    ∀ b, b ∉ (Pset D0 w i : Set (Alph α i)) → ¬ CoAligned (hierOf w i) x b := by
  intro b hb hco
  have hlast : ∀ c, (hierOf w i).getLast? = some c → c ∈ (Pset D0 w i : Set (Alph α i)) := by
    intro c hc
    rw [getLast?_hierOf hw i, Option.some.injEq] at hc
    rw [← hc]
    exact Finset.mem_insert_self _ _
  have hnt := coAlignedNT_of_coAligned hco
    (fun he => hx.2.1 (hlast x he)) (fun he => hb (hlast b he))
  exact hx.2.2 b (coAlignedNT_mem hnt).2 hb hnt

/-- An isolated letter of the same closed type can be merged without changing the core run. -/
theorem isolated_merge (D0 : Lettered α Q) {w : List α} (hw : D0.IsHole w)
    {i : ℕ} {x y : Alph α i}
    (hx : Isolated (hierOf w i) (Pset D0 w i) x) (hy : y ∉ Pset D0 w i)
    (ht : exType D0 w i (Pset D0 w i) x = exType D0 w i (Pset D0 w i) y) :
    (tower D0 (markOf w) i).IsHole ((hierOf w i).map (identify x y)) ∧
    (∀ k, (tower D0 (markOf w) i).core ((hierOf w i).map (identify x y)) k =
      (tower D0 (markOf w) i).core (hierOf w i) k) := by
  have hT := sameType_of_exType_eq D0 ht
  have hQ : ∀ j (hj : j < (hierOf w i).length), (hierOf w i)[j] = x →
      (tower D0 (markOf w) i).core (hierOf w i) j ∈ (Qset Q i : Set (Cores Q i)) := by
    intro j hj he
    exact core_mem_Qset_of_not_mem_Pset D0 hw.ne_nil i j hj (he ▸ hx.2.1)
  exact ⟨(tower D0 (markOf w) i).isHole_identify hT hy (hx.partners_protected hw.ne_nil D0)
    hQ (fun j hj _ => core_mem_Uset D0 hw.ne_nil i j hj)
    ((isHole_hierOf_iff hw.ne_nil D0 i).mpr hw),
    (tower D0 (markOf w) i).core_identify hT.κ_eq hQ⟩

end Exchange
end DeciNSSE.Exchange
