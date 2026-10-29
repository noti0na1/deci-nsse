import DeciNSSE.Holes.Exchange
import DeciNSSE.Holes.Depth

/-! # Shape preservation under level maps

Maps preserving comparisons and the start prefix preserve the canonical depth
and every start count, including levels where the start prefix is the whole word.
-/
set_option autoImplicit false
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

theorem NoCollapse.isComp_iff {F : β → γ} {u : List β} (h : NoCollapse F u) (s e : ℕ) :
    IsComp (u.map F) s e ↔ IsComp u s e :=
  isComp_map_iff F u h s e

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

theorem coAlignedNT_of_map (F : β → γ) {u : List β}
    (hcomp : ∀ s e, IsComp (u.map F) s e ↔ IsComp u s e) {p q : γ}
    (h : CoAlignedNT (u.map F) p q) : ∃ p0 q0, F p0 = p ∧ F q0 = q ∧ CoAlignedNT u p0 q0 := by
  obtain ⟨hpq, s, e, ⟨hc, hs1, -⟩, hen, hb⟩ := h
  have hc' := (hcomp s e).mp hc
  rw [List.length_map] at hen
  have hs : s - 1 < u.length := by have := hc'.1; have := hc'.2.1; omega
  have he : e - 1 < u.length := by have := hc'.1; have := hc'.2.1; omega
  have hse : s - 1 + 1 = s := by omega
  have hee : e - 1 + 1 = e := by have := hc'.1; omega
  simp only [List.getElem?_map, List.getElem?_eq_getElem hs, List.getElem?_eq_getElem he,
    Option.map_some, Option.some.injEq] at hb
  have hlm : IsLeftMax u s e := by
    refine ⟨hc', hs1, ?_⟩
    rw [List.getElem?_eq_getElem hs, List.getElem?_eq_getElem he]
    intro h'
    have h'' := Option.some.inj h'
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hpq (h1 ▸ h2 ▸ congrArg F h'')
    · exact hpq (h2 ▸ h1 ▸ congrArg F h''.symm)
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨u[s - 1], u[e - 1], h1, h2, ?_, s, e, hlm, hen, Or.inl ⟨?_, ?_⟩⟩
    · intro h'; exact hpq (h1 ▸ h2 ▸ congrArg F h')
    · simp [List.getElem?_eq_getElem hs]
    · simp [List.getElem?_eq_getElem he]
  · refine ⟨u[e - 1], u[s - 1], h2, h1, ?_, s, e, hlm, hen, Or.inr ⟨?_, ?_⟩⟩
    · intro h'; exact hpq (h2 ▸ h1 ▸ congrArg F h')
    · simp [List.getElem?_eq_getElem hs]
    · simp [List.getElem?_eq_getElem he]

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
theorem drop_expand_cutP (ℓ : Γ) (V : List (List Γ)) (k : ℕ) :
    (expand ℓ V).drop (cutP ℓ V k) = expand ℓ (V.drop k) := by
  have h : expand ℓ V = expand ℓ (V.take k) ++ expand ℓ (V.drop k) := by
    rw [← expand_append, List.take_append_drop]
  rw [h]; exact List.drop_left' rfl

omit [DecidableEq Γ] in

theorem eq_of_append_marker_prefix {ℓ : Γ} : ∀ {A B X Y : List Γ}, ℓ ∉ A → ℓ ∉ B →
    A ++ ℓ :: X <+: B ++ ℓ :: Y → A = B
  | [], [], _, _, _, _, _ => rfl
  | [], b :: B, X, Y, _, hB, h => by
      rw [List.nil_append, List.cons_append, List.cons_prefix_cons] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hB
  | a :: A, [], X, Y, hA, _, h => by
      rw [List.nil_append, List.cons_append, List.cons_prefix_cons] at h
      exact absurd (h.1.symm ▸ List.mem_cons_self) hA
  | a :: A, b :: B, X, Y, hA, hB, h => by
      rw [List.cons_append, List.cons_append, List.cons_prefix_cons] at h
      obtain ⟨rfl, h⟩ := h
      rw [eq_of_append_marker_prefix (fun h' => hA (List.mem_cons_of_mem _ h'))
        (fun h' => hB (List.mem_cons_of_mem _ h')) h]

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
  exact (eq_of_append_marker_prefix (hav _ (List.getElem_mem _)) (hav _ (List.getElem_mem _))
    hcu).symm

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

theorem isUnary_hierOf_of_le {w : List α} {k : ℕ} (h : IsUnary (hierOf w k)) :
    ∀ k', k ≤ k' → IsUnary (hierOf w k') := by
  intro k' hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => exact h
  | succ d ih => exact isUnary_hierOf_succ (ih (by omega))

theorem depth_le_of_isUnary {w : List α} {k : ℕ} (hk : IsUnary (hierOf w k)) : depth w ≤ k :=
  Nat.find_min' (exists_isUnary_hierOf w) hk

theorem isUnary_iff_depth_le (w : List α) (k : ℕ) : IsUnary (hierOf w k) ↔ depth w ≤ k :=
  ⟨depth_le_of_isUnary, fun h => isUnary_hierOf_of_le (isUnary_depth w) k h⟩

theorem depth_eq_of_isUnary_iff {w w' : List α}
    (h : ∀ k, IsUnary (hierOf w' k) ↔ IsUnary (hierOf w k)) : depth w' = depth w := by
  refine le_antisymm (depth_le_of_isUnary ((h _).mpr (isUnary_depth w)))
    (depth_le_of_isUnary ((h _).mp (isUnary_depth w')))

/-- Iterate a letter map through the nested packet alphabets. -/
def liftMap {j j' : ℕ} (φ : Alph α j' → Alph α j) : (r : ℕ) → Alph α (j' + r) → Alph α (j + r)
  | 0 => φ
  | r + 1 => List.map (liftMap φ r)
theorem core_take {Γ C : Type*} (D : Lettered Γ C) (u : List Γ) {L x : ℕ} (hx : x ≤ L) :
    D.core (u.take L) x = D.core u x := by
  rw [core_eq_kst, core_eq_kst, List.take_take, Nat.min_eq_left hx]

theorem count_map_of_injOn {β γ : Type*} [DecidableEq β] [DecidableEq γ] (f : β → γ) {a : β} :
    ∀ {l : List β}, (∀ x ∈ l, f x = f a → x = a) → (l.map f).count (f a) = l.count a
  | [], _ => rfl
  | x :: l, h => by
      have ih := count_map_of_injOn f (l := l) (fun y hy => h y (List.mem_cons_of_mem _ hy))
      rw [List.map_cons, List.count_cons, List.count_cons, ih]
      by_cases hx : x = a
      · subst hx; simp
      · have : f x ≠ f a := fun h' => hx (h x List.mem_cons_self h')
        simp [hx, this]
/-- A start prefix covering a whole level also covers the next level. -/
theorem start_cap_up (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (k : ℕ)
    (h : sCount D0 w k = (hierOf w k).length) :
    sCount D0 w (k + 1) = (hierOf w (k + 1)).length := by
  rw [sCount_succ D0 hw k, h, List.take_length, ← expand_hierOf hw k,
    count_expand _ (avoid_hierOf k)]
  omega

theorem sCount_pos (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (k : ℕ) :
    1 ≤ sCount D0 w (k + 1) := by
  rw [sCount_succ D0 hw k]
  have := List.length_pos_iff.mpr (hierOf_ne_nil hw (k + 1))
  omega

end
section StartBelow
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

/-- Equal markers and start prefixes at one level preserve all lower start counts and prefixes. -/
theorem start_below (D0 : Lettered α Q) {w w' : List α} (hw0 : w ≠ []) (hw'0 : w' ≠ [])
    (j : ℕ) (hmk : ∀ i < j, markOf w' i = markOf w i)
    (hpref : (hierOf w' j).take (sCount D0 w j) = (hierOf w j).take (sCount D0 w j))
    (hj : sCount D0 w' j = sCount D0 w j) :
    ∀ i ≤ j, sCount D0 w' i = sCount D0 w i ∧
      (hierOf w' i).take (sCount D0 w i) = (hierOf w i).take (sCount D0 w i) := by
  have htw : ∀ i ≤ j, tower D0 (markOf w') i = tower D0 (markOf w) i :=
    fun i hi => tower_congr D0 i (fun k hk => hmk k (by omega))
  have hpre' : ∀ i ≤ j, ∀ x < (hierOf w' i).length,
      isStart i ((tower D0 (markOf w) i).core (hierOf w' i) x) = true ↔
        x < sCount D0 w' i := by
    intro i hi
    rw [← htw i hi]
    exact (startCore_invariants D0 hw'0 i).1
  have hpre := fun i => (startCore_invariants D0 hw0 i).1

  have hL : ∀ d i, i + d = j → ∃ L, sCount D0 w i ≤ L ∧ L ≤ (hierOf w i).length ∧
      (hierOf w' i).take L = (hierOf w i).take L ∧
      (d = 0 ∨ sCount D0 w i < L ∨ L = (hierOf w i).length) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      obtain rfl : i = j := by omega
      exact ⟨sCount D0 w i, le_rfl, (startCore_invariants D0 hw0 i).2.1, hpref, Or.inl rfl⟩
    | succ d ih =>
      intro i hi
      obtain ⟨L, hsL, hLn, hLeq, -⟩ := ih (i + 1) (by omega)
      have hm := hmk i (by omega)
      have hu := expand_hierOf hw0 i
      have hu' := expand_hierOf hw'0 i
      rw [hm] at hu'
      refine ⟨cutP (markOf w i) (hierOf w (i + 1)) L, ?_, ?_, ?_, Or.inr ?_⟩
      · rcases Nat.lt_or_ge (sCount D0 w (i + 1)) (hierOf w (i + 1)).length with hlt | hge
        · have hs := sCount_succ D0 hw0 i
          have hpos := sCount_pos D0 hw0 i
          have hk : sCount D0 w (i + 1) - 1 < (hierOf w (i + 1)).length := by omega
          have hc := count_take_expand (markOf w i) (avoid_hierOf i) hk (sCount D0 w i)
          rw [hu, Nat.sub_add_cancel hpos] at hc
          have h1 : ¬ cutP (markOf w i) (hierOf w (i + 1)) (sCount D0 w (i + 1)) ≤
              sCount D0 w i := by
            rw [← hc]; omega
          have h2 := cutP_mono (markOf w i) (hierOf w (i + 1)) hsL
          omega
        · have hL' : L = (hierOf w (i + 1)).length := by omega
          rw [hL', ← length_expand, hu]
          exact (startCore_invariants D0 hw0 i).2.1
      · rw [← hu]; exact cutP_le_length _ _ _
      · rw [← hu, ← hu', take_expand_cutP]
        have : cutP (markOf w i) (hierOf w (i + 1)) L =
            cutP (markOf w i) (hierOf w' (i + 1)) L := by
          simp only [cutP, hLeq]
        rw [this, take_expand_cutP, hLeq]
      · rcases Nat.lt_or_ge (sCount D0 w (i + 1)) (hierOf w (i + 1)).length with hlt | hge
        · left
          have hs := sCount_succ D0 hw0 i
          have hpos := sCount_pos D0 hw0 i
          have hk : sCount D0 w (i + 1) - 1 < (hierOf w (i + 1)).length := by omega
          have hc := count_take_expand (markOf w i) (avoid_hierOf i) hk (sCount D0 w i)
          rw [hu, Nat.sub_add_cancel hpos] at hc
          have h1 : ¬ cutP (markOf w i) (hierOf w (i + 1)) (sCount D0 w (i + 1)) ≤
              sCount D0 w i := by
            rw [← hc]; omega
          have h2 := cutP_mono (markOf w i) (hierOf w (i + 1)) hsL
          omega
        · right
          have hL' : L = (hierOf w (i + 1)).length := by omega
          rw [hL', ← length_expand, hu]

  have hcap : ∀ d i, i + d = j → sCount D0 w i = (hierOf w i).length →
      sCount D0 w i < sCount D0 w' i → False := by
    intro d
    induction d with
    | zero =>
      intro i hi _ hlt
      obtain rfl : i = j := by omega
      omega
    | succ d ih =>
      intro i hi hcapi hlt
      obtain ⟨L, hsL, hLn, hLeq, -⟩ := hL (d + 1) i hi
      obtain ⟨L1, hsL1, hLn1, hLeq1, -⟩ := hL d (i + 1) (by omega)
      have hcap1 := start_cap_up D0 hw0 i hcapi
      have hm := hmk i (by omega)
      have hu := expand_hierOf hw0 i
      have hu' := expand_hierOf hw'0 i
      rw [hm] at hu'
      have hLi : L = (hierOf w i).length := by omega
      have hlen' : (hierOf w i).length < (hierOf w' i).length := by
        have := (startCore_invariants D0 hw'0 i).2.1; omega
      have hpref0 : (hierOf w' i).take (hierOf w i).length = hierOf w i := by
        rw [← hLi, hLeq, hLi, List.take_length]
      have hL1 : L1 = (hierOf w (i + 1)).length := by omega
      have hpref1 : (hierOf w' (i + 1)).take (hierOf w (i + 1)).length = hierOf w (i + 1) := by
        rw [← hL1, hLeq1, hL1, List.take_length]
      have hlen1 : (hierOf w (i + 1)).length < (hierOf w' (i + 1)).length := by
        rcases Nat.lt_or_ge (hierOf w (i + 1)).length (hierOf w' (i + 1)).length with h | h
        · exact h
        · exfalso
          rw [List.take_of_length_le h] at hpref1
          rw [← hu, ← hu', hpref1] at hlen'
          omega
      refine ih (i + 1) (by omega) hcap1 ?_
      rw [sCount_succ D0 hw'0 i, hcap1]
      have hcnt : (hierOf w (i + 1)).length ≤
          ((hierOf w' i).take (sCount D0 w' i)).count (markOf w' i) := by
        obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := hierOf w' i)
          (show (hierOf w i).length ≤ sCount D0 w' i by omega)
        rw [← ht, List.count_append, hpref0, hmk i (by omega), ← hu,
          count_expand _ (avoid_hierOf i)]
        omega
      omega
  intro i hi
  obtain ⟨L, hsL, hLn, hLeq, hdisj⟩ := hL (j - i) i (by omega)
  have hlenL : L ≤ (hierOf w' i).length := by
    have := congrArg List.length hLeq
    simp only [List.length_take] at this
    omega
  have hcore : ∀ x ≤ L, (tower D0 (markOf w) i).core (hierOf w' i) x =
      (tower D0 (markOf w) i).core (hierOf w i) x := by
    intro x hx
    rw [← core_take _ _ hx, hLeq, core_take _ _ hx]
  have hge : sCount D0 w i ≤ sCount D0 w' i := by
    rcases Nat.eq_zero_or_pos (sCount D0 w i) with h0 | hpos
    · omega
    · have hx : sCount D0 w i - 1 < sCount D0 w i := by omega
      have := (hpre i _ (by have := (startCore_invariants D0 hw0 i).2.1; omega)).mpr hx
      rw [← hcore _ (by omega)] at this
      have := (hpre' i hi _ (by omega)).mp this
      omega
  have hle : sCount D0 w' i ≤ sCount D0 w i := by
    by_contra hlt
    push Not at hlt
    rcases Nat.lt_or_ge (sCount D0 w i) (hierOf w i).length with hs | hs
    · have hsL' : sCount D0 w i < L ∨ L = (hierOf w i).length := by
        rcases hdisj with h | h | h
        · obtain rfl : i = j := by omega
          omega
        · exact Or.inl h
        · exact Or.inr h
      have hsL2 : sCount D0 w i ≤ L := hsL
      have hnot := mt (hpre i _ hs).mp (lt_irrefl _)
      rw [← hcore _ hsL2] at hnot
      exact hnot ((hpre' i hi _ (by omega)).mpr hlt)
    · exact hcap (j - i) i (by omega) (by have := (startCore_invariants D0 hw0 i).2.1; omega) hlt
  have heq : sCount D0 w' i = sCount D0 w i := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  have := congrArg (List.take (sCount D0 w i)) hLeq
  simpa [List.take_take, Nat.min_eq_left hsL] using this

end StartBelow
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

/-- Holehood, canonical shape, and start counts preserved by a level map. -/
structure LevelMapResult (D0 : Lettered α Q) (w : List α) (i : ℕ) (f : Alph α i → Alph α i)
    (w' : List α) : Prop where
  /-- The decoded word is a hole. -/
  hole : D0.IsHole w'
  /-- Markers below the mapped level are unchanged. -/
  mark_lt : ∀ k < i, markOf w' k = markOf w k
  /-- Lower alphabets only lose letters. -/
  mem_le : ∀ k ≤ i, ∀ a ∈ hierOf w' k, a ∈ hierOf w k
  /-- Higher level words are images under iterated letter maps. -/
  level : ∀ r, hierOf w' (i + r) = (hierOf w (i + r)).map (liftMap f r)
  /-- Higher markers follow the same maps. -/
  mark_ge : ∀ r, markOf w' (i + r) = liftMap f r (markOf w (i + r))
  /-- No higher map collapses a boundary pair. -/
  noCollapse : ∀ r, NoCollapse (liftMap f r) (hierOf w (i + r))
  /-- Every canonical start count is unchanged. -/
  sCount_eq : ∀ k, sCount D0 w' k = sCount D0 w k
  /-- Exactly the same levels are unary. -/
  unary_iff : ∀ k, IsUnary (hierOf w' k) ↔ IsUnary (hierOf w k)

/-- A comparison-preserving level map fixing the start prefix preserves canonical shape and all start counts. -/
theorem levelMap_spec (D0 : Lettered α Q) {w : List α} (hw : D0.IsHole w) (i : ℕ)
    (f : Alph α i → Alph α i) (hcol : NoCollapse f (hierOf w i))
    (hhole : (tower D0 (markOf w) i).IsHole ((hierOf w i).map f))
    (hsub : ∀ a ∈ hierOf w i, f a ∈ hierOf w i)
    (hpre : ∀ a ∈ (hierOf w i).take (sCount D0 w i), f a = a)
    (hcore : ∀ k, (tower D0 (markOf w) i).core ((hierOf w i).map f) k =
      (tower D0 (markOf w) i).core (hierOf w i) k) :
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

  have hup : ∀ r, hierOf w' (i + r) = (hierOf w (i + r)).map (liftMap f r) ∧
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
  have hmark : ∀ r, markOf w' (i + r) = liftMap f r (markOf w (i + r)) := by
    intro r
    rw [markOf, (hup r).1, List.getLastD_eq_getLast?, List.getLast?_map,
      getLast?_hierOf hw0 (i + r)]
    rfl

  have htw : tower D0 (markOf w') i = tower D0 (markOf w) i :=
    tower_congr D0 i (fun k hk => hmk k hk)
  have hsi : sCount D0 w' i = sCount D0 w i := by
    unfold sCount
    rw [htw, hlev, List.length_map]
    refine List.countP_congr fun x _ => ?_
    rw [hcore x]
  have hpref : (hierOf w' i).take (sCount D0 w i) = (hierOf w i).take (sCount D0 w i) := by
    rw [hlev, ← List.map_take]
    conv_rhs => rw [← List.map_id ((hierOf w i).take (sCount D0 w i))]
    exact List.map_congr_left hpre
  have hbelow := start_below D0 hw0 hw'0 i hmk hpref hsi
  have habove : ∀ r, sCount D0 w' (i + r) = sCount D0 w (i + r) := by
    intro r
    induction r with
    | zero => exact hsi
    | succ r ih =>
      obtain ⟨hr, hc⟩ := hup r
      have hr1 := (hup (r + 1)).1
      show sCount D0 w' ((i + r) + 1) = sCount D0 w ((i + r) + 1)
      rw [sCount_succ D0 hw'0, sCount_succ D0 hw0, ih, hmark r, hr]
      have hl1 : (hierOf w' (i + r + 1)).length = (hierOf w (i + r + 1)).length := by
        have := congrArg List.length hr1
        rw [List.length_map] at this
        exact this
      rw [hl1, ← List.map_take, count_map_of_injOn]
      intro x hx hfx
      exact hc.reflect_last (getLast?_hierOf hw0 _) x (List.mem_of_mem_take hx) hfx
  have hcount : ∀ k, sCount D0 w' k = sCount D0 w k := by
    intro k
    rcases Nat.lt_or_ge k i with hk | hk
    · exact (hbelow k hk.le).1
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact habove r

  have hunary_up : ∀ r, IsUnary (hierOf w' (i + r)) ↔ IsUnary (hierOf w (i + r)) := by
    intro r
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
          hi ((hunary_up 0).mp (isUnary_hierOf_of_le h i hk.le))
        exact iff_of_false h2 h1
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact hunary_up r
  have hmem : ∀ k ≤ i, ∀ a ∈ hierOf w' k, a ∈ hierOf w k := by
    refine mem_hierOf_sub hw'0 hw0 i hmk ?_
    rw [hlev]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hsub b hb
  exact ⟨hhole', hmk, hmem, fun r => (hup r).1, hmark, fun r => (hup r).2, hcount, hunary⟩

/-- Preserving all unary levels preserves canonical depth. -/
theorem LevelMapResult.depth_eq {D0 : Lettered α Q} {w w' : List α} {i : ℕ}
    {f : Alph α i → Alph α i} (h : LevelMapResult D0 w i f w') : depth w' = depth w :=
  depth_eq_of_isUnary_iff h.unary_iff

end LevelMap
end DeciNSSE.LevelMaps
