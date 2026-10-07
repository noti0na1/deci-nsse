import DeciNSSE.Constraints.Closure

/-! # Constraint spines

Fresh chains of constructor bounds enforce prescribed labels or exclude
extreme prefixes along a word. Restricting a spine solution recovers precisely
these conditions on the original variables.
-/

namespace DeciNSSE

variable {n k m : ℕ}

/-- Reindex a constraint along `Fin.castAdd m`. -/
def Constraint.lift (ϕ : Constraint n k) (m : ℕ) : Constraint n (k + m) :=
  ϕ.map (Lit.rename (Fin.castAdd m))

@[simp] theorem sat_lift (ρ' : V (k + m) → Tree n) (ϕ : Constraint n k) :
    Covariant.Sat ρ' (ϕ.lift m) ↔ Covariant.Sat (ρ' ∘ Fin.castAdd m) ϕ :=
  sat_rename _ _ _

@[simp] theorem sat_append (ρ : V k → Tree n) (ϕ ψ : Constraint n k) :
    Covariant.Sat ρ (ϕ ++ ψ) ↔ Covariant.Sat ρ ϕ ∧ Covariant.Sat ρ ψ := by
  simp only [Covariant.Sat, List.mem_append, or_imp, forall_and]

@[simp] theorem sat_cons (ρ : V k → Tree n) (l : Lit n k) (ϕ : Constraint n k) :
    Covariant.Sat ρ (l :: ϕ) ↔ Covariant.holds ρ l ∧ Covariant.Sat ρ ϕ := by
  simp [Covariant.Sat]

@[simp] theorem sat_nil (ρ : V k → Tree n) : Covariant.Sat ρ ([] : Constraint n k) := by
  simp [Covariant.Sat]

/-- The children of a spine node: `next` at the spine letter `i`, and the shared
filler `fill` at each of the other `n - 1` positions. -/
def spineChildren (i : Fin n) (next fill : V k) : Fin n → V k :=
  fun j => if j = i then next else fill

@[simp] theorem spineChildren_self (i : Fin n) (next fill : V k) :
    spineChildren i next fill i = next := by simp [spineChildren]

theorem spineChildren_of_ne {i j : Fin n} (h : j ≠ i) (next fill : V k) :
    spineChildren i next fill j = fill := by simp [spineChildren, h]

theorem spineChildren_eq_or (i j : Fin n) (next fill : V k) :
    spineChildren i next fill j = next ∨ spineChildren i next fill j = fill := by
  by_cases h : j = i <;> simp [spineChildren, h]

/-- A lower link `f(…, next at i, …, b, …) ≤ a`. -/
def lowerLink (i : Fin n) (a next b : V k) : Lit n k :=
  .fLe (spineChildren i next b) a

/-- An upper link `a ≤ f(…, next at i, …, t, …)`. -/
def upperLink (i : Fin n) (a next t : V k) : Lit n k :=
  .leF a (spineChildren i next t)

/-- The lower constructor literals along the selected spine. -/
def lowerSteps (v : ℕ → V k) (b : V k) : List (Fin n) → Constraint n k
  | [] => []
  | i :: ν => lowerLink i (v 0) (v 1) b :: lowerSteps (fun j => v (j + 1)) b ν

/-- The upper constructor literals along the selected spine. -/
def upperSteps (v : ℕ → V k) (t : V k) : List (Fin n) → Constraint n k
  | [] => []
  | i :: ν => upperLink i (v 0) (v 1) t :: upperSteps (fun j => v (j + 1)) t ν

/-- Exact membership in a lower chain: position `j` reads the letter `ν[j]`. -/
theorem mem_lowerSteps_iff {v : ℕ → V k} {b : V k} {ν : List (Fin n)} {l : Lit n k} :
    l ∈ lowerSteps v b ν ↔
      ∃ j, ∃ hj : j < ν.length, l = lowerLink ν[j] (v j) (v (j + 1)) b := by
  induction ν generalizing v with
  | nil => simp [lowerSteps]
  | cons i ν ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨j, hj, he⟩ := ih.mp h
        exact ⟨j + 1, by simpa using hj, he⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact List.mem_cons.mpr (Or.inl he)
      | succ j =>
        apply List.mem_cons.mpr ∘ Or.inr
        exact ih.mpr ⟨j, by simpa using hj, he⟩

theorem mem_upperSteps_iff {v : ℕ → V k} {t : V k} {ν : List (Fin n)} {l : Lit n k} :
    l ∈ upperSteps v t ν ↔
      ∃ j, ∃ hj : j < ν.length, l = upperLink ν[j] (v j) (v (j + 1)) t := by
  induction ν generalizing v with
  | nil => simp [upperSteps]
  | cons i ν ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨j, hj, he⟩ := ih.mp h
        exact ⟨j + 1, by simpa using hj, he⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact List.mem_cons.mpr (Or.inl he)
      | succ j =>
        apply List.mem_cons.mpr ∘ Or.inr
        exact ih.mpr ⟨j, by simpa using hj, he⟩

theorem leF_not_mem_lowerSteps (v : ℕ → V k) (b c : V k) (a : Fin n → V k)
    (ν : List (Fin n)) : Lit.leF c a ∉ lowerSteps v b ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_lowerSteps_iff.mp h
  simp [lowerLink] at he

theorem eqBot_not_mem_lowerSteps (v : ℕ → V k) (b c : V k) (ν : List (Fin n)) :
    Lit.eqBot c ∉ lowerSteps v b ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_lowerSteps_iff.mp h
  simp [lowerLink] at he

theorem eqTop_not_mem_lowerSteps (v : ℕ → V k) (b c : V k) (ν : List (Fin n)) :
    Lit.eqTop c ∉ lowerSteps v b ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_lowerSteps_iff.mp h
  simp [lowerLink] at he

theorem fLe_not_mem_upperSteps (v : ℕ → V k) (t c : V k) (a : Fin n → V k)
    (ν : List (Fin n)) : Lit.fLe a c ∉ upperSteps v t ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_upperSteps_iff.mp h
  simp [upperLink] at he

theorem eqBot_not_mem_upperSteps (v : ℕ → V k) (t c : V k) (ν : List (Fin n)) :
    Lit.eqBot c ∉ upperSteps v t ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_upperSteps_iff.mp h
  simp [upperLink] at he

theorem eqTop_not_mem_upperSteps (v : ℕ → V k) (t c : V k) (ν : List (Fin n)) :
    Lit.eqTop c ∉ upperSteps v t ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_upperSteps_iff.mp h
  simp [upperLink] at he

namespace Spine

open Safety

theorem holds_lowerLink (ρ : V k → Tree n) (i : Fin n) (a next b : V k) :
    Covariant.holds ρ (lowerLink i a next b) ↔
      Tree.node (ρ ∘ spineChildren i next b) ≤ ρ a := Iff.rfl

theorem holds_upperLink (ρ : V k → Tree n) (i : Fin n) (a next t : V k) :
    Covariant.holds ρ (upperLink i a next t) ↔
      ρ a ≤ Tree.node (ρ ∘ spineChildren i next t) := Iff.rfl

/-- A lower chain propagates its endpoint below the followed tree. -/
theorem lowerSteps_bound (ρ : V k → Tree n) (v : ℕ → V k) (b : V k)
    (ν : List (Fin n)) (h : Covariant.Sat ρ (lowerSteps v b ν)) :
    ρ (v ν.length) ≤ trace (ρ (v 0)) ν := by
  induction ν generalizing v with
  | nil => exact le_rfl
  | cons i ν ih =>
    obtain ⟨he, hr⟩ := (sat_cons _ _ _).mp h
    have hedge : ρ (v 1) ≤ descend (ρ (v 0)) i := by
      simpa using descend_mono he i
    exact le_trans (ih _ hr) (trace_mono hedge ν)

theorem upperSteps_bound (ρ : V k → Tree n) (v : ℕ → V k) (t : V k)
    (ν : List (Fin n)) (h : Covariant.Sat ρ (upperSteps v t ν)) :
    trace (ρ (v 0)) ν ≤ ρ (v ν.length) := by
  induction ν generalizing v with
  | nil => exact le_rfl
  | cons i ν ih =>
    obtain ⟨he, hr⟩ := (sat_cons _ _ _).mp h
    have hedge : descend (ρ (v 0)) i ≤ ρ (v 1) := by
      simpa using descend_mono he i
    exact le_trans (trace_mono hedge ν) (ih _ hr)

theorem node_bot_le_iff (t : Tree n) :
    Tree.node (fun _ => Tree.bot) ≤ t ↔ t ≠ Tree.bot := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
  · simp only [Tree.le_bot_iff, Tree.node_ne_bot, ne_eq, not_true_eq_false]
  · simp
  · simp

theorem le_node_top_iff (t : Tree n) :
    t ≤ Tree.node (fun _ => Tree.top) ↔ t ≠ Tree.top := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
  · simp
  · simp only [Tree.top_le_iff, Tree.node_ne_top, ne_eq, not_true_eq_false]
  · simp

/-- The canonical assignment follows actual subtrees and freezes at a leaf. -/
theorem lowerSteps_sat (ρ : V k → Tree n) (v : ℕ → V k) (b : V k)
    (ν : List (Fin n)) (t : Tree n)
    (hv : ∀ j, j ≤ ν.length → ρ (v j) = trace t (ν.take j))
    (hb : ρ b = Tree.bot) (ht : trace t ν ≠ Tree.bot) :
    Covariant.Sat ρ (lowerSteps v b ν) := by
  induction ν generalizing v t with
  | nil => simp [lowerSteps]
  | cons i ν ih =>
    have hroot : t ≠ Tree.bot := by rintro rfl; simp at ht
    apply (sat_cons _ _ _).mpr
    constructor
    · have h0 := hv 0 (by simp)
      have h1 := hv 1 (by simp)
      simp only [List.take_zero, trace_nil] at h0
      simp only [List.take_succ_cons, List.take_zero, trace_cons, trace_nil] at h1
      rw [holds_lowerLink, h0]
      rcases t.eq_bot_or_eq_top_or_node with h | rfl | ⟨a, rfl⟩
      · exact False.elim (hroot h)
      · exact Tree.le_top _
      · rw [Tree.node_le_node_iff]
        intro j
        by_cases hj : j = i
        · subst hj; simp [h1]
        · simp [spineChildren, hj, hb]
    · apply ih _ (descend t i) _ ht
      intro j hj
      simpa [List.take_succ_cons] using hv (j + 1) (by simp; omega)

theorem upperSteps_sat (ρ : V k → Tree n) (v : ℕ → V k) (tv : V k)
    (ν : List (Fin n)) (t : Tree n)
    (hv : ∀ j, j ≤ ν.length → ρ (v j) = trace t (ν.take j))
    (htv : ρ tv = Tree.top) (ht : trace t ν ≠ Tree.top) :
    Covariant.Sat ρ (upperSteps v tv ν) := by
  induction ν generalizing v t with
  | nil => simp [upperSteps]
  | cons i ν ih =>
    have hroot : t ≠ Tree.top := by rintro rfl; simp at ht
    apply (sat_cons _ _ _).mpr
    constructor
    · have h0 := hv 0 (by simp)
      have h1 := hv 1 (by simp)
      simp only [List.take_zero, trace_nil] at h0
      simp only [List.take_succ_cons, List.take_zero, trace_cons, trace_nil] at h1
      rw [holds_upperLink, h0]
      rcases t.eq_bot_or_eq_top_or_node with rfl | h | ⟨a, rfl⟩
      · exact Tree.bot_le _
      · exact False.elim (hroot h)
      · rw [Tree.node_le_node_iff]
        intro j
        by_cases hj : j = i
        · subst hj; simp [h1]
        · simp [spineChildren, hj, htv]
    · apply ih _ (descend t i) _ ht
      intro j hj
      simpa [List.take_succ_cons] using hv (j + 1) (by simp; omega)

/-- The old variables keep their indices. With `L` the spine length, lower
chain positions `1..L` are `k + j - 1`, upper chain positions are
`k + L + j - 1`, the bottom filler is `k + 2L` and the top filler `k + 2L + 1`. -/
def xv (x : V k) (L j : ℕ) : V (k + (2 * L + 2)) :=
  if h : 0 < j ∧ j ≤ L then ⟨k + j - 1, by omega⟩ else Fin.castAdd _ x

/-- The target spine variable, using the original target at cut zero. -/
def yv (y : V k) (L j : ℕ) : V (k + (2 * L + 2)) :=
  if h : 0 < j ∧ j ≤ L then ⟨k + L + j - 1, by omega⟩ else Fin.castAdd _ y

/-- The fresh bottom filler shared by the spines. -/
def bv (k L : ℕ) : V (k + (2 * L + 2)) := ⟨k + 2 * L, by omega⟩
/-- The fresh top filler shared by the spines. -/
def tv (k L : ℕ) : V (k + (2 * L + 2)) := ⟨k + 2 * L + 1, by omega⟩

@[simp] theorem xv_zero (x : V k) (L : ℕ) : xv x L 0 = Fin.castAdd _ x := by
  simp [xv]
@[simp] theorem yv_zero (y : V k) (L : ℕ) : yv y L 0 = Fin.castAdd _ y := by
  simp [yv]

/-- One extension fills both chains at once; their fresh blocks cannot interfere. -/
def extend (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n))
    (z : V (k + (2 * ν.length + 2))) : Tree n :=
  if h : z.val < k then ρ ⟨z.val, h⟩
  else if z.val < k + ν.length then trace (ρ x) (ν.take (z.val - k + 1))
  else if z.val < k + 2 * ν.length then
    trace (ρ y) (ν.take (z.val - (k + ν.length) + 1))
  else if z.val = k + 2 * ν.length then Tree.bot else Tree.top

@[simp] theorem extend_old (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n))
    (z : V k) : extend ρ x y ν (Fin.castAdd _ z) = ρ z := by
  simp [extend, z.isLt]

theorem extend_restrict (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n)) :
    extend ρ x y ν ∘ Fin.castAdd _ = ρ := by
  funext z; simp

@[simp] theorem extend_bv (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n)) :
    extend ρ x y ν (bv k ν.length) = Tree.bot := by
  simp [extend, bv, show ¬ k + 2 * ν.length < k by omega,
    show ¬ k + 2 * ν.length < k + ν.length by omega]

@[simp] theorem extend_tv (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n)) :
    extend ρ x y ν (tv k ν.length) = Tree.top := by
  simp [extend, tv, show ¬ k + 2 * ν.length + 1 < k by omega,
    show ¬ k + 2 * ν.length + 1 < k + ν.length by omega,
    show ¬ k + 2 * ν.length + 1 < k + 2 * ν.length by omega]

theorem extend_xv (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n))
    (j : ℕ) (hj : j ≤ ν.length) :
    extend ρ x y ν (xv x ν.length j) = trace (ρ x) (ν.take j) := by
  by_cases hz : j = 0
  · subst j; simp
  · have hp : 0 < j ∧ j ≤ ν.length := ⟨by omega, hj⟩
    have hge : ¬ k + j - 1 < k := by omega
    have hlt : k + j - 1 < k + ν.length := by omega
    have he : k + j - 1 - k + 1 = j := by omega
    simp [xv, hp, extend, hge, hlt, he]

theorem extend_yv (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n))
    (j : ℕ) (hj : j ≤ ν.length) :
    extend ρ x y ν (yv y ν.length j) = trace (ρ y) (ν.take j) := by
  by_cases hz : j = 0
  · subst j; simp
  · have hp : 0 < j ∧ j ≤ ν.length := ⟨by omega, hj⟩
    have hge : ¬ k + ν.length + j - 1 < k := by omega
    have hge' : ¬ k + ν.length + j - 1 < k + ν.length := by omega
    have hlt : k + ν.length + j - 1 < k + 2 * ν.length := by omega
    have he : k + ν.length + j - 1 - (k + ν.length) + 1 = j := by omega
    simp [yv, hp, extend, hge, hge', hlt, he]

end Spine

open Safety Spine

/-- `x` has no bottom at any prefix of `ν`: a lower chain ending in `f(⊥,…,⊥)`. -/
def noBotChain (x : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  lowerSteps (xv x ν.length) (bv k ν.length) ν ++
    [.fLe (fun _ => bv k ν.length) (xv x ν.length ν.length), .eqBot (bv k ν.length)]

/-- `y` has a bottom at some prefix of `ν`: an upper chain ending in `⊥`. -/
def botChain (y : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  upperSteps (yv y ν.length) (tv k ν.length) ν ++
    [.eqBot (yv y ν.length ν.length), .eqTop (tv k ν.length)]

/-- `x` has a top at some prefix of `ν`: a lower chain ending in `⊤`. -/
def topChain (x : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  lowerSteps (xv x ν.length) (bv k ν.length) ν ++
    [.eqTop (xv x ν.length ν.length), .eqBot (bv k ν.length)]

/-- `y` has no top at any prefix of `ν`: an upper chain ending in `f(⊤,…,⊤)`. -/
def noTopChain (y : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  upperSteps (yv y ν.length) (tv k ν.length) ν ++
    [.leF (yv y ν.length ν.length) (fun _ => tv k ν.length), .eqTop (tv k ν.length)]

namespace Spine

variable {ν : List (Fin n)} {x y : V k} {ρ' : V (k + (2 * ν.length + 2)) → Tree n}

theorem noBotChain_sound (h : Covariant.Sat ρ' (noBotChain x ν)) :
    trace (ρ' (Fin.castAdd _ x)) ν ≠ Tree.bot := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : Tree.node (fun _ => ρ' (bv k ν.length)) ≤ ρ' (xv x ν.length ν.length) ∧
      ρ' (bv k ν.length) = Tree.bot := by
    simpa [Covariant.Sat, Covariant.holds, Function.comp_def] using he
  have hb := lowerSteps_bound _ _ _ _ hs
  rw [xv_zero] at hb
  apply (node_bot_le_iff _).mp
  have h1 := he'.1
  rw [he'.2] at h1
  exact le_trans h1 hb

theorem botChain_sound (h : Covariant.Sat ρ' (botChain y ν)) :
    trace (ρ' (Fin.castAdd _ y)) ν = Tree.bot := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : ρ' (yv y ν.length ν.length) = Tree.bot ∧
      ρ' (tv k ν.length) = Tree.top := by simpa [Covariant.Sat, Covariant.holds] using he
  have hb := upperSteps_bound _ _ _ _ hs
  rw [yv_zero, he'.1] at hb
  exact (Tree.le_bot_iff _).mp hb

theorem topChain_sound (h : Covariant.Sat ρ' (topChain x ν)) :
    trace (ρ' (Fin.castAdd _ x)) ν = Tree.top := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : ρ' (xv x ν.length ν.length) = Tree.top ∧
      ρ' (bv k ν.length) = Tree.bot := by simpa [Covariant.Sat, Covariant.holds] using he
  have hb := lowerSteps_bound _ _ _ _ hs
  rw [xv_zero, he'.1] at hb
  exact (Tree.top_le_iff _).mp hb

theorem noTopChain_sound (h : Covariant.Sat ρ' (noTopChain y ν)) :
    trace (ρ' (Fin.castAdd _ y)) ν ≠ Tree.top := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : ρ' (yv y ν.length ν.length) ≤ Tree.node (fun _ => ρ' (tv k ν.length)) ∧
      ρ' (tv k ν.length) = Tree.top := by simpa [Covariant.Sat, Covariant.holds, Function.comp_def] using he
  have hb := upperSteps_bound _ _ _ _ hs
  rw [yv_zero] at hb
  apply (le_node_top_iff _).mp
  have h1 := he'.1
  rw [he'.2] at h1
  exact le_trans hb h1

theorem noBotChain_extend (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ x) ν ≠ Tree.bot) : Covariant.Sat (extend ρ x y ν) (noBotChain x ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact lowerSteps_sat _ _ _ _ _ (extend_xv ρ x y ν) (extend_bv ..) h
  · have he := extend_xv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simpa [Covariant.Sat, Covariant.holds, he, Function.comp_def, node_bot_le_iff] using h

theorem botChain_extend (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ y) ν = Tree.bot) : Covariant.Sat (extend ρ x y ν) (botChain y ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact upperSteps_sat _ _ _ _ _ (extend_yv ρ x y ν) (extend_tv ..)
      (by rw [h]; exact Tree.bot_ne_top)
  · have he := extend_yv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simp [Covariant.Sat, Covariant.holds, he, h]

theorem topChain_extend (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ x) ν = Tree.top) : Covariant.Sat (extend ρ x y ν) (topChain x ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact lowerSteps_sat _ _ _ _ _ (extend_xv ρ x y ν) (extend_bv ..)
      (by rw [h]; exact Tree.top_ne_bot)
  · have he := extend_xv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simp [Covariant.Sat, Covariant.holds, he, h]

theorem noTopChain_extend (ρ : V k → Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ y) ν ≠ Tree.top) : Covariant.Sat (extend ρ x y ν) (noTopChain y ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact upperSteps_sat _ _ _ _ _ (extend_yv ρ x y ν) (extend_tv ..) h
  · have he := extend_yv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simpa [Covariant.Sat, Covariant.holds, he, Function.comp_def, le_node_top_iff] using h

end Spine

/-- A path witnessing failure of right safety: `x` has no bottom on `ν`,
while `y` has a bottom on `ν`. -/
def rUnsafe (ϕ : Constraint n k) (x y : V k) (ν : List (Fin n)) :
    Constraint n (k + (2 * ν.length + 2)) :=
  ϕ.lift _ ++ noBotChain x ν ++ botChain y ν

/-- A path witnessing failure of left safety: `x` has a top on `ν`,
while `y` has no top on `ν`. -/
def lUnsafe (ϕ : Constraint n k) (x y : V k) (ν : List (Fin n)) :
    Constraint n (k + (2 * ν.length + 2)) :=
  ϕ.lift _ ++ topChain x ν ++ noTopChain y ν

namespace Spine

variable {ϕ : Constraint n k} {x y : V k} {ν : List (Fin n)}

@[simp] theorem sat_rUnsafe_iff (ρ' : V (k + (2 * ν.length + 2)) → Tree n) :
    Covariant.Sat ρ' (rUnsafe ϕ x y ν) ↔ Covariant.Sat (ρ' ∘ Fin.castAdd _) ϕ ∧
      Covariant.Sat ρ' (noBotChain x ν) ∧ Covariant.Sat ρ' (botChain y ν) := by
  simp only [rUnsafe, sat_append, sat_lift, and_assoc]

@[simp] theorem sat_lUnsafe_iff (ρ' : V (k + (2 * ν.length + 2)) → Tree n) :
    Covariant.Sat ρ' (lUnsafe ϕ x y ν) ↔ Covariant.Sat (ρ' ∘ Fin.castAdd _) ϕ ∧
      Covariant.Sat ρ' (topChain x ν) ∧ Covariant.Sat ρ' (noTopChain y ν) := by
  simp only [lUnsafe, sat_append, sat_lift, and_assoc]

theorem rUnsafe_extend (ρ : V k → Tree n) (hϕ : Covariant.Sat ρ ϕ)
    (hx : trace (ρ x) ν ≠ Tree.bot) (hy : trace (ρ y) ν = Tree.bot) :
    Covariant.Sat (extend ρ x y ν) (rUnsafe ϕ x y ν) := by
  apply (sat_rUnsafe_iff _).mpr
  exact ⟨by simpa [extend_restrict] using hϕ,
    noBotChain_extend _ _ _ _ hx, botChain_extend _ _ _ _ hy⟩

theorem lUnsafe_extend (ρ : V k → Tree n) (hϕ : Covariant.Sat ρ ϕ)
    (hx : trace (ρ x) ν = Tree.top) (hy : trace (ρ y) ν ≠ Tree.top) :
    Covariant.Sat (extend ρ x y ν) (lUnsafe ϕ x y ν) := by
  apply (sat_lUnsafe_iff _).mpr
  exact ⟨by simpa [extend_restrict] using hϕ,
    topChain_extend _ _ _ _ hx, noTopChain_extend _ _ _ _ hy⟩

end Spine

/-- Exact semantics of right unsafety: restricted to the old variables, the
solutions of `rUnsafe ϕ x y ν` are exactly the solutions of `ϕ` in which `y`
has a bottom on `ν` and `x` has none. -/
theorem rUnsafe_restrict_iff (ϕ : Constraint n k) (x y : V k) (ν : List (Fin n))
    (ρ : V k → Tree n) :
    (∃ ρ', ρ' ∘ Fin.castAdd _ = ρ ∧ Covariant.Sat ρ' (rUnsafe ϕ x y ν)) ↔
      Covariant.Sat ρ ϕ ∧ ¬ covPrefBot ν (ρ x) ∧ covPrefBot ν (ρ y) := by
  simp only [covPrefBot, ← trace_eq_bot_iff]
  constructor
  · rintro ⟨ρ', rfl, hs⟩
    obtain ⟨hϕ, hx, hy⟩ := (sat_rUnsafe_iff _).mp hs
    exact ⟨hϕ, noBotChain_sound hx, botChain_sound hy⟩
  · rintro ⟨hϕ, hx, hy⟩
    exact ⟨extend ρ x y ν, extend_restrict .., rUnsafe_extend ρ hϕ hx hy⟩

/-- Exact semantics of left unsafety. -/
theorem lUnsafe_restrict_iff (ϕ : Constraint n k) (x y : V k) (ν : List (Fin n))
    (ρ : V k → Tree n) :
    (∃ ρ', ρ' ∘ Fin.castAdd _ = ρ ∧ Covariant.Sat ρ' (lUnsafe ϕ x y ν)) ↔
      Covariant.Sat ρ ϕ ∧ covPrefTop ν (ρ x) ∧ ¬ covPrefTop ν (ρ y) := by
  simp only [covPrefTop, ← trace_eq_top_iff]
  constructor
  · rintro ⟨ρ', rfl, hs⟩
    obtain ⟨hϕ, hx, hy⟩ := (sat_lUnsafe_iff _).mp hs
    exact ⟨hϕ, topChain_sound hx, noTopChain_sound hy⟩
  · rintro ⟨hϕ, hx, hy⟩
    exact ⟨extend ρ x y ν, extend_restrict .., lUnsafe_extend ρ hϕ hx hy⟩

end DeciNSSE
