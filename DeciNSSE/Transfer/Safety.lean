import DeciNSSE.Satisfiability.Decide

/-! # Path witnesses to failed entailment

A failed tree inequality has a path witnessing a bottom or top mismatch.
Fresh variable chains encode these mismatches as flat constraint systems,
reducing counterexamples to satisfiability.
-/

namespace DeciNSSE

variable {k m : ℕ}

/-- Embed a literal into a larger variable set, retaining its original indices. -/
def Lit.lift (l : Lit k) (m : ℕ) : Lit (k + m) := l.rename (Fin.castAdd m)

/-- Embed every literal of a constraint system into a larger variable set. -/
def Constraint.lift (ϕ : Constraint k) (m : ℕ) : Constraint (k + m) :=
  ϕ.map (fun l => l.lift m)

@[simp] theorem sat_lift (ρ' : V (k + m) → Tree) (ϕ : Constraint k) :
    Sat ρ' (ϕ.lift m) ↔ Sat (ρ' ∘ Fin.castAdd m) ϕ :=
  sat_rename _ _ _

@[simp] theorem sat_append (ρ : V k → Tree) (ϕ ψ : Constraint k) :
    Sat ρ (ϕ ++ ψ) ↔ Sat ρ ϕ ∧ Sat ρ ψ := by
  simp only [Sat, List.mem_append, or_imp, forall_and]

namespace Safety

/-- Follow one child of a constructor node, leaving a leaf unchanged. -/
def descend (t : Tree) (i : Fin 2) : Tree :=
  if h : t.fn [] = some Sym.f then t.branch i h else t

@[simp] theorem descend_bot (i : Fin 2) : descend Tree.bot i = Tree.bot := by
  simp [descend]

@[simp] theorem descend_top (i : Fin 2) : descend Tree.top i = Tree.top := by
  simp [descend]

@[simp] theorem descend_node (l r : Tree) (i : Fin 2) :
    descend (Tree.node l r) i = if i = 0 then l else r := by
  apply Tree.ext
  funext π
  fin_cases i <;> simp [descend, Tree.branch, Tree.node]

/-- Follow a path through a tree, retaining the first leaf if the path extends beyond it. -/
def trace (t : Tree) : List (Fin 2) → Tree
  | [] => t
  | i :: ν => trace (descend t i) ν

@[simp] theorem trace_nil (t : Tree) : trace t [] = t := rfl
@[simp] theorem trace_cons (t : Tree) (i : Fin 2) (ν : List (Fin 2)) :
    trace t (i :: ν) = trace (descend t i) ν := rfl
@[simp] theorem trace_bot (ν : List (Fin 2)) : trace Tree.bot ν = Tree.bot := by
  induction ν <;> simp_all
@[simp] theorem trace_top (ν : List (Fin 2)) : trace Tree.top ν = Tree.top := by
  induction ν <;> simp_all

theorem trace_append (t : Tree) (ν μ : List (Fin 2)) :
    trace t (ν ++ μ) = trace (trace t ν) μ := by
  induction ν generalizing t <;> simp_all

theorem descend_mono {t u : Tree} (h : t ≤ u) (i : Fin 2) :
    descend t i ≤ descend u i := by
  rcases (Tree.le_iff_root_cases _ _).mp h with rfl | rfl |
    ⟨l, r, l', r', rfl, rfl, hl, hr⟩
  · simp
  · simp
  · fin_cases i <;> simp_all

theorem trace_mono {t u : Tree} (h : t ≤ u) (ν : List (Fin 2)) :
    trace t ν ≤ trace u ν := by
  induction ν generalizing t u with
  | nil => exact h
  | cons i ν ih => exact ih (descend_mono h i)

/-- The tree contains the specified label at the given path. -/
def HasLabel (t : Tree) (ν : List (Fin 2)) (s : Sym) : Prop :=
  ∃ τ, τ <+: ν ∧ t.fn τ = some s

@[simp] theorem hasLabel_nil (t : Tree) (s : Sym) :
    HasLabel t [] s ↔ t.fn [] = some s := by simp [HasLabel]

@[simp] theorem hasLabel_bot (ν : List (Fin 2)) (s : Sym) :
    HasLabel Tree.bot ν s ↔ s = Sym.bot := by
  constructor
  · rintro ⟨τ, _, h⟩; cases τ <;> simpa using h.symm
  · rintro rfl; exact ⟨[], List.nil_prefix, rfl⟩

@[simp] theorem hasLabel_top (ν : List (Fin 2)) (s : Sym) :
    HasLabel Tree.top ν s ↔ s = Sym.top := by
  constructor
  · rintro ⟨τ, _, h⟩; cases τ <;> simpa using h.symm
  · rintro rfl; exact ⟨[], List.nil_prefix, rfl⟩

theorem hasLabel_node_cons (l r : Tree) (i : Fin 2) (ν : List (Fin 2))
    (s : Sym) (hs : s ≠ Sym.f) :
    HasLabel (Tree.node l r) (i :: ν) s ↔ HasLabel (if i = 0 then l else r) ν s := by
  constructor
  · rintro ⟨τ, hp, h⟩
    cases τ with
    | nil => exact False.elim (hs (Option.some.inj h).symm)
    | cons j τ =>
      obtain ⟨μ, he⟩ := hp
      have hij : j = i := (List.cons.inj he).1
      subst j
      refine ⟨τ, ⟨μ, (List.cons.inj he).2⟩, ?_⟩
      fin_cases i <;> simpa using h
  · rintro ⟨τ, ⟨μ, he⟩, h⟩
    refine ⟨i :: τ, ⟨μ, by simp [he]⟩, ?_⟩
    fin_cases i <;> simpa using h

theorem trace_eq_bot_iff (t : Tree) (ν : List (Fin 2)) :
    trace t ν = Tree.bot ↔ HasLabel t ν Sym.bot := by
  induction ν generalizing t with
  | nil => simp
  | cons i ν ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨l, r, rfl⟩
    · simp
    · simp
    · rw [trace_cons, descend_node, ih, hasLabel_node_cons _ _ _ _ _ (by decide)]

theorem trace_eq_top_iff (t : Tree) (ν : List (Fin 2)) :
    trace t ν = Tree.top ↔ HasLabel t ν Sym.top := by
  induction ν generalizing t with
  | nil => simp
  | cons i ν ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨l, r, rfl⟩
    · simp
    · simp
    · rw [trace_cons, descend_node, ih, hasLabel_node_cons _ _ _ _ _ (by decide)]

/-- A lower-bound literal following child `i`, with variable `b` on the other branch. -/
def lowerLink (i : Fin 2) (a next b : V k) : Lit k :=
  if i = 0 then .fLe next b a else .fLe b next a

/-- An upper-bound literal following child `i`, with variable `t` on the other branch. -/
def upperLink (i : Fin 2) (a next t : V k) : Lit k :=
  if i = 0 then .leF a next t else .leF a t next

/-- A chain of constructor lower bounds along a binary path. -/
def lowerSteps (v : ℕ → V k) (b : V k) : List (Fin 2) → Constraint k
  | [] => []
  | i :: ν => lowerLink i (v 0) (v 1) b :: lowerSteps (fun j => v (j + 1)) b ν

/-- A chain of constructor upper bounds along a binary path. -/
def upperSteps (v : ℕ → V k) (t : V k) : List (Fin 2) → Constraint k
  | [] => []
  | i :: ν => upperLink i (v 0) (v 1) t :: upperSteps (fun j => v (j + 1)) t ν

@[simp] theorem sat_cons (ρ : V k → Tree) (l : Lit k) (ϕ : Constraint k) :
    Sat ρ (l :: ϕ) ↔ l.holds ρ ∧ Sat ρ ϕ := by simp [Sat]

theorem lowerSteps_bound (ρ : V k → Tree) (v : ℕ → V k) (b : V k)
    (ν : List (Fin 2)) (h : Sat ρ (lowerSteps v b ν)) :
    ρ (v ν.length) ≤ trace (ρ (v 0)) ν := by
  induction ν generalizing v with
  | nil => exact le_rfl
  | cons i ν ih =>
    obtain ⟨he, hr⟩ := (sat_cons _ _ _).mp h
    have hedge : ρ (v 1) ≤ descend (ρ (v 0)) i := by
      fin_cases i
      · simpa using descend_mono he 0
      · simpa using descend_mono he 1
    exact le_trans (ih _ hr) (trace_mono hedge ν)

theorem upperSteps_bound (ρ : V k → Tree) (v : ℕ → V k) (t : V k)
    (ν : List (Fin 2)) (h : Sat ρ (upperSteps v t ν)) :
    trace (ρ (v 0)) ν ≤ ρ (v ν.length) := by
  induction ν generalizing v with
  | nil => exact le_rfl
  | cons i ν ih =>
    obtain ⟨he, hr⟩ := (sat_cons _ _ _).mp h
    have hedge : descend (ρ (v 0)) i ≤ ρ (v 1) := by
      fin_cases i
      · simpa using descend_mono he 0
      · simpa using descend_mono he 1
    exact le_trans (trace_mono hedge ν) (ih _ hr)

theorem node_bot_bot_le_iff (t : Tree) :
    Tree.node Tree.bot Tree.bot ≤ t ↔ t ≠ Tree.bot := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨l, r, rfl⟩ <;> simp

theorem le_node_top_top_iff (t : Tree) :
    t ≤ Tree.node Tree.top Tree.top ↔ t ≠ Tree.top := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨l, r, rfl⟩ <;> simp

theorem lowerSteps_sat (ρ : V k → Tree) (v : ℕ → V k) (b : V k)
    (ν : List (Fin 2)) (t : Tree)
    (hv : ∀ j, j ≤ ν.length → ρ (v j) = trace t (ν.take j))
    (hb : ρ b = Tree.bot) (ht : trace t ν ≠ Tree.bot) :
    Sat ρ (lowerSteps v b ν) := by
  induction ν generalizing v t with
  | nil => simp [lowerSteps, Sat]
  | cons i ν ih =>
    have hroot : t ≠ Tree.bot := by rintro rfl; simp at ht
    apply (sat_cons _ _ _).mpr
    constructor
    · have h0 := hv 0 (by simp)
      have h1 := hv 1 (by simp)
      simp only [List.take_zero, trace_nil] at h0
      simp only [List.take_succ_cons, List.take_zero, trace_cons, trace_nil] at h1
      rcases t.eq_bot_or_eq_top_or_node with h | rfl | ⟨l, r, rfl⟩
      · exact False.elim (hroot h)
      · fin_cases i <;> simp [lowerLink, Lit.holds, h0, h1, hb]
      · fin_cases i <;> simp [lowerLink, Lit.holds, h0, h1, hb]
    · apply ih _ (descend t i) _ ht
      intro j hj
      simpa [List.take_succ_cons] using hv (j + 1) (by simp; omega)

theorem upperSteps_sat (ρ : V k → Tree) (v : ℕ → V k) (tv : V k)
    (ν : List (Fin 2)) (t : Tree)
    (hv : ∀ j, j ≤ ν.length → ρ (v j) = trace t (ν.take j))
    (htv : ρ tv = Tree.top) (ht : trace t ν ≠ Tree.top) :
    Sat ρ (upperSteps v tv ν) := by
  induction ν generalizing v t with
  | nil => simp [upperSteps, Sat]
  | cons i ν ih =>
    have hroot : t ≠ Tree.top := by rintro rfl; simp at ht
    apply (sat_cons _ _ _).mpr
    constructor
    · have h0 := hv 0 (by simp)
      have h1 := hv 1 (by simp)
      simp only [List.take_zero, trace_nil] at h0
      simp only [List.take_succ_cons, List.take_zero, trace_cons, trace_nil] at h1
      rcases t.eq_bot_or_eq_top_or_node with rfl | h | ⟨l, r, rfl⟩
      · fin_cases i <;> simp [upperLink, Lit.holds, h0, h1, htv]
      · exact False.elim (hroot h)
      · fin_cases i <;> simp [upperLink, Lit.holds, h0, h1, htv]
    · apply ih _ (descend t i) _ ht
      intro j hj
      simpa [List.take_succ_cons] using hv (j + 1) (by simp; omega)

/-- The variable for a position in the lower witness chain, starting at `x`. -/
def xv (x : V k) (n j : ℕ) : V (k + (2 * n + 2)) :=
  if h : 0 < j ∧ j ≤ n then ⟨k + j - 1, by omega⟩ else Fin.castAdd _ x

/-- The variable for a position in the upper witness chain, starting at `y`. -/
def yv (y : V k) (n j : ℕ) : V (k + (2 * n + 2)) :=
  if h : 0 < j ∧ j ≤ n then ⟨k + n + j - 1, by omega⟩ else Fin.castAdd _ y

/-- The fresh variable constrained to bottom in a witness system. -/
def bv (k n : ℕ) : V (k + (2 * n + 2)) := ⟨k + 2 * n, by omega⟩
/-- The fresh variable constrained to top in a witness system. -/
def tv (k n : ℕ) : V (k + (2 * n + 2)) := ⟨k + 2 * n + 1, by omega⟩

@[simp] theorem xv_zero (x : V k) (n : ℕ) : xv x n 0 = Fin.castAdd _ x := by
  simp [xv]
@[simp] theorem yv_zero (y : V k) (n : ℕ) : yv y n 0 = Fin.castAdd _ y := by
  simp [yv]

theorem xv_injective (x : V k) (n : ℕ) :
    Function.Injective (fun j : Fin (n + 1) => xv x n j) := by
  intro i j h
  have hv := congrArg Fin.val h
  dsimp [xv] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd] at hv <;> apply Fin.ext <;> omega

/--
Extend a tree assignment with traces along both witness chains and fixed bottom and top
variables.
-/
def extend (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2))
    (z : V (k + (2 * ν.length + 2))) : Tree :=
  if h : z.val < k then ρ ⟨z.val, h⟩
  else if z.val < k + ν.length then trace (ρ x) (ν.take (z.val - k + 1))
  else if z.val < k + 2 * ν.length then
    trace (ρ y) (ν.take (z.val - (k + ν.length) + 1))
  else if z.val = k + 2 * ν.length then Tree.bot else Tree.top

@[simp] theorem extend_old (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2))
    (z : V k) : extend ρ x y ν (Fin.castAdd _ z) = ρ z := by
  simp [extend, z.isLt]

theorem extend_restrict (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2)) :
    extend ρ x y ν ∘ Fin.castAdd _ = ρ := by funext z; simp

@[simp] theorem extend_bv (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2)) :
    extend ρ x y ν (bv k ν.length) = Tree.bot := by
  simp [extend, bv, show ¬ k + 2 * ν.length < k by omega,
    show ¬ k + 2 * ν.length < k + ν.length by omega]

@[simp] theorem extend_tv (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2)) :
    extend ρ x y ν (tv k ν.length) = Tree.top := by
  simp [extend, tv, show ¬ k + 2 * ν.length + 1 < k by omega,
    show ¬ k + 2 * ν.length + 1 < k + ν.length by omega,
    show ¬ k + 2 * ν.length + 1 < k + 2 * ν.length by omega]

theorem extend_xv (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2))
    (j : ℕ) (hj : j ≤ ν.length) :
    extend ρ x y ν (xv x ν.length j) = trace (ρ x) (ν.take j) := by
  by_cases hz : j = 0
  · subst j; simp
  · have hp : 0 < j ∧ j ≤ ν.length := ⟨by omega, hj⟩
    have hge : ¬ k + j - 1 < k := by omega
    have hlt : k + j - 1 < k + ν.length := by omega
    have he : k + j - 1 - k + 1 = j := by omega
    simp [xv, hp, extend, hge, hlt, he]

theorem extend_yv (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2))
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

end Safety

open Safety

/-- Constraints forcing the lower witness chain to end above a constructor node. -/
def noBotChain (x : V k) (ν : List (Fin 2)) : Constraint (k + (2 * ν.length + 2)) :=
  lowerSteps (xv x ν.length) (bv k ν.length) ν ++
    [.fLe (bv k ν.length) (bv k ν.length) (xv x ν.length ν.length),
     .eqBot (bv k ν.length)]

/-- Constraints forcing the upper witness chain to end at bottom. -/
def botChain (y : V k) (ν : List (Fin 2)) : Constraint (k + (2 * ν.length + 2)) :=
  upperSteps (yv y ν.length) (tv k ν.length) ν ++
    [.eqBot (yv y ν.length ν.length), .eqTop (tv k ν.length)]

/-- Constraints forcing the lower witness chain to end at top. -/
def topChain (x : V k) (ν : List (Fin 2)) : Constraint (k + (2 * ν.length + 2)) :=
  lowerSteps (xv x ν.length) (bv k ν.length) ν ++
    [.eqTop (xv x ν.length ν.length), .eqBot (bv k ν.length)]

/-- Constraints forcing the upper witness chain to end below a constructor node. -/
def noTopChain (y : V k) (ν : List (Fin 2)) : Constraint (k + (2 * ν.length + 2)) :=
  upperSteps (yv y ν.length) (tv k ν.length) ν ++
    [.leF (yv y ν.length ν.length) (tv k ν.length) (tv k ν.length),
     .eqTop (tv k ν.length)]

namespace Safety

variable {ν : List (Fin 2)} {x y : V k} {ρ' : V (k + (2 * ν.length + 2)) → Tree}

theorem noBotChain_sound (h : Sat ρ' (noBotChain x ν)) :
    trace (ρ' (Fin.castAdd _ x)) ν ≠ Tree.bot := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : Tree.node (ρ' (bv k ν.length)) (ρ' (bv k ν.length)) ≤
      ρ' (xv x ν.length ν.length) ∧ ρ' (bv k ν.length) = Tree.bot := by
    simpa [Sat, Lit.holds] using he
  have hb := lowerSteps_bound _ _ _ _ hs
  rw [xv_zero] at hb
  apply (node_bot_bot_le_iff _).mp
  rw [he'.2] at he'
  exact le_trans he'.1 hb

theorem botChain_sound (h : Sat ρ' (botChain y ν)) :
    trace (ρ' (Fin.castAdd _ y)) ν = Tree.bot := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : ρ' (yv y ν.length ν.length) = Tree.bot ∧
      ρ' (tv k ν.length) = Tree.top := by simpa [Sat, Lit.holds] using he
  have hb := upperSteps_bound _ _ _ _ hs
  rw [yv_zero, he'.1] at hb
  exact (Tree.le_bot_iff _).mp hb

theorem topChain_sound (h : Sat ρ' (topChain x ν)) :
    trace (ρ' (Fin.castAdd _ x)) ν = Tree.top := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : ρ' (xv x ν.length ν.length) = Tree.top ∧
      ρ' (bv k ν.length) = Tree.bot := by simpa [Sat, Lit.holds] using he
  have hb := lowerSteps_bound _ _ _ _ hs
  rw [xv_zero, he'.1] at hb
  exact (Tree.top_le_iff _).mp hb

theorem noTopChain_sound (h : Sat ρ' (noTopChain y ν)) :
    trace (ρ' (Fin.castAdd _ y)) ν ≠ Tree.top := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : ρ' (yv y ν.length ν.length) ≤
      Tree.node (ρ' (tv k ν.length)) (ρ' (tv k ν.length)) ∧
      ρ' (tv k ν.length) = Tree.top := by simpa [Sat, Lit.holds] using he
  have hb := upperSteps_bound _ _ _ _ hs
  rw [yv_zero] at hb
  apply (le_node_top_top_iff _).mp
  rw [he'.2] at he'
  exact le_trans hb he'.1

theorem noBotChain_extend (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2))
    (h : trace (ρ x) ν ≠ Tree.bot) : Sat (extend ρ x y ν) (noBotChain x ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact lowerSteps_sat _ _ _ _ _ (extend_xv ρ x y ν) (extend_bv ..) h
  · have he := extend_xv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simpa [Sat, Lit.holds, he, node_bot_bot_le_iff] using h

theorem botChain_extend (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2))
    (h : trace (ρ y) ν = Tree.bot) : Sat (extend ρ x y ν) (botChain y ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact upperSteps_sat _ _ _ _ _ (extend_yv ρ x y ν) (extend_tv ..)
      (by rw [h]; exact Tree.bot_ne_top)
  · have he := extend_yv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simp [Sat, Lit.holds, he, h]

theorem topChain_extend (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2))
    (h : trace (ρ x) ν = Tree.top) : Sat (extend ρ x y ν) (topChain x ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact lowerSteps_sat _ _ _ _ _ (extend_xv ρ x y ν) (extend_bv ..)
      (by rw [h]; exact Tree.top_ne_bot)
  · have he := extend_xv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simp [Sat, Lit.holds, he, h]

theorem noTopChain_extend (ρ : V k → Tree) (x y : V k) (ν : List (Fin 2))
    (h : trace (ρ y) ν ≠ Tree.top) : Sat (extend ρ x y ν) (noTopChain y ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact upperSteps_sat _ _ _ _ _ (extend_yv ρ x y ν) (extend_tv ..) h
  · have he := extend_yv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simpa [Sat, Lit.holds, he, le_node_top_top_iff] using h

end Safety

/-- The original constraints extended by a witness to a right-side bottom mismatch. -/
def rUnsafe (ϕ : Constraint k) (x y : V k) (ν : List (Fin 2)) :
    Constraint (k + (2 * ν.length + 2)) :=
  ϕ.lift _ ++ noBotChain x ν ++ botChain y ν

/-- The original constraints extended by a witness to a left-side top mismatch. -/
def lUnsafe (ϕ : Constraint k) (x y : V k) (ν : List (Fin 2)) :
    Constraint (k + (2 * ν.length + 2)) :=
  ϕ.lift _ ++ topChain x ν ++ noTopChain y ν

namespace Safety

variable {ϕ : Constraint k} {x y : V k} {ν : List (Fin 2)}

@[simp] theorem sat_rUnsafe_iff (ρ' : V (k + (2 * ν.length + 2)) → Tree) :
    Sat ρ' (rUnsafe ϕ x y ν) ↔ Sat (ρ' ∘ Fin.castAdd _) ϕ ∧
      Sat ρ' (noBotChain x ν) ∧ Sat ρ' (botChain y ν) := by
  simp [rUnsafe]

@[simp] theorem sat_lUnsafe_iff (ρ' : V (k + (2 * ν.length + 2)) → Tree) :
    Sat ρ' (lUnsafe ϕ x y ν) ↔ Sat (ρ' ∘ Fin.castAdd _) ϕ ∧
      Sat ρ' (topChain x ν) ∧ Sat ρ' (noTopChain y ν) := by
  simp [lUnsafe]

/--
Every solution of the right mismatch system gives a counterexample to the proposed inequality.
-/
theorem rUnsafe_sound {ρ' : V (k + (2 * ν.length + 2)) → Tree}
    (h : Sat ρ' (rUnsafe ϕ x y ν)) :
    Sat (ρ' ∘ Fin.castAdd _) ϕ ∧ ¬ ρ' (Fin.castAdd _ x) ≤ ρ' (Fin.castAdd _ y) := by
  obtain ⟨hϕ, hx, hy⟩ := (sat_rUnsafe_iff _).mp h
  refine ⟨hϕ, fun hle => noBotChain_sound hx ?_⟩
  have hm := trace_mono hle ν
  rw [botChain_sound hy] at hm
  exact (Tree.le_bot_iff _).mp hm

/--
Every solution of the left mismatch system gives a counterexample to the proposed inequality.
-/
theorem lUnsafe_sound {ρ' : V (k + (2 * ν.length + 2)) → Tree}
    (h : Sat ρ' (lUnsafe ϕ x y ν)) :
    Sat (ρ' ∘ Fin.castAdd _) ϕ ∧ ¬ ρ' (Fin.castAdd _ x) ≤ ρ' (Fin.castAdd _ y) := by
  obtain ⟨hϕ, hx, hy⟩ := (sat_lUnsafe_iff _).mp h
  refine ⟨hϕ, fun hle => noTopChain_sound hy ?_⟩
  have hm := trace_mono hle ν
  rw [topChain_sound hx] at hm
  exact (Tree.top_le_iff _).mp hm

/-- A right-side label mismatch extends a solution to the right witness system. -/
theorem rUnsafe_extend (ρ : V k → Tree) (hϕ : Sat ρ ϕ)
    (hx : trace (ρ x) ν ≠ Tree.bot) (hy : trace (ρ y) ν = Tree.bot) :
    Sat (extend ρ x y ν) (rUnsafe ϕ x y ν) := by
  apply (sat_rUnsafe_iff _).mpr
  exact ⟨by simpa [extend_restrict] using hϕ,
    noBotChain_extend _ _ _ _ hx, botChain_extend _ _ _ _ hy⟩

/-- A left-side label mismatch extends a solution to the left witness system. -/
theorem lUnsafe_extend (ρ : V k → Tree) (hϕ : Sat ρ ϕ)
    (hx : trace (ρ x) ν = Tree.top) (hy : trace (ρ y) ν ≠ Tree.top) :
    Sat (extend ρ x y ν) (lUnsafe ϕ x y ν) := by
  apply (sat_lUnsafe_iff _).mpr
  exact ⟨by simpa [extend_restrict] using hϕ,
    topChain_extend _ _ _ _ hx, noTopChain_extend _ _ _ _ hy⟩

theorem not_hasLabel_of_label {t : Tree} {ν : List (Fin 2)} {a s : Sym}
    (h : t.fn ν = some a) (hs : s ≠ Sym.f) (ha : a ≠ s) : ¬ HasLabel t ν s := by
  rintro ⟨τ, hp, ht⟩
  by_cases he : τ = ν
  · subst τ; exact ha (Option.some.inj (h.symm.trans ht))
  · have hf := t.label_eq_f_of_proper_prefix hp he (by simp [h])
    exact hs (Option.some.inj (ht.symm.trans hf))

/-- A failed tree comparison has a binary path witnessing a bottom or top label mismatch. -/
theorem not_le_iff_unsafe (t u : Tree) :
    ¬ t ≤ u ↔ ∃ ν, (trace t ν ≠ Tree.bot ∧ trace u ν = Tree.bot) ∨
      (trace t ν = Tree.top ∧ trace u ν ≠ Tree.top) := by
  classical
  constructor
  · intro h
    change ¬ (∀ ν a b, t.fn ν = some a → u.fn ν = some b → a ≤ b) at h
    push Not at h
    obtain ⟨ν, a, b, ht, hu, hab⟩ := h
    have hc : (b = Sym.bot ∧ a ≠ Sym.bot) ∨ (a = Sym.top ∧ b ≠ Sym.top) := by
      cases a <;> cases b <;> simp_all <;> exact absurd hab (by decide)
    refine ⟨ν, ?_⟩
    rcases hc with ⟨rfl, ha⟩ | ⟨rfl, hb⟩
    · exact Or.inl ⟨fun h => not_hasLabel_of_label ht (by decide) ha
        ((trace_eq_bot_iff _ _).mp h),
        (trace_eq_bot_iff _ _).mpr ⟨ν, List.prefix_refl _, hu⟩⟩
    · exact Or.inr ⟨(trace_eq_top_iff _ _).mpr ⟨ν, List.prefix_refl _, ht⟩,
        fun h => not_hasLabel_of_label hu (by decide) hb ((trace_eq_top_iff _ _).mp h)⟩
  · rintro ⟨ν, h⟩ hle
    have hm := trace_mono hle ν
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hy] at hm; exact hx ((Tree.le_bot_iff _).mp hm)
    · rw [hx] at hm; exact hy ((Tree.top_le_iff _).mp hm)

end Safety

/-- Failed entailment is equivalent to satisfiability of a path-witness system on one side. -/
theorem not_entails_iff {ϕ : Constraint k} {x y : V k} :
    ¬ Entails ϕ x y ↔ ∃ ν,
      (∃ ρ', Sat ρ' (rUnsafe ϕ x y ν)) ∨ (∃ ρ', Sat ρ' (lUnsafe ϕ x y ν)) := by
  classical
  constructor
  · intro h
    change ¬ (∀ ρ, Sat ρ ϕ → ρ x ≤ ρ y) at h
    push Not at h
    obtain ⟨ρ, hϕ, hxy⟩ := h
    obtain ⟨ν, hν⟩ := (not_le_iff_unsafe _ _).mp hxy
    refine ⟨ν, ?_⟩
    rcases hν with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨_, rUnsafe_extend ρ hϕ hx hy⟩
    · exact Or.inr ⟨_, lUnsafe_extend ρ hϕ hx hy⟩
  · rintro ⟨ν, ⟨ρ', hs⟩ | ⟨ρ', hs⟩⟩ h
    · obtain ⟨hϕ, hxy⟩ := rUnsafe_sound hs
      exact hxy (h _ hϕ)
    · obtain ⟨hϕ, hxy⟩ := lUnsafe_sound hs
      exact hxy (h _ hϕ)

end DeciNSSE
