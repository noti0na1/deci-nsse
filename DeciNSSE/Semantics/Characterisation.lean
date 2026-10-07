import DeciNSSE.Constraints.Basic

/-! # Semantic characterisations

The pathwise variance order is the greatest fixed point of the constructor rule;
its least fixed point differs at positive arity. Finite terms represent exactly
the trees with finite domains, and finite graphs represent exactly the trees with
finitely many subtrees. Flat constraints express a variable inequality exactly
at positive arity, allowing existential auxiliary variables and distinct inputs.
-/

namespace DeciNSSE.Characterisation

open DeciNSSE.Tree

variable {n : ℕ}

/-- One-step unfolding of the polarised non-structural order:
`⊥ ≤ t`, `t ≤ ⊤`, and `f(a) ≤ f(b)` iff each child pair is related covariantly or
contravariantly according to `c i`. -/
def Step (c : Fin n → Bool) (R : Tree n → Tree n → Prop) (t u : Tree n) : Prop :=
  t = bot ∨ u = top ∨ ∃ a b, t = node a ∧ u = node b ∧
    ∀ i, if c i then R (b i) (a i) else R (a i) (b i)

/-- `Step c` as a monotone map on binary relations. -/
def stepHom (c : Fin n → Bool) :
    (Tree n → Tree n → Prop) →o (Tree n → Tree n → Prop) where
  toFun := Step c
  monotone' := by
    intro R S hRS t u h
    rcases h with h1 | h1 | ⟨a, b, rfl, rfl, hab⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ⟨a, b, rfl, rfl, fun i => ?_⟩)
      have hi := hab i
      cases hc : c i
      · simp only [hc, Bool.false_eq_true, ite_false] at hi ⊢
        exact hRS _ _ hi
      · simp only [hc, ite_true] at hi ⊢
        exact hRS _ _ hi

/-- Coinduction: every post-fixed point of `Step c` is contained in `Tree.Le c`. -/
theorem le_of_postfixed (c : Fin n → Bool) (R : Tree n → Tree n → Prop)
    (hR : ∀ t u, R t u → Step c R t u) : ∀ t u, R t u → Tree.Le c t u := by
  intro t u h π
  induction π generalizing t u with
  | nil =>
    intro a b ha hb
    simp only [polarity_nil, Bool.false_eq_true, ite_false]
    rcases hR t u h with rfl | rfl | ⟨A, B, rfl, rfl, _⟩
    · simp only [bot_fn_nil, Option.some.injEq] at ha; subst ha; exact Sym.bot_le b
    · simp only [top_fn_nil, Option.some.injEq] at hb; subst hb; exact Sym.le_top a
    · simp only [node_fn_nil, Option.some.injEq] at ha hb; subst ha; subst hb; exact le_rfl
  | cons i π ih =>
    intro a b ha hb
    rcases hR t u h with rfl | rfl | ⟨A, B, rfl, rfl, hAB⟩
    · simp at ha
    · simp at hb
    · simp only [node_fn_cons] at ha hb
      have hi := hAB i
      simp only [polarity_cons]
      rcases Bool.eq_false_or_eq_true (c i) with hc | hc
      · simp only [hc, ite_true] at hi
        have := ih (B i) (A i) hi b a hb ha
        rcases Bool.eq_false_or_eq_true (polarity c π) with hp | hp
        · simp only [hp, hc, Bool.true_xor, Bool.not_true, Bool.false_eq_true, ite_false,
            ite_true] at this ⊢
          exact this
        · simp only [hp, hc, Bool.true_xor, Bool.not_false, Bool.false_eq_true, ite_false,
            ite_true] at this ⊢
          exact this
      · simp only [hc, Bool.false_eq_true, ite_false] at hi
        have := ih (A i) (B i) hi a b ha hb
        simpa [hc] using this

/-- The variance order is a post-fixed point of the constructor rule. -/
theorem treeLe_postfixed (c : Fin n → Bool) : Tree.Le c ≤ stepHom c (Tree.Le c) := by
  intro t u h
  exact (treeLe_iff_root_cases c t u).mp h

/-- `Tree.Le c` is exactly the greatest fixed point of the constructor rule. -/
theorem treeLe_eq_gfp (c : Fin n → Bool) : Tree.Le c = OrderHom.gfp (stepHom c) := by
  apply _root_.le_antisymm
  · exact OrderHom.le_gfp _ (treeLe_postfixed c)
  · intro t u h
    apply le_of_postfixed c (OrderHom.gfp (stepHom c)) _ t u h
    intro t' u' h'
    have hfix := OrderHom.map_gfp (stepHom c)
    rw [← hfix] at h'
    exact h'

/-- The tree with a constructor at every path, infinite precisely at positive arity. -/
abbrev fullTree (n : ℕ) : Tree n := (RGraph.allF n).unfold

/-- The inductive (least fixed point) reading is a different relation for `n ≥ 1`:
it does not relate `f^ω` to itself, whereas `Tree.Le c` is reflexive. -/
theorem lfp_misses_fullTree (c : Fin n → Bool) (i0 : Fin n) :
    ¬ OrderHom.lfp (stepHom c) (fullTree n) (fullTree n) := by
  intro h
  let R : Tree n → Tree n → Prop := fun t u => ¬ (t = fullTree n ∧ u = fullTree n)
  have hpre : stepHom c R ≤ R := by
    intro t u hs ⟨ht, hu⟩
    subst ht; subst hu
    have hn := RGraph.allF_unfold_node (n := n)
    rcases hs with h1 | h1 | ⟨a, b, ha, hb, hab⟩
    · exact node_ne_bot _ (hn.symm.trans h1)
    · exact node_ne_top _ (hn.symm.trans h1)
    · have ea : a = fun _ => fullTree n := (node_eq_node_iff _ _).mp (ha.symm.trans hn)
      have eb : b = fun _ => fullTree n := (node_eq_node_iff _ _).mp (hb.symm.trans hn)
      subst ea; subst eb
      have hi := hab i0
      cases hc : c i0 <;> simp [hc, R] at hi
  exact OrderHom.lfp_le _ hpre _ _ h ⟨rfl, rfl⟩

/-- The least fixed point of the constructor rule is not `Tree.Le c` (for `n ≥ 1`). -/
theorem lfp_ne_treeLe (c : Fin n → Bool) (i0 : Fin n) :
    OrderHom.lfp (stepHom c) ≠ Tree.Le c := by
  intro h
  exact lfp_misses_fullTree c i0 (h ▸ treeLe_refl c (fullTree n))

/-- The polarity of a path is the parity of its number of contravariant letters. -/
theorem polarity_eq_odd (c : Fin n → Bool) (π : List (Fin n)) :
    polarity c π = decide (Odd (π.countP (fun i => c i))) := by
  induction π with
  | nil => simp
  | cons i π ih =>
    rw [polarity_cons, ih, List.countP_cons]
    cases c i
    · simp
    · simp only [Bool.true_xor, ite_true, Nat.odd_add_one]
      by_cases ho : Odd (π.countP (fun i => c i)) <;> simp [ho]

/-- A constructor tree is never below bottom in the variance order. -/
theorem not_node_treeLe_bot (c : Fin n → Bool) (a : Fin n → Tree n) :
    ¬ Tree.Le c (node a) bot := by simp
/-- Top is never below a constructor tree in the variance order. -/
theorem not_top_treeLe_node (c : Fin n → Bool) (a : Fin n → Tree n) :
    ¬ Tree.Le c top (node a) := by simp
/-- Top is never below bottom in the variance order. -/
theorem not_top_treeLe_bot (c : Fin n → Bool) : ¬ Tree.Le c (top : Tree n) bot := by simp
/-- Bottom is below top for every variance. -/
theorem bot_treeLe_top (c : Fin n → Bool) : Tree.Le c (bot : Tree n) top := bot_treeLe c _

/-- Strictness of the label order is inherited: `⊥ < f(a) < ⊤` in `Tree.Le c`. -/
theorem bot_lt_node_lt_top (c : Fin n → Bool) (a : Fin n → Tree n) :
    (Tree.Le c bot (node a) ∧ ¬ Tree.Le c (node a) bot) ∧
      (Tree.Le c (node a) top ∧ ¬ Tree.Le c top (node a)) := by simp

/-- The textbook inductive order on finite terms, indexed by a polarity `p`:
`LeF c s false u` means `s ≤ u`, and `LeF c s true u` means `u ≤ s`. -/
def LeF (c : Fin n → Bool) : FTree n → Bool → FTree n → Prop
  | .bot, false, _ => True
  | .bot, true, u => u = .bot
  | .top, false, u => u = .top
  | .top, true, _ => True
  | .node a, p, u =>
    match u with
    | .bot => p = true
    | .top => p = false
    | .node b => ∀ i, LeF c (a i) (Bool.xor p (c i)) (b i)

/-- The inductive order `LeF` agrees with `Tree.Le c` on `toTree` images, at both polarities. -/
theorem leF_iff (c : Fin n → Bool) (s : FTree n) (p : Bool) (u : FTree n) :
    LeF c s p u ↔
      if p then Tree.Le c u.toTree s.toTree else Tree.Le c s.toTree u.toTree := by
  induction s generalizing p u with
  | bot =>
    cases p
    · simp [LeF]
    · simp only [LeF, ite_true, FTree.toTree_bot, treeLe_bot_iff]
      rw [← FTree.toTree_bot]
      exact FTree.toTree_injective.eq_iff.symm
  | top =>
    cases p
    · simp only [LeF, Bool.false_eq_true, ite_false, FTree.toTree_top, top_treeLe_iff]
      rw [← FTree.toTree_top]
      exact FTree.toTree_injective.eq_iff.symm
    · simp [LeF]
  | node a ih =>
    cases u with
    | bot => cases p <;> simp [LeF]
    | top => cases p <;> simp [LeF]
    | node b =>
      simp only [LeF, FTree.toTree_node, node_treeLe_node_iff, ih]
      cases p
      · simp
      · simp only [Bool.true_xor, ite_true]
        apply forall_congr'
        intro i
        cases c i <;> simp

/-- In particular, for `s u : FTree n`, `Tree.Le c s.toTree u.toTree` is the inductive order. -/
theorem treeLe_toTree_iff_leF (c : Fin n → Bool) (s u : FTree n) :
    Tree.Le c s.toTree u.toTree ↔ LeF c s false u := by
  rw [leF_iff]; simp

/-- The domain of a path tree. -/
def domain (t : Tree n) : Set (List (Fin n)) := {π | (t.fn π).isSome}

/-- Every finite term has a finite path domain. -/
theorem domain_toTree_finite (s : FTree n) : (domain s.toTree).Finite := by
  induction s with
  | bot =>
    apply (Set.finite_singleton ([] : List (Fin n))).subset
    intro π h
    cases π with
    | nil => rfl
    | cons i π => simp [domain] at h
  | top =>
    apply (Set.finite_singleton ([] : List (Fin n))).subset
    intro π h
    cases π with
    | nil => rfl
    | cons i π => simp [domain] at h
  | node a ih =>
    apply ((Set.finite_singleton ([] : List (Fin n))).union
      (Set.finite_iUnion (fun i => (ih i).image (List.cons i)))).subset
    intro π h
    cases π with
    | nil => exact Or.inl rfl
    | cons i π =>
      refine Or.inr (Set.mem_iUnion.mpr ⟨i, π, ?_, rfl⟩)
      simpa [domain] using h

/-- A uniform bound on path lengths gives a finite term representing the tree. -/
theorem exists_ftree_of_bounded :
    ∀ (N : ℕ) (t : Tree n), (∀ π, (t.fn π).isSome → π.length < N) →
      ∃ s : FTree n, s.toTree = t := by
  intro N
  induction N with
  | zero =>
    intro t h
    exact absurd (h [] t.root_isSome) (by simp)
  | succ N ih =>
    intro t h
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · exact ⟨.bot, rfl⟩
    · exact ⟨.top, rfl⟩
    · have hc : ∀ i, ∃ s : FTree n, s.toTree = a i := by
        intro i
        apply ih (a i)
        intro π hπ
        have := h (i :: π) (by simpa using hπ)
        simp at this
        omega
      choose s hs using hc
      exact ⟨.node s, by simp [hs]⟩

/-- The finite embedding hits exactly the trees with a finite domain. -/
theorem toTree_range_iff (t : Tree n) :
    (∃ s : FTree n, s.toTree = t) ↔ (domain t).Finite := by
  constructor
  · rintro ⟨s, rfl⟩; exact domain_toTree_finite s
  · intro hfin
    obtain ⟨B, hB⟩ := (hfin.image List.length).bddAbove
    apply exists_ftree_of_bounded (B + 1) t
    intro π hπ
    have : π.length ≤ B := hB ⟨π, hπ, rfl⟩
    omega

/-- The set of subtrees of a tree. -/
def subtrees (t : Tree n) : Set (Tree n) := {u | ∃ π, t.subtree π = some u}

/-- The subtree at the empty path is the tree itself. -/
theorem subtree_nil (t : Tree n) : t.subtree [] = some t := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
    ((subtree_isSome_iff t []).mpr t.root_isSome)
  rw [hv]
  congr 1
  apply Tree.ext; funext ρ
  rw [subtree_fn hv ρ]; rfl

/-- Taking a child of a subtree appends its child index to the path. -/
theorem subtree_branch {t u : Tree n} {π : List (Fin n)} (h : t.subtree π = some u)
    (i : Fin n) (hf : u.fn [] = some Sym.f) :
    t.subtree (π ++ [i]) = some (u.branch i hf) := by
  have hπ : t.fn π = some Sym.f := by rw [← hf, subtree_fn h []]; simp
  have hdom : (t.fn (π ++ [i])).isSome := (t.child_isSome_iff π i).mpr hπ
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((subtree_isSome_iff t _).mpr hdom)
  rw [hv]
  congr 1
  apply Tree.ext; funext ρ
  rw [subtree_fn hv ρ]
  change t.fn (π ++ [i] ++ ρ) = u.fn (i :: ρ)
  rw [subtree_fn h]
  simp [List.append_assoc]

/-- Every subtree of an unfolding is obtained by rerooting the finite graph. -/
theorem subtree_unfold (g : RGraph n) {π : List (Fin n)} {u : Tree n}
    (h : g.unfold.subtree π = some u) : ∃ p, u = (g.reroot p).unfold := by
  have hdom : (g.unfold.fn π).isSome := (subtree_isSome_iff _ _).mp (by simp [h])
  obtain ⟨p, hp⟩ : ∃ p, g.walk π = some p := by
    rw [RGraph.unfold_fn] at hdom
    exact Option.isSome_iff_exists.mp (by simpa using hdom)
  refine ⟨p, Tree.ext (funext fun ρ => ?_)⟩
  rw [subtree_fn h ρ, RGraph.unfold_fn, RGraph.unfold_fn]
  change (g.walkFrom g.root (π ++ ρ)).map g.label =
    ((g.reroot p).walkFrom p ρ).map g.label
  rw [RGraph.walkFrom_append, RGraph.walkFrom_reroot]
  change ((g.walk π).bind _).map _ = _
  rw [hp]; rfl

/-- A finite graph unfolds to a tree with finitely many subtrees. -/
theorem unfold_regular (g : RGraph n) : (subtrees g.unfold).Finite := by
  apply (Set.finite_range (fun p : Fin g.size => (g.reroot p).unfold)).subset
  rintro u ⟨π, h⟩
  obtain ⟨p, hp⟩ := subtree_unfold g h
  exact ⟨p, hp.symm⟩

section Construction
variable (t : Tree n) (hS : (subtrees t).Finite)

/-- Each subtree belongs to the finite enumeration of subtrees. -/
theorem mem_toFinset_of_subtree {π : List (Fin n)} {u : Tree n}
    (h : t.subtree π = some u) : u ∈ hS.toFinset := hS.mem_toFinset.mpr ⟨π, h⟩

/-- Label of a subtree: its root symbol. -/
def rootLabel (u : Tree n) : Sym := (u.fn []).getD Sym.bot

/-- The root label is the symbol read at the empty path. -/
theorem fn_nil_eq_rootLabel (u : Tree n) : u.fn [] = some (rootLabel u) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp u.root_isSome
  simp [rootLabel, ha]

/-- Each constructor child remains in the finite enumeration of subtrees. -/
theorem branch_mem (u : hS.toFinset) (i : Fin n) (hf : u.val.fn [] = some Sym.f) :
    u.val.branch i hf ∈ hS.toFinset := by
  obtain ⟨π, hπ⟩ := hS.mem_toFinset.mp u.property
  exact mem_toFinset_of_subtree t hS (subtree_branch hπ i hf)

/-- The graph whose nodes are the finitely many subtrees of `t` (a semantic witness). -/
noncomputable def graphOf : RGraph n where
  size := hS.toFinset.card
  root := hS.toFinset.equivFin ⟨t, mem_toFinset_of_subtree t hS (subtree_nil t)⟩
  label := fun p => rootLabel (hS.toFinset.equivFin.symm p).val
  child := fun p i =>
    if hf : (hS.toFinset.equivFin.symm p).val.fn [] = some Sym.f then
      hS.toFinset.equivFin ⟨_, branch_mem t hS _ i hf⟩
    else p

/-- Walking the subtree graph reads the corresponding tree labels. -/
theorem graphOf_walkFrom (ρ : List (Fin n)) (p : Fin (graphOf t hS).size) :
    ((graphOf t hS).walkFrom p ρ).map (graphOf t hS).label =
      (hS.toFinset.equivFin.symm p).val.fn ρ := by
  induction ρ generalizing p with
  | nil =>
    change some (rootLabel _) = _
    exact (fn_nil_eq_rootLabel _).symm
  | cons i ρ ih =>
    have hlab : (graphOf t hS).label p = rootLabel (hS.toFinset.equivFin.symm p).val := rfl
    by_cases hf : (hS.toFinset.equivFin.symm p).val.fn [] = some Sym.f
    · have hl : (graphOf t hS).label p = Sym.f := by
        rw [hlab]; have := fn_nil_eq_rootLabel (hS.toFinset.equivFin.symm p).val
        rw [hf] at this; exact (Option.some.inj this).symm
      have hc : (graphOf t hS).child p i =
          hS.toFinset.equivFin ⟨_, branch_mem t hS _ i hf⟩ := by
        simp only [graphOf]
        exact dite_eq_left hf
      rw [RGraph.walkFrom, ite_eq_left hl, ih, hc, Equiv.symm_apply_apply]
      rfl
    · have hl : (graphOf t hS).label p ≠ Sym.f := by
        rw [hlab]; intro h'
        apply hf
        rw [fn_nil_eq_rootLabel, h']
      rw [RGraph.walkFrom, ite_eq_right hl]
      exact (fn_cons_eq_none_of_root_ne_f _ hf i ρ).symm

/-- The graph of finitely many subtrees unfolds to the original tree. -/
theorem graphOf_unfold : (graphOf t hS).unfold = t := by
  apply Tree.ext; funext ρ
  rw [RGraph.unfold_fn]
  change ((graphOf t hS).walkFrom (graphOf t hS).root ρ).map (graphOf t hS).label = _
  rw [graphOf_walkFrom]
  change (hS.toFinset.equivFin.symm (hS.toFinset.equivFin _)).val.fn ρ = _
  rw [Equiv.symm_apply_apply]

end Construction

/-- The regular embedding hits exactly the regular trees (finitely many subtrees). -/
theorem unfold_range_iff (t : Tree n) :
    (∃ g : RGraph n, g.unfold = t) ↔ (subtrees t).Finite := by
  constructor
  · rintro ⟨g, rfl⟩; exact unfold_regular g
  · intro hS; exact ⟨graphOf t hS, graphOf_unfold t hS⟩

/-- Finite trees are regular. -/
theorem subtrees_finite_of_domain_finite (t : Tree n) (h : (domain t).Finite) :
    (subtrees t).Finite := by
  apply (h.image (fun π => (t.subtree π).getD t)).subset
  rintro u ⟨π, hπ⟩
  refine ⟨π, ?_, by simp [hπ]⟩
  show (t.fn π).isSome
  exact (subtree_isSome_iff t π).mp (by simp [hπ])

/-- Entailment over all trees implies entailment over regular trees. -/
theorem entails_toReg (c : Fin n → Bool) {k : ℕ} (ϕ : Constraint n k) (x y : V k)
    (h : Entails c ϕ x y) : EntailsReg c ϕ x y :=
  fun _ hσ => h _ hσ

/-- Entailment over regular trees implies entailment over finite trees. -/
theorem entailsReg_toFin (c : Fin n → Bool) {k : ℕ} (ϕ : Constraint n k) (x y : V k)
    (h : EntailsReg c ϕ x y) : EntailsFin c ϕ x y := by
  intro σ hσ
  choose g hg using fun v => (unfold_range_iff (σ v).toTree).mpr
    (subtrees_finite_of_domain_finite _ (domain_toTree_finite (σ v)))
  have hcomp : RGraph.unfold ∘ g = FTree.toTree ∘ σ := funext hg
  have := h g (by rw [hcomp]; exact hσ)
  simpa [hg] using this

/-- The child vector `(v, u, …, u)`. -/
def firstChild {m : ℕ} (v u : Tree (m + 1)) : Fin (m + 1) → Tree (m + 1) :=
  fun i => if i = 0 then v else u

/-- `x ≤ y ↔ ∃ z u, f(x', u, …) ≤ z ∧ z ≤ f(y', u, …)` with `(x', y') = (x, y)` if the
first coordinate is covariant and `(y, x)` if it is contravariant. Both conjuncts are
literals of `Lit` (`fLe` and `leF`). -/
theorem le_expressible {m : ℕ} (c : Fin (m + 1) → Bool) (x y : Tree (m + 1)) :
    Tree.Le c x y ↔ ∃ z u : Tree (m + 1),
      Tree.Le c (node (firstChild (if c 0 then y else x) u)) z ∧
      Tree.Le c z (node (firstChild (if c 0 then x else y) u)) := by
  constructor
  · intro h
    refine ⟨node (firstChild (if c 0 then y else x) bot), bot, treeLe_refl _ _, ?_⟩
    apply (node_treeLe_node_iff ..).mpr
    intro i
    by_cases hi : i = 0
    · subst hi
      cases hc : c 0 <;> simp [firstChild, h]
    · simp only [firstChild, hi, ite_false]
      split <;> exact treeLe_refl _ _
  · rintro ⟨z, u, h1, h2⟩
    have h3 := (node_treeLe_node_iff ..).mp (treeLe_trans h1 h2) 0
    cases hc : c 0 <;> simp_all [firstChild]

/-- Two flat literals express order between variables `0` and `1`, with auxiliaries `2` and `3`. -/
def leSystem {m : ℕ} (c : Fin (m + 1) → Bool) : Constraint (m + 1) 4 :=
  [.fLe (fun i => if i = 0 then (if c 0 then 1 else 0) else 3) 2,
   .leF 2 (fun i => if i = 0 then (if c 0 then 0 else 1) else 3)]

/-- Existentially assigning the two auxiliary variables expresses the queried order. -/
theorem leSystem_iff {m : ℕ} (c : Fin (m + 1) → Bool) (ρ : V 4 → Tree (m + 1)) :
    (∃ tz tu : Tree (m + 1), Sat c (fun v => if v = 2 then tz else if v = 3 then tu
      else ρ v) (leSystem c)) ↔ Tree.Le c (ρ 0) (ρ 1) := by
  rw [le_expressible]
  have key : ∀ (tz tu : Tree (m + 1)) (b : Bool),
      ((fun v : V 4 => if v = 2 then tz else if v = 3 then tu else ρ v) ∘
        (fun i : Fin (m + 1) => if i = 0 then (if b then (1 : V 4) else 0) else 3)) =
        firstChild (if b then ρ 1 else ρ 0) tu := by
    intro tz tu b
    funext i
    by_cases hi : i = 0 <;> cases b <;> simp [firstChild, hi]
  have key' : ∀ (tz tu : Tree (m + 1)) (b : Bool),
      ((fun v : V 4 => if v = 2 then tz else if v = 3 then tu else ρ v) ∘
        (fun i : Fin (m + 1) => if i = 0 then (if b then (0 : V 4) else 1) else 3)) =
        firstChild (if b then ρ 0 else ρ 1) tu := by
    intro tz tu b
    funext i
    by_cases hi : i = 0 <;> cases b <;> simp [firstChild, hi]
  simp only [Sat, leSystem, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Lit.holds, key, key']
  simp

/-- The single variable a literal of arity zero talks about. -/
def nullaryVar {k : ℕ} : Lit 0 k → V k
  | .leF x _ => x
  | .fLe _ x => x
  | .eqBot x => x
  | .eqTop x => x

/-- A nullary literal depends only on its single variable. -/
theorem holds_zero_local {k : ℕ} (c : Fin 0 → Bool) (ρ ρ' : V k → Tree 0)
    (l : Lit 0 k) (h : ρ (nullaryVar l) = ρ' (nullaryVar l)) :
    Lit.holds c ρ l ↔ Lit.holds c ρ' l := by
  have hv : ∀ a : Fin 0 → V k, ρ ∘ a = ρ' ∘ a := fun a => funext fun i => i.elim0
  cases l with
  | leF x a => simp only [Lit.holds, nullaryVar] at h ⊢; rw [h, hv a]
  | fLe a x => simp only [Lit.holds, nullaryVar] at h ⊢; rw [h, hv a]
  | eqBot x => simp only [Lit.holds, nullaryVar] at h ⊢; rw [h]
  | eqTop x => simp only [Lit.holds, nullaryVar] at h ⊢; rw [h]

/-- At `n = 0` no flat constraint `ϕ` (possibly with auxiliary variables) defines
`x ≤ y` for distinct `x y`: the solution set of `ϕ` is a product of per-variable sets. -/
theorem nullary_not_definable {k : ℕ} (c : Fin 0 → Bool) (x y : V k) (hxy : x ≠ y) :
    ¬ ∃ ϕ : Constraint 0 k, ∀ ρ : V k → Tree 0,
      (∃ ρ' : V k → Tree 0, ρ' x = ρ x ∧ ρ' y = ρ y ∧ Sat c ρ' ϕ) ↔
        Tree.Le c (ρ x) (ρ y) := by
  rintro ⟨ϕ, hϕ⟩
  obtain ⟨ρ1, h1x, h1y, h1⟩ := (hϕ (fun _ => bot)).mpr (treeLe_refl _ _)
  obtain ⟨ρ2, h2x, h2y, h2⟩ := (hϕ (fun _ => top)).mpr (treeLe_refl _ _)
  let ρ3 : V k → Tree 0 := fun v => if v = x then ρ2 v else ρ1 v
  have h3 : Sat c ρ3 ϕ := by
    intro l hl
    by_cases hv : nullaryVar l = x
    · exact (holds_zero_local c ρ3 ρ2 l (by simp [ρ3, hv])).mpr (h2 l hl)
    · exact (holds_zero_local c ρ3 ρ1 l (by simp [ρ3, hv])).mpr (h1 l hl)
  have hle := (hϕ ρ3).mp ⟨ρ3, rfl, rfl, h3⟩
  have e3x : ρ3 x = top := by simp [ρ3, h2x]
  have e3y : ρ3 y = bot := by simp [ρ3, Ne.symm hxy, h1y]
  rw [e3x, e3y] at hle
  exact not_top_treeLe_bot c hle

/-- A flat system with two existential auxiliaries defines order exactly at positive arity. -/
theorem le_definable_iff (c : Fin n → Bool) :
    (∃ ϕ : Constraint n 4, ∀ ρ : V 4 → Tree n,
      (∃ ρ' : V 4 → Tree n, ρ' 0 = ρ 0 ∧ ρ' 1 = ρ 1 ∧ Sat c ρ' ϕ) ↔
        Tree.Le c (ρ 0) (ρ 1)) ↔ 0 < n := by
  cases n with
  | zero =>
    exact iff_of_false (nullary_not_definable c 0 1 (by decide)) (by omega)
  | succ m =>
    refine iff_of_true ?_ (by omega)
    refine ⟨leSystem c, fun ρ => ?_⟩
    constructor
    · rintro ⟨ρ', hx, hy, hs⟩
      have he : (fun v : V 4 => if v = 2 then ρ' 2 else if v = 3 then ρ' 3
          else ρ' v) = ρ' := by
        funext v
        by_cases h2 : v = 2 <;> by_cases h3 : v = 3 <;> simp [h2, h3]
      have hle := (leSystem_iff c ρ').mp ⟨ρ' 2, ρ' 3, by simpa only [he] using hs⟩
      simpa only [hx, hy] using hle
    · intro hle
      obtain ⟨tz, tu, hs⟩ := (leSystem_iff c ρ).mpr hle
      exact ⟨_, by simp, by simp, hs⟩

/-- Non-vacuity: the empty system does not entail `x ≤ y` (any arity, any variance). -/
theorem nil_not_entails (c : Fin n → Bool) : ¬ Entails c ([] : Constraint n 2) 0 1 := by
  intro h
  have := h (fun v => if v = 0 then top else bot) (by simp [Sat])
  simp at this

end DeciNSSE.Characterisation
