import DeciNSSE.Constraints.Signed
import DeciNSSE.Satisfiability.Cycle
import DeciNSSE.Semantics.Median

/-! # Finite median and symmetrisation

The median of finite trees has bounded depth. A finite fixed signed solution
can serve as the third median input to symmetrise another finite solution.
-/

namespace DeciNSSE.FiniteTransfer

open DeciNSSE.Tree

variable {n k : ℕ}

/-- Finite leaf duality: the finite counterpart of `Tree.dual`. -/
def dualFinite (t : FTree n) : FTree n := FTree.normalize (fun _ => false) true t

@[simp] theorem dualFinite_toTree (t : FTree n) : (dualFinite t).toTree = Tree.dual t.toTree :=
  FTree.normalize_toTree _ _ _

/-- The root symbol of a finite tree. -/
def rootSym : FTree n → Sym
  | .bot => .bot
  | .top => .top
  | .node _ => .f

/-- The `i`-th child of a node; a leaf is its own child (constant extension). -/
def child : FTree n → Fin n → FTree n
  | .node a, i => a i
  | .bot, _ => .bot
  | .top, _ => .top

@[simp] theorem rootSym_bot : rootSym (.bot : FTree n) = .bot := rfl
@[simp] theorem rootSym_top : rootSym (.top : FTree n) = .top := rfl
@[simp] theorem rootSym_node (a : Fin n → FTree n) : rootSym (.node a) = .f := rfl
@[simp] theorem child_bot (i : Fin n) : child (.bot : FTree n) i = .bot := rfl
@[simp] theorem child_top (i : Fin n) : child (.top : FTree n) i = .top := rfl
@[simp] theorem child_node (a : Fin n → FTree n) (i : Fin n) : child (.node a) i = a i := rfl

theorem height_child_le (t : FTree n) (i : Fin n) : (child t i).height ≤ t.height := by
  cases t with
  | bot => simp
  | top => simp
  | node a => exact (FTree.height_child_lt a i).le

theorem height_child_lt_of_root {t : FTree n} (h : rootSym t = .f) (i : Fin n) :
    (child t i).height < t.height := by
  cases t with
  | bot => simp at h
  | top => simp at h
  | node a => exact FTree.height_child_lt a i

/-- A constructor median needs a constructor input. -/
theorem medianSym_eq_f {a b c : Sym} (h : medianSym a b c = .f) :
    a = .f ∨ b = .f ∨ c = .f := by
  revert h
  cases a <;> cases b <;> cases c <;> decide

theorem finiteMedian_decreasing {a b c : FTree n}
    (h : medianSym (rootSym a) (rootSym b) (rootSym c) = .f) (i : Fin n) :
    (child a i).height + (child b i).height + (child c i).height <
      a.height + b.height + c.height := by
  have ha := height_child_le a i
  have hb := height_child_le b i
  have hc := height_child_le c i
  rcases medianSym_eq_f h with h | h | h
  · have := height_child_lt_of_root h i; omega
  · have := height_child_lt_of_root h i; omega
  · have := height_child_lt_of_root h i; omega

set_option linter.unusedVariables false in

/-- The median of three finite trees, computed root by root. The hypothesis `h`
is used by the termination proof. -/
def finiteMedian (a b c : FTree n) : FTree n :=
  if h : medianSym (rootSym a) (rootSym b) (rootSym c) = .f then
    .node fun i => finiteMedian (child a i) (child b i) (child c i)
  else if medianSym (rootSym a) (rootSym b) (rootSym c) = .bot then .bot else .top
termination_by a.height + b.height + c.height
decreasing_by exact finiteMedian_decreasing h i

theorem finiteMedian_of_bot {a b c : FTree n}
    (h : medianSym (rootSym a) (rootSym b) (rootSym c) = .bot) : finiteMedian a b c = .bot := by
  rw [finiteMedian]; simp [h]

theorem finiteMedian_of_top {a b c : FTree n}
    (h : medianSym (rootSym a) (rootSym b) (rootSym c) = .top) : finiteMedian a b c = .top := by
  rw [finiteMedian]; simp [h]

theorem finiteMedian_of_f {a b c : FTree n}
    (h : medianSym (rootSym a) (rootSym b) (rootSym c) = .f) :
    finiteMedian a b c = .node fun i => finiteMedian (child a i) (child b i) (child c i) := by
  rw [finiteMedian]; simp [h]

@[simp] theorem trace_toTree_nil (t : FTree n) : Tree.trace t.toTree [] = rootSym t := by
  cases t <;> rfl

theorem trace_toTree_cons (t : FTree n) (i : Fin n) (w : List (Fin n)) :
    Tree.trace t.toTree (i :: w) = Tree.trace (child t i).toTree w := by
  cases t <;> simp

/-- The finite median is pointwise on constant extensions. -/
theorem trace_finiteMedian (a b c : FTree n) (w : List (Fin n)) :
    Tree.trace (finiteMedian a b c).toTree w =
      medianSym (Tree.trace a.toTree w) (Tree.trace b.toTree w) (Tree.trace c.toTree w) := by
  induction w generalizing a b c with
  | nil =>
    simp only [trace_toTree_nil]
    cases hm : medianSym (rootSym a) (rootSym b) (rootSym c)
    · rw [finiteMedian_of_bot hm]; rfl
    · rw [finiteMedian_of_f hm]; rfl
    · rw [finiteMedian_of_top hm]; rfl
  | cons i w ih =>
    have habs : ∀ t : FTree n, rootSym t ≠ .f →
        Tree.trace t.toTree (i :: w) = rootSym t := fun t ht => by
      have h := trace_absorb t.toTree [] (i :: w) (by simpa using ht)
      simpa using h
    cases hm : medianSym (rootSym a) (rootSym b) (rootSym c) with
    | bot =>
      rw [finiteMedian_of_bot hm]
      have h := medianSym_absorb (rootSym a) (rootSym b) (rootSym c)
        (Tree.trace a.toTree (i :: w)) (Tree.trace b.toTree (i :: w)) (Tree.trace c.toTree (i :: w))
        (habs a) (habs b) (habs c) (by rw [hm]; decide)
      rw [h, hm]; simp
    | top =>
      rw [finiteMedian_of_top hm]
      have h := medianSym_absorb (rootSym a) (rootSym b) (rootSym c)
        (Tree.trace a.toTree (i :: w)) (Tree.trace b.toTree (i :: w)) (Tree.trace c.toTree (i :: w))
        (habs a) (habs b) (habs c) (by rw [hm]; decide)
      rw [h, hm]; simp
    | f =>
      rw [finiteMedian_of_f hm, trace_toTree_cons, child_node, ih, trace_toTree_cons a,
        trace_toTree_cons b, trace_toTree_cons c]

/-- `finite_med`: the median of three finite trees is the finite tree `finiteMedian`. -/
@[simp] theorem finiteMedian_toTree (a b c : FTree n) :
    (finiteMedian a b c).toTree = Tree.median a.toTree b.toTree c.toTree := by
  apply trace_injective
  funext w
  rw [trace_finiteMedian, trace_median]

/-- `sat_med`: the median preserves all four literal forms when all three inputs
solve them (constants use two equal leaves). -/
theorem sat_median3 {A B C : V k → Tree n} {ϕ : Constraint n k}
    (ha : Covariant.Sat A ϕ) (hb : Covariant.Sat B ϕ) (hc : Covariant.Sat C ϕ) :
    Covariant.Sat (fun z => Tree.median (A z) (B z) (C z)) ϕ := by
  intro l hl
  have h₁ := ha l hl
  have h₂ := hb l hl
  have h₃ := hc l hl
  cases l with
  | leF u a =>
    have h := median_mono h₁ h₂ h₃
    rw [median_node] at h
    exact h
  | fLe a u =>
    have h := median_mono h₁ h₂ h₃
    rw [median_node] at h
    exact h
  | eqBot u =>
    change A u = Tree.bot at h₁
    change B u = Tree.bot at h₂
    change Tree.median (A u) (B u) (C u) = Tree.bot
    simp [h₁, h₂]
  | eqTop u =>
    change A u = Tree.top at h₁
    change B u = Tree.top at h₂
    change Tree.median (A u) (B u) (C u) = Tree.top
    simp [h₁, h₂]

/-- Median of a finite signed assignment, its sign dual, and the normalisation of a
finite variance-tree assignment `D`. -/
def symmetrizeFinite (c : Fin n → Bool) (A : V (2 * k) → FTree n) (D : V k → FTree n)
    (z : V (2 * k)) : FTree n :=
  finiteMedian (A z) (dualFinite (A (sv (base z) (!(sign z))))) (FTree.normalize c (sign z) (D (base z)))

@[simp] theorem symmetrizeFinite_toTree (c : Fin n → Bool) (A : V (2 * k) → FTree n)
    (D : V k → FTree n) (z : V (2 * k)) :
    (symmetrizeFinite c A D z).toTree =
      Tree.median (A z).toTree (Signed.dual (FTree.toTree ∘ A) z) (normalized c (FTree.toTree ∘ D) z) := by
  simp [symmetrizeFinite, Signed.dual, normalized]

/-- Finite symmetrisation is fixed by sign duality. -/
theorem symmetrizeFinite_fixed (c : Fin n → Bool) (A : V (2 * k) → FTree n) (D : V k → FTree n) :
    Signed.dual (FTree.toTree ∘ symmetrizeFinite c A D) = FTree.toTree ∘ symmetrizeFinite c A D := by
  funext z
  obtain ⟨u, p, rfl⟩ := sv_cases z
  simp only [signedDual_sv, Function.comp_apply, symmetrizeFinite_toTree, normalized_sv, dual_median,
    dual_involutive, Bool.not_not]
  rw [← normalize_not, Bool.not_not, median_swap]

/-- Finite symmetrisation preserves satisfaction of the signed constraints. -/
theorem symmetrizeFinite_sat {c : Fin n → Bool} {ϕ : Constraint n k}
    {A : V (2 * k) → FTree n} {D : V k → FTree n}
    (ha : Covariant.Sat (FTree.toTree ∘ A) (signed c ϕ))
    (hd : Sat c (FTree.toTree ∘ D) ϕ) :
    Covariant.Sat (FTree.toTree ∘ symmetrizeFinite c A D) (signed c ϕ) := by
  have h := sat_median3 ha (sat_signedDual c ha) ((sat_iff_signed c _ ϕ).mp hd)
  have he : (fun z => Tree.median ((FTree.toTree ∘ A) z) (Signed.dual (FTree.toTree ∘ A) z)
      (normalized c (FTree.toTree ∘ D) z)) = FTree.toTree ∘ symmetrizeFinite c A D := by
    funext z; simp
  rwa [he] at h

/-- Two inputs excluding top keep the median below top. -/
theorem medianSym_ne_top {a b c : Sym} (ha : a ≠ .top) (hb : b ≠ .top) :
    medianSym a b c ≠ .top := by
  revert ha hb
  cases a <;> cases b <;> cases c <;> decide

end DeciNSSE.FiniteTransfer
