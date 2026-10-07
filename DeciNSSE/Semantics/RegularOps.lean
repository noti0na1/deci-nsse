import DeciNSSE.Constraints.Signed
import DeciNSSE.Semantics.Median

/-! # Regularity of tree operations

Finite graphs realise duality, variance normalisation and median. Product
graphs track the inputs to median, with extreme leaves treated as absorbing
states before pruning.
-/

namespace DeciNSSE

namespace RegularVariance

open DeciNSSE.Tree

variable {n : ℕ}

theorem reroot_root (g : RGraph n) : g.reroot g.root = g := by cases g; rfl

@[simp] theorem reroot_reroot (g : RGraph n) (p q : Fin g.size) :
    (g.reroot p).reroot q = g.reroot q := rfl

@[simp] theorem reroot_label (g : RGraph n) (p : Fin g.size) :
    (g.reroot p).label = g.label := rfl

@[simp] theorem reroot_child (g : RGraph n) (p : Fin g.size) :
    (g.reroot p).child = g.child := rfl

theorem unfold_reroot_fn (g : RGraph n) (p : Fin g.size) (w : List (Fin n)) :
    (g.reroot p).unfold.fn w = (g.walkFrom p w).map g.label := by
  change ((g.reroot p).walkFrom p w).map g.label = _
  rw [RGraph.walkFrom_reroot]

/-- A graph presents a tree family when root labels agree with the states and every
constructor state steps, along each child index, to the child's tree. -/
theorem unfold_reroot_of_family (G : RGraph n) (t : Fin G.size → Tree n)
    (hroot : ∀ q, (t q).fn [] = some (G.label q))
    (hstep : ∀ q, G.label q = Sym.f → ∀ i, Safety.descend (t q) i = t (G.child q i))
    (q : Fin G.size) : (G.reroot q).unfold = t q := by
  have key : ∀ (w : List (Fin n)) (q : Fin G.size),
      (G.walkFrom q w).map G.label = (t q).fn w := by
    intro w
    induction w with
    | nil => intro q; exact (hroot q).symm
    | cons i w ih =>
      intro q
      by_cases hf : G.label q = Sym.f
      · rw [RGraph.walkFrom, ite_eq_left hf, ih, ← hstep q hf i]
        have hq : (t q).fn [] = some Sym.f := by rw [hroot, hf]
        simp [Safety.descend, hq, Tree.branch]
      · rw [RGraph.walkFrom, ite_eq_right hf]
        have hq : (t q).fn [] ≠ some Sym.f := by
          rw [hroot]; exact fun h => hf (Option.some.inj h)
        rw [Tree.fn_cons_eq_none_of_root_ne_f _ hq]
        rfl
  apply Tree.ext
  funext w
  rw [unfold_reroot_fn, key]

/-- The same lemma at the distinguished root. -/
theorem unfold_of_family (G : RGraph n) (t : Fin G.size → Tree n)
    (hroot : ∀ q, (t q).fn [] = some (G.label q))
    (hstep : ∀ q, G.label q = Sym.f → ∀ i, Safety.descend (t q) i = t (G.child q i)) :
    G.unfold = t G.root := by
  conv_lhs => rw [← reroot_root G]
  exact unfold_reroot_of_family G t hroot hstep G.root

/-- Keep a leaf state absorbing; follow the edge at constructor states. -/
def next (g : RGraph n) (q : Fin g.size) (i : Fin n) : Fin g.size :=
  if g.label q = Sym.f then g.child q i else q

theorem next_of_f {g : RGraph n} {q : Fin g.size} (h : g.label q = Sym.f) (i : Fin n) :
    next g q i = g.child q i := ite_eq_left h

theorem unfold_reroot_root_fn (g : RGraph n) (q : Fin g.size) :
    (g.reroot q).unfold.fn [] = some (g.label q) := rfl

/-- Absorbing leaf states realise the leaf-freezing descent. -/
theorem descend_unfold_reroot (g : RGraph n) (q : Fin g.size) (i : Fin n) :
    Safety.descend (g.reroot q).unfold i = (g.reroot (next g q i)).unfold := by
  cases hl : g.label q with
  | bot =>
    have he : (g.reroot q).unfold = Tree.bot := RGraph.unfold_bot _ hl
    simp [next, hl, he]
  | top =>
    have he : (g.reroot q).unfold = Tree.top := RGraph.unfold_top _ hl
    simp [next, hl, he]
  | f =>
    rw [RGraph.unfold_node (g.reroot q) hl, Safety.descend_node, next_of_f hl]
    rfl

theorem trace_cons (t : Tree n) (i : Fin n) (w : List (Fin n)) :
    Tree.trace t (i :: w) = Tree.trace (Safety.descend t i) w := by
  simp [Tree.trace]

theorem fn_nil_eq_trace (t : Tree n) : t.fn [] = some (Tree.trace t []) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp t.root_isSome
  rw [hs, trace_of_fn hs]

/-- The median commutes with leaf-freezing descent, with no side condition. -/
theorem descend_median (a b c : Tree n) (i : Fin n) :
    Safety.descend (Tree.median a b c) i =
      Tree.median (Safety.descend a i) (Safety.descend b i) (Safety.descend c i) := by
  apply trace_injective
  funext w
  rw [← trace_cons, trace_median, trace_median, trace_cons, trace_cons, trace_cons]

theorem median_fn_nil (a b c : Tree n) :
    (Tree.median a b c).fn [] = some (medianSym (Tree.trace a []) (Tree.trace b []) (Tree.trace c [])) := by
  rw [fn_nil_eq_trace, trace_median]

theorem descend_dual (t : Tree n) (i : Fin n) :
    Safety.descend (Tree.dual t) i = Tree.dual (Safety.descend t i) := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩ <;> simp

theorem descend_normalize (c : Fin n → Bool) (p : Bool) {t : Tree n}
    (hf : t.fn [] = some Sym.f) (i : Fin n) :
    Safety.descend (Tree.normalize c p t) i = Tree.normalize c (Bool.xor p (c i)) (Safety.descend t i) := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
  · simp at hf
  · simp at hf
  · simp

/-- Swap `⊥` and `⊤` on every state; edges are unchanged. -/
def dualGraph (g : RGraph n) : RGraph n where
  size := g.size
  root := g.root
  label q := Sym.flip true (g.label q)
  child := g.child

theorem dualGraph_root_fn (g : RGraph n) (q : Fin g.size) :
    (Tree.dual (g.reroot q).unfold).fn [] = some ((dualGraph g).label q) := by
  rw [dual_fn, unfold_reroot_root_fn]
  rfl

theorem dualGraph_step (g : RGraph n) (q : Fin g.size) (hq : (dualGraph g).label q = Sym.f)
    (i : Fin n) :
    Safety.descend (Tree.dual (g.reroot q).unfold) i = Tree.dual (g.reroot ((dualGraph g).child q i)).unfold := by
  have hf : g.label q = Sym.f := (Sym.flip_eq_f true _).mp hq
  rw [descend_dual, descend_unfold_reroot, next_of_f hf]
  rfl

/-- The dual graph unfolds to the dual tree. -/
theorem unfold_dualGraph (g : RGraph n) : (dualGraph g).unfold = Tree.dual g.unfold := by
  rw [unfold_of_family (dualGraph g) (fun q => Tree.dual (g.reroot q).unfold)
    (fun q => dualGraph_root_fn g q) (fun q hq i => dualGraph_step g q hq i)]
  exact congrArg (fun h => Tree.dual (RGraph.unfold h)) (reroot_root g)

/-- States are pairs of a graph state and a polarity bit, encoded by `sv`. -/
def normalizeGraph (c : Fin n → Bool) (p : Bool) (g : RGraph n) : RGraph n where
  size := 2 * g.size
  root := sv g.root p
  label z := Sym.flip (sign z) (g.label (base z))
  child z i := sv (g.child (base z) i) (Bool.xor (sign z) (c i))

theorem normalizeGraph_root_fn (c : Fin n → Bool) (p : Bool) (g : RGraph n)
    (z : Fin (2 * g.size)) :
    (Tree.normalize c (sign z) (g.reroot (base z)).unfold).fn [] = some ((normalizeGraph c p g).label z) := by
  rw [normalize_fn, unfold_reroot_root_fn]
  show _ = some (Sym.flip (sign z) (g.label (base z)))
  simp

theorem normalizeGraph_step (c : Fin n → Bool) (p : Bool) (g : RGraph n) (z : Fin (2 * g.size))
    (hz : (normalizeGraph c p g).label z = Sym.f) (i : Fin n) :
    Safety.descend (Tree.normalize c (sign z) (g.reroot (base z)).unfold) i =
      Tree.normalize c (sign ((normalizeGraph c p g).child z i))
        (g.reroot (base ((normalizeGraph c p g).child z i))).unfold := by
  have hf : g.label (base z) = Sym.f := (Sym.flip_eq_f _ _).mp hz
  have hr : (g.reroot (base z)).unfold.fn [] = some Sym.f := by
    rw [unfold_reroot_root_fn, hf]
  rw [descend_normalize c (sign z) hr, descend_unfold_reroot, next_of_f hf]
  show _ = Tree.normalize c (sign (sv (g.child (base z) i) (Bool.xor (sign z) (c i))))
    (g.reroot (base (sv (g.child (base z) i) (Bool.xor (sign z) (c i))))).unfold
  rw [sign_sv, base_sv]

/-- The graph with a polarity bit unfolds to the normalised tree. -/
theorem unfold_normalizeGraph (c : Fin n → Bool) (p : Bool) (g : RGraph n) :
    (normalizeGraph c p g).unfold = Tree.normalize c p g.unfold := by
  rw [unfold_of_family (normalizeGraph c p g)
    (fun z : Fin (2 * g.size) => Tree.normalize c (sign z) (g.reroot (base z)).unfold)
    (fun z => normalizeGraph_root_fn c p g z) (fun z hz i => normalizeGraph_step c p g z hz i)]
  show Tree.normalize c (sign (sv g.root p)) (g.reroot (base (sv g.root p))).unfold = _
  rw [sign_sv, base_sv, reroot_root]

namespace Med

variable {a b c : ℕ}

/-- Encode a triple of states. -/
def enc (q₁ : Fin a) (q₂ : Fin b) (q₃ : Fin c) : Fin (a * (b * c)) :=
  finProdFinEquiv (q₁, finProdFinEquiv (q₂, q₃))

/-- The first component of a median product-graph state. -/
def p₁ (s : Fin (a * (b * c))) : Fin a := (finProdFinEquiv.symm s).1

/-- The second component of a median product-graph state. -/
def p₂ (s : Fin (a * (b * c))) : Fin b := (finProdFinEquiv.symm (finProdFinEquiv.symm s).2).1

/-- The third component of a median product-graph state. -/
def p₃ (s : Fin (a * (b * c))) : Fin c := (finProdFinEquiv.symm (finProdFinEquiv.symm s).2).2

@[simp] theorem p₁_enc (q₁ : Fin a) (q₂ : Fin b) (q₃ : Fin c) : p₁ (enc q₁ q₂ q₃) = q₁ := by
  simp [p₁, enc]

@[simp] theorem p₂_enc (q₁ : Fin a) (q₂ : Fin b) (q₃ : Fin c) : p₂ (enc q₁ q₂ q₃) = q₂ := by
  simp [p₂, enc]

@[simp] theorem p₃_enc (q₁ : Fin a) (q₂ : Fin b) (q₃ : Fin c) : p₃ (enc q₁ q₂ q₃) = q₃ := by
  simp [p₃, enc]

end Med

/-- The pointwise median label of a product state. -/
def medLabel (g₁ g₂ g₃ : RGraph n) (s : Fin (g₁.size * (g₂.size * g₃.size))) : Sym :=
  medianSym (g₁.label (Med.p₁ s)) (g₂.label (Med.p₂ s)) (g₃.label (Med.p₃ s))

/-- Triple product with absorbing leaf states (constant extension), pruned below
extreme median labels. -/
def medianGraph (g₁ g₂ g₃ : RGraph n) : RGraph n where
  size := g₁.size * (g₂.size * g₃.size)
  root := Med.enc g₁.root g₂.root g₃.root
  label := medLabel g₁ g₂ g₃
  child s i :=
    if medLabel g₁ g₂ g₃ s = Sym.f then
      Med.enc (next g₁ (Med.p₁ s) i) (next g₂ (Med.p₂ s) i) (next g₃ (Med.p₃ s) i)
    else s

theorem trace_unfold_reroot_nil (g : RGraph n) (q : Fin g.size) :
    Tree.trace (g.reroot q).unfold [] = g.label q :=
  trace_of_fn (unfold_reroot_root_fn g q)

/-- The tree family presented by the product states. -/
noncomputable def medFamily (g₁ g₂ g₃ : RGraph n) (s : Fin (g₁.size * (g₂.size * g₃.size))) :
    Tree n :=
  Tree.median (g₁.reroot (Med.p₁ s)).unfold (g₂.reroot (Med.p₂ s)).unfold (g₃.reroot (Med.p₃ s)).unfold

theorem medianGraph_root_fn (g₁ g₂ g₃ : RGraph n) (s : Fin (g₁.size * (g₂.size * g₃.size))) :
    (medFamily g₁ g₂ g₃ s).fn [] = some ((medianGraph g₁ g₂ g₃).label s) := by
  rw [medFamily, median_fn_nil, trace_unfold_reroot_nil, trace_unfold_reroot_nil,
    trace_unfold_reroot_nil]
  rfl

theorem medianGraph_step (g₁ g₂ g₃ : RGraph n) (s : Fin (g₁.size * (g₂.size * g₃.size)))
    (hs : (medianGraph g₁ g₂ g₃).label s = Sym.f) (i : Fin n) :
    Safety.descend (medFamily g₁ g₂ g₃ s) i =
      medFamily g₁ g₂ g₃ ((medianGraph g₁ g₂ g₃).child s i) := by
  have hc : (medianGraph g₁ g₂ g₃).child s i =
      Med.enc (next g₁ (Med.p₁ s) i) (next g₂ (Med.p₂ s) i) (next g₃ (Med.p₃ s) i) :=
    ite_eq_left hs
  rw [hc, medFamily, medFamily, descend_median, descend_unfold_reroot, descend_unfold_reroot,
    descend_unfold_reroot, Med.p₁_enc, Med.p₂_enc, Med.p₃_enc]

/-- The product graph unfolds to the median of its three input trees. -/
theorem unfold_medianGraph (g₁ g₂ g₃ : RGraph n) :
    (medianGraph g₁ g₂ g₃).unfold = Tree.median g₁.unfold g₂.unfold g₃.unfold := by
  rw [unfold_of_family (medianGraph g₁ g₂ g₃) (medFamily g₁ g₂ g₃)
    (fun s => medianGraph_root_fn g₁ g₂ g₃ s) (fun s hs i => medianGraph_step g₁ g₂ g₃ s hs i)]
  show medFamily g₁ g₂ g₃ (Med.enc g₁.root g₂.root g₃.root) = _
  rw [medFamily, Med.p₁_enc, Med.p₂_enc, Med.p₃_enc, reroot_root, reroot_root, reroot_root]

/-- The one-state all-constructor graph presents `Tree.full`, at every arity. -/
theorem unfold_allF : (RGraph.allF n).unfold = (Tree.full : Tree n) := by
  apply Tree.ext
  funext w
  rw [RGraph.allF_unfold_fn, full_fn]

end RegularVariance

end DeciNSSE
