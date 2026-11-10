import DeciNSSE.Constraints.Signed
import DeciNSSE.Satisfiability.LeastShape

/-! # Sign duality and the variance shape

Sign duality `σ` reverses a signed literal, exchanges its constants and flips the
signs of its variables. The signed translation is closed under `σ`, so the least
shapes of the two signs of a variable have the same constructor positions. The
variance shape of a variable reads, at each path, the label of the least shape of
its signed copy whose sign is the polarity of the path. Without a label clash in the
signed translation it solves the variance system.

## Main declarations

- `SignDuality.flipV`, `SignDuality.dualFlip`, `SignDuality.FlipClosed`,
  `SignDuality.signed_flipClosed`: sign duality and the closure of the signed
  translation under it.
- `SignDuality.SignCoherent`, `SignDuality.signed_signCoherent`: children carry the sign
  of their parent shifted by their variance.
- `SignDuality.leastShape_flip_f`: the two signs of a variable have the same
  constructor positions in the least shape.
- `varianceShape`, `varianceShape_sat`, `varianceShape_depth`: the variance shape, a
  solution when the signed translation has no label clash, and bounded in depth by
  every depth bound of the least shapes.
- `satisfiable_iff_signed_not_labelClash`: a variance system is satisfiable exactly when its
  signed translation has no label clash.
-/

namespace DeciNSSE.SignDuality

variable {n k : ℕ}

/-- Complement the sign of a signed variable: `u^p ↦ u^{1−p}`. -/
def flipV (z : V (2 * k)) : V (2 * k) := sv (base z) (!(sign z))

@[simp] theorem flipV_sv (u : V k) (p : Bool) : flipV (sv u p) = sv u (!p) := by
  simp [flipV]

@[simp] theorem flipV_flipV (z : V (2 * k)) : flipV (flipV z) = z := by
  obtain ⟨u, p, rfl⟩ := sv_cases z
  simp

@[simp] theorem sign_flipV (z : V (2 * k)) : sign (flipV z) = !(sign z) := by
  simp [flipV]

@[simp] theorem base_flipV (z : V (2 * k)) : base (flipV z) = base z := by
  simp [flipV]

/-- `σ` on literals: reverse constructor literals, swap the constants, flip signs.
Child positions are preserved. -/
def dualFlip : Lit n (2 * k) → Lit n (2 * k)
  | .leF x a => .fLe (flipV ∘ a) (flipV x)
  | .fLe a x => .leF (flipV x) (flipV ∘ a)
  | .eqBot x => .eqTop (flipV x)
  | .eqTop x => .eqBot (flipV x)

@[simp] theorem dualFlip_dualFlip (l : Lit n (2 * k)) : dualFlip (dualFlip l) = l := by
  cases l <;> simp [dualFlip, Function.comp_def]

/-- A signed system is `σ`-closed when it contains the `σ`-image of each literal. -/
def FlipClosed (ψ : Constraint n (2 * k)) : Prop :=
  ∀ l ∈ ψ, dualFlip l ∈ ψ

/-- The signed translation is `σ`-closed: the two signed forms of each original literal
are `σ`-images of each other. -/
theorem signed_flipClosed (c : Fin n → Bool) (ϕ : Constraint n k) :
    FlipClosed (signed c ϕ) := by
  intro l hl
  obtain ⟨m, hm, hl⟩ := List.mem_flatMap.mp hl
  apply List.mem_flatMap.mpr
  refine ⟨m, hm, ?_⟩
  cases m <;> simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
  all_goals rcases hl with rfl | rfl <;> simp [dualFlip, Function.comp_def]

/-- The dual of a literal is a given literal exactly when it is the dual of that literal. -/
theorem dualFlip_eq_iff {l m : Lit n (2 * k)} : dualFlip l = m ↔ l = dualFlip m :=
  ⟨fun h => by rw [← h, dualFlip_dualFlip], fun h => by rw [h, dualFlip_dualFlip]⟩

/-- Renaming the variables of a literal renames the bases of its signed forms. -/
theorem signedLit_rename {K : ℕ} (c : Fin n → Bool) (r : V k → V K) (l : Lit n k) :
    signedLit c (l.rename r) =
      (signedLit c l).map (Lit.rename fun z => sv (r (base z)) (sign z)) := by
  cases l <;> simp [signedLit, Lit.rename, Function.comp_def]

/-- A normalized assignment takes dual values at the two signs of a variable. -/
@[simp] theorem normalized_flipV (c : Fin n → Bool) (ρ : V k → Tree n) (z : V (2 * k)) :
    normalized c ρ (flipV z) = Tree.dual (normalized c ρ z) := by
  simp [normalized]

/-- A normalized assignment satisfies a signed literal exactly when it satisfies its dual. -/
theorem holds_dualFlip_normalized (c : Fin n → Bool) (ρ : V k → Tree n) (l : Lit n (2 * k)) :
    Covariant.holds (normalized c ρ) (dualFlip l) ↔ Covariant.holds (normalized c ρ) l := by
  cases l with
  | leF u a =>
    change Tree.node (fun i => normalized c ρ (flipV (a i))) ≤ normalized c ρ (flipV u) ↔
      normalized c ρ u ≤ Tree.node (normalized c ρ ∘ a)
    simp only [normalized_flipV, ← dual_node, dual_le_iff]; rfl
  | fLe a u =>
    change normalized c ρ (flipV u) ≤ Tree.node (fun i => normalized c ρ (flipV (a i))) ↔
      Tree.node (normalized c ρ ∘ a) ≤ normalized c ρ u
    simp only [normalized_flipV, ← dual_node, dual_le_iff]; rfl
  | eqBot u => simp [dualFlip, Covariant.holds]
  | eqTop u => simp [dualFlip, Covariant.holds]

section Exchange

variable {ψ : Constraint n (2 * k)}

/-- `σ` maps the closure rules to themselves with the endpoints reversed. -/
theorem derives_flip (hc : FlipClosed ψ) {u v : V (2 * k)} (h : Derives ψ u v) :
    Derives ψ (flipV v) (flipV u) := by
  induction h with
  | refl => exact .refl _
  | trans _ _ ih ih' => exact ih'.trans ih
  | decomp i hl _ hu ih => exact Derives.decomp i (hc _ hu) ih (hc _ hl)

/-- `σ` turns a lower path bound `x` of `y` into the upper path bound `σx` of `σy`. -/
theorem lowerAt_flip (hc : FlipClosed ψ) {π : List (Fin n)} {x y : V (2 * k)}
    (h : LowerAt ψ π x y) : UpperAt ψ π (flipV y) (flipV x) := by
  induction h with
  | nil hd => exact .nil (derives_flip hc hd)
  | cons hl hd _ ih => exact .cons (derives_flip hc hd) (hc _ hl) ih

/-- `σ` turns an upper path bound `y` of `x` into the lower path bound `σy` of `σx`. -/
theorem upperAt_flip (hc : FlipClosed ψ) {π : List (Fin n)} {x y : V (2 * k)}
    (h : UpperAt ψ π x y) : LowerAt ψ π (flipV y) (flipV x) := by
  induction h with
  | nil hd => exact .nil (derives_flip hc hd)
  | cons hd hl _ ih => exact .cons (hc _ hl) (derives_flip hc hd) ih

theorem lowerAt_flip_iff (hc : FlipClosed ψ) {π : List (Fin n)} {x y : V (2 * k)} :
    UpperAt ψ π (flipV y) (flipV x) ↔ LowerAt ψ π x y :=
  ⟨fun h => by simpa using upperAt_flip hc h, lowerAt_flip hc⟩

theorem lowerLabel_f_flip (hc : FlipClosed ψ) (z : V (2 * k)) (π : List (Fin n)) :
    LowerLabel ψ π .f z ↔ UpperLabel ψ π .f (flipV z) := by
  constructor
  · rintro ⟨a, y, hl, hp⟩
    exact ⟨flipV y, flipV ∘ a, hc _ hl, lowerAt_flip hc hp⟩
  · rintro ⟨y, b, hl, hp⟩
    exact ⟨flipV ∘ b, flipV y, hc _ hl, by simpa using upperAt_flip hc hp⟩

theorem upperLabel_f_flip (hc : FlipClosed ψ) (z : V (2 * k)) (π : List (Fin n)) :
    UpperLabel ψ π .f z ↔ LowerLabel ψ π .f (flipV z) := by
  have h := lowerLabel_f_flip hc (flipV z) π
  simp only [flipV_flipV] at h
  exact h.symm

/-- The constructor label of the least shape is `σ`-invariant. -/
theorem shapeLabel_flip_f (hc : FlipClosed ψ) (z : V (2 * k)) (π : List (Fin n)) :
    shapeLabel ψ z π = .f ↔ shapeLabel ψ (flipV z) π = .f := by
  rw [shapeLabel_eq_f_iff, shapeLabel_eq_f_iff]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨(upperLabel_f_flip hc z π).mp hu, (lowerLabel_f_flip hc z π).mp hl⟩
  · rintro ⟨hl, hu⟩
    refine ⟨(lowerLabel_f_flip hc z π).mpr hu, ?_⟩
    have h := (lowerLabel_f_flip hc (flipV z) π).mp hl
    simpa using h

theorem active_shape_flip (hc : FlipClosed ψ) (z : V (2 * k)) (π : List (Fin n)) :
    Active (shapeLabel ψ z) π ↔ Active (shapeLabel ψ (flipV z)) π := by
  simp only [Active, shapeLabel_flip_f hc z]

/-- Constructor positions of the least shape agree at `u^p` and `u^{1−p}`. -/
theorem leastShape_flip_f (hc : FlipClosed ψ) (z : V (2 * k)) (π : List (Fin n)) :
    (leastShape ψ z).fn π = some .f ↔ (leastShape ψ (flipV z)).fn π = some .f := by
  classical
  have ha := active_shape_flip hc z π
  have hf := shapeLabel_flip_f hc z π
  rw [leastShape_fn, leastShape_fn]
  split_ifs <;> simp_all

end Exchange

/-- In every constructor literal, child `i` carries the parent sign shifted by `c i`. -/
def SignCoherent (c : Fin n → Bool) (ψ : Constraint n (2 * k)) : Prop :=
  (∀ u a, Lit.leF u a ∈ ψ → ∀ i, sign (a i) = Bool.xor (sign u) (c i)) ∧
    (∀ a u, Lit.fLe a u ∈ ψ → ∀ i, sign (a i) = Bool.xor (sign u) (c i))

theorem signed_signCoherent (c : Fin n → Bool) (ϕ : Constraint n k) :
    SignCoherent c (signed c ϕ) := by
  constructor
  · intro u a h i
    obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
    cases l with
    | leF x b =>
      simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false,
        Lit.leF.injEq, reduceCtorEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp
    | fLe b x =>
      simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false,
        Lit.leF.injEq, reduceCtorEq, false_or] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp
    | eqBot x => simp [signedLit] at hl
    | eqTop x => simp [signedLit] at hl
  · intro a u h i
    obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
    cases l with
    | leF x b =>
      simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false,
        Lit.fLe.injEq, reduceCtorEq, false_or] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp
    | fLe b x =>
      simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false,
        Lit.fLe.injEq, reduceCtorEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp
    | eqBot x => simp [signedLit] at hl
    | eqTop x => simp [signedLit] at hl

end DeciNSSE.SignDuality

namespace DeciNSSE

open SignDuality

variable {n k : ℕ}

/-- The variance shape: at the path `π`, the label of the least shape of the signed
translation at the sign `u^{pol π}`. -/
noncomputable def varianceShape (c : Fin n → Bool) (ϕ : Constraint n k) (u : V k) : Tree n where
  fn π := (leastShape (signed c ϕ) (sv u (polarity c π))).fn π
  wf := by
    refine ⟨(leastShape _ _).wf.1, fun π i => ?_⟩
    rw [Tree.child_isSome_iff, polarity_append_singleton]
    cases hc : c i
    · simp
    · have := leastShape_flip_f (signed_flipClosed c ϕ) (sv u (polarity c π)) π
      simpa using this.symm

@[simp] theorem varianceShape_fn (c : Fin n → Bool) (ϕ : Constraint n k) (u : V k)
    (π : List (Fin n)) :
    (varianceShape c ϕ u).fn π = (leastShape (signed c ϕ) (sv u (polarity c π))).fn π := rfl

/-- Every depth bound of the least shapes of the signed translation bounds the variance
shape. -/
theorem varianceShape_depth {c : Fin n → Bool} {ϕ : Constraint n k} {D : ℕ}
    (hD : ∀ z π, ((leastShape (signed c ϕ) z).fn π).isSome → π.length ≤ D) (u : V k)
    (π : List (Fin n)) (hπ : ((varianceShape c ϕ u).fn π).isSome) : π.length ≤ D :=
  hD _ π hπ

/-- Without a label clash in the signed translation, the variance shape is a solution. -/
theorem varianceShape_sat {c : Fin n → Bool} {ϕ : Constraint n k}
    (hn : ¬ LabelClash (signed c ϕ)) : Sat c (varianceShape c ϕ) ϕ := by
  have hS := leastShape_sat hn
  intro l hl
  cases l with
  | eqBot u =>
    have h0 : leastShape (signed c ϕ) (sv u false) = Tree.bot :=
      hS (.eqBot (sv u false)) (mem_signed hl (by simp [signedLit]))
    change varianceShape c ϕ u = Tree.bot
    exact (Tree.root_eq_bot_iff _).mp (by simp [h0])
  | eqTop u =>
    have h0 : leastShape (signed c ϕ) (sv u false) = Tree.top :=
      hS (.eqTop (sv u false)) (mem_signed hl (by simp [signedLit]))
    change varianceShape c ϕ u = Tree.top
    exact (Tree.root_eq_top_iff _).mp (by simp [h0])
  | leF u a =>
    have hp : leastShape (signed c ϕ) (sv u false) ≤
        Tree.node (leastShape (signed c ϕ) ∘ fun i => sv (a i) (c i)) :=
      hS (.leF (sv u false) fun i => sv (a i) (c i)) (mem_signed hl (by simp [signedLit]))
    have hm : Tree.node (leastShape (signed c ϕ) ∘ fun i => sv (a i) (!(c i))) ≤
        leastShape (signed c ϕ) (sv u true) :=
      hS (.fLe (fun i => sv (a i) (!(c i))) (sv u true)) (mem_signed hl (by simp [signedLit]))
    intro π r s hr hs
    cases π with
    | nil =>
      obtain rfl : s = .f := (Option.some.inj hs).symm
      exact hp [] _ _ hr rfl
    | cons i π =>
      change (leastShape (signed c ϕ) (sv u (polarity c (i :: π)))).fn (i :: π) = some r at hr
      change (leastShape (signed c ϕ) (sv (a i) (polarity c π))).fn π = some s at hs
      rw [polarity_cons] at hr ⊢
      cases hci : c i <;> cases hpi : polarity c π <;> simp only [hci, hpi, Bool.xor_false,
        Bool.xor_true, Bool.not_false, Bool.not_true] at hr hs ⊢
      · exact hp (i :: π) _ _ hr (by simpa [hci] using hs)
      · exact hm (i :: π) _ _ (by simpa [hci] using hs) hr
      · exact hm (i :: π) _ _ (by simpa [hci] using hs) hr
      · exact hp (i :: π) _ _ hr (by simpa [hci] using hs)
  | fLe a u =>
    have hp : Tree.node (leastShape (signed c ϕ) ∘ fun i => sv (a i) (c i)) ≤
        leastShape (signed c ϕ) (sv u false) :=
      hS (.fLe (fun i => sv (a i) (c i)) (sv u false)) (mem_signed hl (by simp [signedLit]))
    have hm : leastShape (signed c ϕ) (sv u true) ≤
        Tree.node (leastShape (signed c ϕ) ∘ fun i => sv (a i) (!(c i))) :=
      hS (.leF (sv u true) fun i => sv (a i) (!(c i))) (mem_signed hl (by simp [signedLit]))
    intro π r s hr hs
    cases π with
    | nil =>
      obtain rfl : r = .f := (Option.some.inj hr).symm
      exact hp [] _ _ rfl hs
    | cons i π =>
      change (leastShape (signed c ϕ) (sv u (polarity c (i :: π)))).fn (i :: π) = some s at hs
      change (leastShape (signed c ϕ) (sv (a i) (polarity c π))).fn π = some r at hr
      rw [polarity_cons] at hs ⊢
      cases hci : c i <;> cases hpi : polarity c π <;> simp only [hci, hpi, Bool.xor_false,
        Bool.xor_true, Bool.not_false, Bool.not_true] at hr hs ⊢
      · exact hp (i :: π) _ _ (by simpa [hci] using hr) hs
      · exact hm (i :: π) _ _ hs (by simpa [hci] using hr)
      · exact hm (i :: π) _ _ hs (by simpa [hci] using hr)
      · exact hp (i :: π) _ _ (by simpa [hci] using hr) hs

/-- A variance system is satisfiable exactly when its signed translation has no label
clash. -/
theorem satisfiable_iff_signed_not_labelClash (c : Fin n → Bool) (ϕ : Constraint n k) :
    Satisfiable c ϕ ↔ ¬ LabelClash (signed c ϕ) :=
  ⟨fun hs hc => hc.unsatisfiable (sat_implies_signed_sat c ϕ hs),
    fun hn => ⟨_, varianceShape_sat hn⟩⟩

end DeciNSSE
