import DeciNSSE.Constraints.Signed
import DeciNSSE.Satisfiability.LeastShape

/-! # A finite selector for signed solutions

The least-shape solution and its sign dual have the same constructor positions.
Selecting between their labels according to variable sign and path polarity
preserves this common finite domain and produces a fixed signed solution.
Sign coherence makes both sides of each literal select from the same solution.
-/

namespace DeciNSSE.FiniteVariance

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

/-- The sign dual reads the opposite sign. -/
theorem signedDual_eq_flipV (A : V (2 * k) → Tree n) (z : V (2 * k)) :
    Signed.dual A z = Tree.dual (A (flipV z)) := rfl

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

/-- Each source literal produces exactly one `σ`-pair of signed literals. -/
theorem signed_flipClosed (c : Fin n → Bool) (ϕ : Constraint n k) :
    FlipClosed (signed c ϕ) := by
  intro l hl
  obtain ⟨m, hm, hl⟩ := List.mem_flatMap.mp hl
  apply List.mem_flatMap.mpr
  refine ⟨m, hm, ?_⟩
  cases m <;> simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
  all_goals rcases hl with rfl | rfl <;> simp [dualFlip, Function.comp_def]

section Exchange

variable {ψ : Constraint n (2 * k)}

/-- `σ` maps the closure rules to themselves with the endpoints reversed. -/
theorem derives_flip (hc : FlipClosed ψ) {u v : V (2 * k)} (h : Derives ψ u v) :
    Derives ψ (flipV v) (flipV u) := by
  induction h with
  | refl => exact .refl _
  | trans _ _ ih ih' => exact ih'.trans ih
  | decomp i hl _ hu ih => exact Derives.decomp i (hc _ hu) ih (hc _ hl)

/-- `σ` maps `LowerAt.nil/cons` to `UpperAt.nil/cons`. -/
theorem lowerAt_flip (hc : FlipClosed ψ) {π : List (Fin n)} {x y : V (2 * k)}
    (h : LowerAt ψ π x y) : UpperAt ψ π (flipV y) (flipV x) := by
  induction h with
  | nil hd => exact .nil (derives_flip hc hd)
  | cons hl hd _ ih => exact .cons (derives_flip hc hd) (hc _ hl) ih

/-- `σ` maps `UpperAt.nil/cons` to `LowerAt.nil/cons`. -/
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

/-- Two trees with the same constructor positions (hence the same domain). -/
def SameShape (a b : Tree n) : Prop := ∀ π, a.fn π = some .f ↔ b.fn π = some .f

theorem SameShape.domain {a b : Tree n} (h : SameShape a b) (π : List (Fin n)) :
    (a.fn π).isSome = (b.fn π).isSome := by
  apply Bool.eq_iff_iff.mpr
  induction π using List.reverseRecOn with
  | nil => simp [Tree.root_isSome]
  | append_singleton π i => simp only [Tree.child_isSome_iff, h π]

theorem SameShape.symm {a b : Tree n} (h : SameShape a b) : SameShape b a :=
  fun π => (h π).symm

/-- Read `b` where `p ⊕ pol(π) = 1` and `a` elsewhere; the shapes must agree. -/
def mix (c : Fin n → Bool) (p : Bool) (a b : Tree n) (h : SameShape a b) : Tree n where
  fn π := if Bool.xor p (polarity c π) then b.fn π else a.fn π
  wf := by
    constructor
    · cases p
      · simpa using a.wf.1
      · simpa using b.wf.1
    · intro π i
      have hd := h.domain (π ++ [i])
      have hf := h π
      cases Bool.xor p (polarity c (π ++ [i])) <;>
        cases Bool.xor p (polarity c π) <;> simp_all [Tree.child_isSome_iff]

@[simp] theorem mix_fn (c : Fin n → Bool) (p : Bool) (a b : Tree n) (h : SameShape a b)
    (π : List (Fin n)) :
    (mix c p a b h).fn π = if Bool.xor p (polarity c π) then b.fn π else a.fn π := rfl

theorem mix_domain (c : Fin n → Bool) (p : Bool) (a b : Tree n) (h : SameShape a b)
    (π : List (Fin n)) : ((mix c p a b h).fn π).isSome = (a.fn π).isSome := by
  simp only [mix_fn]; split <;> simp_all [h.domain π]

/-- The least-shape solution of a flip-closed system has the same shape as its sign dual. -/
theorem leastShape_sameShape_dual {ψ : Constraint n (2 * k)} (hc : FlipClosed ψ)
    (z : V (2 * k)) : SameShape (leastShape ψ z) (Signed.dual (leastShape ψ) z) := by
  intro π
  rw [signedDual_eq_flipV]
  exact (leastShape_flip_f hc z π).trans
    (normalize_constructor (fun _ => false) true (leastShape ψ (flipV z)) π).symm

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

/-- The selector `M`: `B` at even signed polarity `p ⊕ pol(π) = 0`, `Signed.dual B` at odd. -/
def select (c : Fin n → Bool) (B : V (2 * k) → Tree n)
    (h : ∀ z, SameShape (B z) (Signed.dual B z)) (z : V (2 * k)) : Tree n :=
  mix c (sign z) (B z) (Signed.dual B z) (h z)

theorem select_fn (c : Fin n → Bool) (B : V (2 * k) → Tree n)
    (h : ∀ z, SameShape (B z) (Signed.dual B z)) (z : V (2 * k)) (π : List (Fin n)) :
    (select c B h z).fn π =
      if Bool.xor (sign z) (polarity c π) then (Signed.dual B z).fn π else (B z).fn π := rfl

/-- `M` has the domain of `B`. -/
theorem select_domain (c : Fin n → Bool) (B : V (2 * k) → Tree n)
    (h : ∀ z, SameShape (B z) (Signed.dual B z)) (z : V (2 * k)) (π : List (Fin n)) :
    ((select c B h z).fn π).isSome = ((B z).fn π).isSome :=
  mix_domain _ _ _ _ _ _

/-- `M` is finite (of bounded depth) whenever `B` is. -/
theorem select_depth (c : Fin n → Bool) (B : V (2 * k) → Tree n)
    (h : ∀ z, SameShape (B z) (Signed.dual B z)) {D : ℕ}
    (hB : ∀ z π, ((B z).fn π).isSome → π.length ≤ D) (z : V (2 * k)) (π : List (Fin n))
    (hπ : ((select c B h z).fn π).isSome) : π.length ≤ D :=
  hB z π (by rwa [select_domain] at hπ)

/-- `Signed.dual M = M`, from `Signed.dual B = C` and `Signed.dual C = B`. -/
theorem select_fixed (c : Fin n → Bool) (B : V (2 * k) → Tree n)
    (h : ∀ z, SameShape (B z) (Signed.dual B z)) : Signed.dual (select c B h) = select c B h := by
  funext z
  obtain ⟨u, p, rfl⟩ := sv_cases z
  apply Tree.ext; funext π
  simp only [signedDual_sv, dual_fn, select_fn, sign_sv, Bool.not_not]
  cases p <;> cases polarity c π <;> simp [Option.map_map, Function.comp_def]

/-- `M` satisfies every sign-coherent system satisfied by both `B` and `Signed.dual B`. -/
theorem select_sat_of_coherent {c : Fin n → Bool} {ψ : Constraint n (2 * k)}
    (hψ : SignCoherent c ψ) {B : V (2 * k) → Tree n} (hs : Covariant.Sat B ψ) (hS : Covariant.Sat (Signed.dual B) ψ)
    (h : ∀ z, SameShape (B z) (Signed.dual B z)) : Covariant.Sat (select c B h) ψ := by
  intro l hl
  have hb := hs l hl
  have hc := hS l hl
  cases l with
  | eqBot u =>
    change B u = Tree.bot at hb
    change Signed.dual B u = Tree.bot at hc
    change select c B h u = Tree.bot
    apply Tree.ext; funext π
    simp only [select_fn, hb, hc, ite_self]
  | eqTop u =>
    change B u = Tree.top at hb
    change Signed.dual B u = Tree.top at hc
    change select c B h u = Tree.top
    apply Tree.ext; funext π
    simp only [select_fn, hb, hc, ite_self]
  | leF u a =>
    change B u ≤ Tree.node (B ∘ a) at hb
    change Signed.dual B u ≤ Tree.node (Signed.dual B ∘ a) at hc
    change select c B h u ≤ Tree.node (select c B h ∘ a)
    intro π r s hr hs'
    cases π with
    | nil =>
      have he : s = .f := (Option.some.inj hs').symm
      subst he
      rw [select_fn] at hr
      split at hr
      · exact hc [] _ _ hr rfl
      · exact hb [] _ _ hr rfl
    | cons i π =>
      have hs'' : (select c B h (a i)).fn π = some s := hs'
      rw [select_fn, polarity_cons, ← Bool.xor_assoc] at hr
      rw [select_fn, hψ.1 u a hl i] at hs''
      split at hr <;> rename_i he
      · rw [ite_eq_left he] at hs''
        exact hc (i :: π) _ _ hr hs''
      · rw [ite_eq_right he] at hs''
        exact hb (i :: π) _ _ hr hs''
  | fLe a u =>
    change Tree.node (B ∘ a) ≤ B u at hb
    change Tree.node (Signed.dual B ∘ a) ≤ Signed.dual B u at hc
    change Tree.node (select c B h ∘ a) ≤ select c B h u
    intro π r s hr hs'
    cases π with
    | nil =>
      have he : r = .f := (Option.some.inj hr).symm
      subst he
      rw [select_fn] at hs'
      split at hs'
      · exact hc [] _ _ rfl hs'
      · exact hb [] _ _ rfl hs'
    | cons i π =>
      have hr' : (select c B h (a i)).fn π = some r := hr
      rw [select_fn, polarity_cons, ← Bool.xor_assoc] at hs'
      rw [select_fn, hψ.2 a u hl i] at hr'
      split at hs' <;> rename_i he
      · rw [ite_eq_left he] at hr'
        exact hc (i :: π) _ _ hr' hs'
      · rw [ite_eq_right he] at hr'
        exact hb (i :: π) _ _ hr' hs'

/-- `M` satisfies the signed translation whenever `B` does. -/
theorem select_sat {c : Fin n → Bool} {ϕ : Constraint n k} {B : V (2 * k) → Tree n}
    (hs : Covariant.Sat B (signed c ϕ)) (h : ∀ z, SameShape (B z) (Signed.dual B z)) :
    Covariant.Sat (select c B h) (signed c ϕ) :=
  select_sat_of_coherent (signed_signCoherent c ϕ) hs (sat_signedDual c hs) h

end DeciNSSE.FiniteVariance
