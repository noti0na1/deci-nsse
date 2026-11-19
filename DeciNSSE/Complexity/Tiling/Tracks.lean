import DeciNSSE.Monitor.Bridge

/-! # Path bounds on signed copies

## Main declarations

- `Track` transports constructor bounds along a fixed copy of a signed system.
- `Track.path_iff` follows the copy sign along a word.
- `singleTrack` and `doubleTrack` give these transports for the covariant
  emitter and the two-copy variance construction.
-/

namespace DeciNSSE.Complexity.Tiling
open SignDuality
variable {n k m : ℕ}

/-- Form an upper or lower constructor inequality rooted at `u`, according to its orientation. -/
def nodeLit (lower : Bool) (u : V k) (a : Fin n → V k) : Lit n k :=
  if lower then .fLe a u else .leF u a

/-- Form the equation to bottom for an upper bound or to top for a lower bound. -/
def leafLit (lower : Bool) (u : V k) : Lit n k :=
  if lower then .eqTop u else .eqBot u

/-- Signed coordinates agree exactly when both their base variables and their signs agree. -/
theorem sv_eq_iff {u v : V k} {p q : Bool} :
    sv u p = sv v q ↔ u = v ∧ p = q :=
  ⟨fun h => ⟨by simpa using congrArg base h, by simpa using congrArg sign h⟩,
    fun ⟨h₁,h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩

private theorem node_signedLit (l : Lit n k) (c : Fin n → Bool) (b p : Bool) (u : V k) (a) :
    nodeLit b (sv u p) a ∈ signedLit c l ↔
      ∃ t, nodeLit (b ^^ p) u t = l ∧ a = fun i => sv (t i) (p ^^ c i) := by
  cases l <;> cases b <;> cases p <;> simp [nodeLit, signedLit, sv_eq_iff, eq_comm, and_comm]

/-- A signed constructor literal comes from an original literal with the appropriate orientation
and its child signs determined by variance. -/
theorem node_signed (Z : Constraint n k) (c : Fin n → Bool) (b p : Bool) (u : V k) (a) :
    nodeLit b (sv u p) a ∈ signed c Z ↔ ∃ t, nodeLit (b ^^ p) u t ∈ Z ∧
      a = fun i => sv (t i) (p ^^ c i) := by
  simp only [signed, List.mem_flatMap, node_signedLit]
  constructor
  · rintro ⟨l,hl,t,et,he⟩
    exact ⟨t,et ▸ hl,he⟩
  · rintro ⟨t,ht,he⟩
    exact ⟨_,ht,t,rfl,he⟩

/-- A leaf equation at a signed coordinate is the original leaf equation with its orientation
adjusted by the sign. -/
theorem leaf_signed (Z : Constraint n k) (c : Fin n → Bool) (b p : Bool) (u : V k) :
    leafLit b (sv u p) ∈ signed c Z ↔ leafLit (b ^^ p) u ∈ Z := by
  have one (l : Lit n k) : leafLit b (sv u p) ∈ signedLit c l ↔ leafLit (b ^^ p) u = l := by
    cases l <;> cases b <;> cases p <;> simp [leafLit, signedLit, sv_eq_iff, eq_comm]
  simp [signed, one]

/-- No variable is the root of both an upper and a lower constructor literal. -/
def Separated (Z : Constraint n k) : Prop :=
  ∀ x a b, nodeLit true x a ∈ Z → nodeLit false x b ∉ Z

/-- The variable closure of a separated system relates only equal variables. -/
theorem Separated.derives {Z : Constraint n k} (h : Separated Z) {u v}
    (d : Derives Z u v) : u = v := by
  induction d with
  | refl => rfl
  | trans _ _ h₁ h₂ => exact h₁.trans h₂
  | decomp _ hl _ hu ih => exact (h _ _ _ (ih ▸ hl) hu).elim

/-- Signed translation preserves separation of upper and lower constructor roots. -/
theorem Separated.signed {Z : Constraint n k} (h : Separated Z) (c : Fin n → Bool) :
    Separated (DeciNSSE.signed c Z) := by
  intro x a b hl hu
  obtain ⟨x,p,rfl⟩ := sv_cases x
  obtain ⟨a, ha, _⟩ := (node_signed ..).mp hl
  obtain ⟨b, hb, _⟩ := (node_signed ..).mp hu
  cases p <;> first | exact h _ _ _ ha hb | exact h _ _ _ hb ha

/-- Reach a variable by following syntactic upper or lower constructor children. -/
def Trace (Z : Constraint n k) (b : Bool) : List (Fin n) → V k → V k → Prop
  | [], x, z => x = z
  | i :: w, x, z => ∃ a, nodeLit b x a ∈ Z ∧ Trace Z b w (a i) z

/-- A syntactic trace on a concatenation splits at a common intermediate variable. -/
theorem trace_append (Z : Constraint n k) (b : Bool) (u v : List (Fin n)) (x z : V k) :
    Trace Z b (u ++ v) x z ↔ ∃ y, Trace Z b u x y ∧ Trace Z b v y z := by
  induction u generalizing x with
  | nil => simp [Trace]
  | cons i u ih =>
    simp only [List.cons_append, Trace, ih]
    exact ⟨fun ⟨a,ha,y,hy,hz⟩ => ⟨y,⟨a,ha,hy⟩,hz⟩,
      fun ⟨y,⟨a,ha,hy⟩,hz⟩ => ⟨a,ha,y,hy,hz⟩⟩

/-- For separated systems an upper path bound is exactly a trace along upper constructor
children. -/
theorem upper_trace {Z : Constraint n k} (sep : Separated Z) (w) (x z) :
    UpperAt Z w x z ↔ Trace Z false w x z := by
  induction w generalizing x with
  | nil => exact ⟨fun h => sep.derives (upperAt_nil_iff.mp h), fun he => he ▸ .nil (.refl _)⟩
  | cons i w ih =>
    constructor
    · intro h
      cases h with
      | cons d hl ht => cases sep.derives d; exact ⟨_,hl,(ih _).mp ht⟩
    · rintro ⟨a, ha, ht⟩
      exact .cons (.refl _) ha ((ih _).mpr ht)

/-- For separated systems a lower path bound is exactly a trace along lower constructor
children. -/
theorem lower_trace {Z : Constraint n k} (sep : Separated Z) (w) (x z) :
    LowerAt Z w z x ↔ Trace Z true w x z := by
  induction w generalizing x with
  | nil =>
    exact ⟨fun h => (sep.derives (lowerAt_nil_iff.mp h)).symm, fun he => he ▸ .nil (.refl _)⟩
  | cons i w ih =>
    constructor
    · intro h
      cases h with
      | cons hl d ht => cases sep.derives d; exact ⟨_,hl,(ih _).mp ht⟩
    · rintro ⟨a, ha, ht⟩
      exact .cons ha (.refl _) ((ih _).mpr ht)

/-- At sign `p`, a copy carries each child to sign `p xor c i`. The orientation
bit `dual` specifies whether upper and lower bounds are exchanged. -/
structure Track (Z : Constraint n k) (ψ : Constraint n (2*m))
    (c : Fin n → Bool) (dual : Bool) where
  /-- The variable representing a base variable at the given copy sign. -/
  var : Bool → V k → V (2*m)
  /-- Constructor literals pass along the track with the specified orientation and child signs. -/
  node : ∀ b p x a, nodeLit b (var p x) a ∈ ψ ↔
    ∃ t, nodeLit (b ^^ dual) x t ∈ Z ∧ a = fun i => var (p ^^ c i) (t i)
  /-- Leaf equations pass along the track with the specified orientation. -/
  leaf : ∀ b p x, leafLit b (var p x) ∈ ψ ↔ leafLit (b ^^ dual) x ∈ Z
  /-- The relation on copy signs that can represent the same variable. -/
  compatible : Bool → Bool → Prop
  /-- A sign is compatible with itself. -/
  refl : ∀ p, compatible p p
  /-- Copied variables agree exactly when their signs are compatible and their bases agree. -/
  eq : ∀ p q x y, var p x = var q y ↔ compatible p q ∧ x = y
  /-- Flipping a signed variable takes it outside this track. -/
  noFlip : ∀ p q x y, flipV (var p x) ≠ var q y

/-- A trace along a signed copy projects to a base trace whose endpoint copy is fixed by the
path polarity. -/
theorem Track.path_iff {Z : Constraint n k} {ψ : Constraint n (2*m)} {c dual}
    (F : Track Z ψ c dual) (b p : Bool) (w : List (Fin n)) (x z) :
    Trace ψ b w (F.var p x) z ↔
      ∃ y, Trace Z (b ^^ dual) w x y ∧ z = F.var (p ^^ polarity c w) y := by
  induction w generalizing p x with
  | nil => simp [Trace, eq_comm]
  | cons i w ih =>
    simp only [Trace, F.node, polarity_cons, ← Bool.xor_assoc]
    constructor
    · rintro ⟨a,⟨t,ht,rfl⟩,hz⟩
      obtain ⟨y,hy,he⟩ := (ih _ _).mp hz
      exact ⟨y,⟨t,ht,hy⟩,he⟩
    · rintro ⟨y,⟨t,ht,hy⟩,he⟩
      exact ⟨_,⟨t,ht,rfl⟩,(ih _ _).mpr ⟨y,hy,he⟩⟩

/-- With covariant children one signing stays in a single sign block. -/
def singleTrack (Z : Constraint n k) (d : Bool) :
    Track Z (signed (fun _ => false) Z) (fun _ => false) d where
  var _ x := sv x d
  node b p x a := by simpa using node_signed Z (fun _ => false) b d x a
  leaf b p x := leaf_signed ..
  compatible _ _ := True
  refl _ := trivial
  eq p q x y := by simp [sv_eq_iff]
  noFlip p q x y := by simp [sv_eq_iff]

/-- The two-copy construction keeps the original orientation along the whole path. -/
def doubleTrack (Z : Constraint n k) (c : Fin n → Bool) (d : Bool) :
    Track Z (signed c (signed c Z)) c d where
  var p x := sv (sv x p) (d ^^ p)
  node b p x a := by
    rw [node_signed]
    simp only [node_signed]
    have h : ((b ^^ (d ^^ p)) ^^ p) = (b ^^ d) := by cases b <;> cases d <;> cases p <;> rfl
    rw [h]
    have hc (i : Fin n) : ((d ^^ p) ^^ c i) = (d ^^ (p ^^ c i)) := Bool.xor_assoc ..
    simp only [hc]
    exact ⟨fun ⟨_,⟨t,ht,rfl⟩,he⟩ => ⟨t,ht,he⟩,
      fun ⟨t,ht,he⟩ => ⟨_,⟨t,ht,rfl⟩,he⟩⟩
  leaf b p x := by rw [leaf_signed, leaf_signed]; cases b <;> cases p <;> cases d <;> rfl
  compatible := Eq
  refl _ := rfl
  eq p q x y := by simp [sv_eq_iff]; grind
  noFlip p q x y := by simp [sv_eq_iff]

/-- A variable has a bound in the indicated orientation from a constructor literal or an
equation to a leaf. -/
def HasBound (Z : Constraint n k) (b : Bool) (x : V k) :=
  (∃ a, nodeLit b x a ∈ Z) ∨ leafLit b x ∈ Z

/-- A bound at a signed coordinate corresponds to a bound at the base variable with orientation
adjusted by the sign. -/
theorem hasBound_signed (Z : Constraint n k) (c : Fin n → Bool) (b p : Bool) (u : V k) :
    HasBound (signed c Z) b (sv u p) ↔ HasBound Z (b ^^ p) u := by
  simp only [HasBound, node_signed, leaf_signed]
  apply or_congr_left
  exact ⟨fun ⟨_,t,ht,_⟩ => ⟨t,ht⟩, fun ⟨t,ht⟩ => ⟨_,t,ht,rfl⟩⟩

/-- Every variable with an upper bound is free of lower bounds. -/
def Polarized (Z : Constraint n k) := ∀ x, HasBound Z false x → ¬ HasBound Z true x

/-- Signed translation preserves the separation of all upper and lower bounds. -/
theorem Polarized.signed {Z : Constraint n k} (h : Polarized Z) (c : Fin n → Bool) :
    Polarized (DeciNSSE.signed c Z) := by
  intro x hb ht
  obtain ⟨v,p,rfl⟩ := sv_cases x
  rw [hasBound_signed] at hb ht
  cases p <;> first | exact h _ hb ht | exact h _ ht hb

/-- A polarized system has a finite solution for every variance by assigning extreme leaves to
the variables. -/
theorem Polarized.finite {Z : Constraint n k} (h : Polarized Z) (c : Fin n → Bool) :
    SatisfiableFin c Z := by
  classical
  let ρ (v : V k) : FTree n := if HasBound Z false v then .bot else .top
  have bot (v) (hb : HasBound Z false v) : (ρ v).toTree = Tree.bot := by simp [ρ,hb]
  have top (v) (ht : HasBound Z true v) : (ρ v).toTree = Tree.top := by
    simp [ρ,show ¬ HasBound Z false v from fun hb => h v hb ht]
  refine ⟨ρ,?_⟩
  intro l hl
  cases l with
  | eqBot v => exact bot v (Or.inr hl)
  | eqTop v => exact top v (Or.inr hl)
  | leF v a => simp [Lit.holds, treeLe_iff_normalize, bot v (Or.inl ⟨a,hl⟩)]
  | fLe a v => simp [Lit.holds, treeLe_iff_normalize, top v (Or.inl ⟨a,hl⟩)]

/-- A signed track has a constructor bound at a copied variable exactly when the base variable
has the corresponding oriented constructor bound. -/
theorem Track.has_node {Z : Constraint n k} {ψ : Constraint n (2*m)} {c dual}
    (F : Track Z ψ c dual) (b p) (x) :
    (∃ a, nodeLit b (F.var p x) a ∈ ψ) ↔ ∃ t, nodeLit (b ^^ dual) x t ∈ Z := by
  simp only [F.node]
  exact ⟨fun ⟨_,t,ht,_⟩ => ⟨t,ht⟩,fun ⟨t,ht⟩ => ⟨_,t,ht,rfl⟩⟩

end DeciNSSE.Complexity.Tiling
