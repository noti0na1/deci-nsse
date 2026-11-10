import DeciNSSE.Constraints.Basic

/-! # Signed translation of variance

Each variable has positive and negative coordinates. Normalization turns
variance constraints into a covariant system on these doubled variables: a
variance assignment solves a system exactly when its two normalizations solve
the signed translation.

## Main declarations

- `sv`, `base`, `sign`: signed variables, their base variables and their signs.
- `signedLit`, `signed`: the signed translation of a literal and of a system.
- `normalized`: the signed assignment of the two normalizations of a variance assignment.
- `sat_iff_signed`: a variance assignment solves a system exactly when its normalized
  assignment solves the signed translation.
-/

namespace DeciNSSE

variable {n k : ℕ}

/-- The positive block comes first, followed by the negative block. -/
def sv (u : V k) (p : Bool) : V (2 * k) :=
  ⟨if p then k + u.val else u.val, by cases p <;> simp <;> omega⟩

/-- The original variable underlying a signed coordinate. -/
def base (z : V (2 * k)) : V k :=
  if h : z.val < k then ⟨z.val, h⟩ else ⟨z.val - k, by omega⟩

/-- The polarity bit of a signed coordinate. -/
def sign (z : V (2 * k)) : Bool := if z.val < k then false else true

@[simp] theorem base_sv (u : V k) (p : Bool) : base (sv u p) = u := by
  cases p <;> apply Fin.ext <;> simp [base, sv, u.isLt, show ¬ k + u.val < k by omega]

@[simp] theorem sign_sv (u : V k) (p : Bool) : sign (sv u p) = p := by
  cases p <;> simp [sign, sv, u.isLt, show ¬ k + u.val < k by omega]

@[simp] theorem sv_base_sign (z : V (2 * k)) : sv (base z) (sign z) = z := by
  apply Fin.ext
  by_cases h : z.val < k
  · simp [sv, base, sign, h]
  · simp [sv, base, sign, h]; omega

theorem sv_cases (z : V (2 * k)) : ∃ u p, z = sv u p :=
  ⟨base z, sign z, (sv_base_sign z).symm⟩

/-- Each original literal contributes its positive and negative covariant forms. -/
def signedLit (c : Fin n → Bool) : Lit n k → Constraint n (2 * k)
  | .leF u a => [.leF (sv u false) (fun i => sv (a i) (c i)),
      .fLe (fun i => sv (a i) (!(c i))) (sv u true)]
  | .fLe a u => [.fLe (fun i => sv (a i) (c i)) (sv u false),
      .leF (sv u true) (fun i => sv (a i) (!(c i)))]
  | .eqBot u => [.eqBot (sv u false), .eqTop (sv u true)]
  | .eqTop u => [.eqTop (sv u false), .eqBot (sv u true)]

/-- Translate each literal to its positive and negative covariant forms. -/
def signed (c : Fin n → Bool) (ϕ : Constraint n k) : Constraint n (2 * k) :=
  ϕ.flatMap (signedLit c)

theorem mem_signed {c : Fin n → Bool} {ϕ : Constraint n k} {l : Lit n k} (hl : l ∈ ϕ)
    {m : Lit n (2 * k)} (hm : m ∈ signedLit c l) : m ∈ signed c ϕ :=
  List.mem_flatMap.mpr ⟨l, hl, hm⟩

@[simp] theorem sat_signed_iff (c : Fin n → Bool) (A : V (2 * k) → Tree n)
    (ϕ : Constraint n k) :
    Covariant.Sat A (signed c ϕ) ↔ ∀ l ∈ ϕ, Covariant.Sat A (signedLit c l) := by
  constructor
  · intro h l hl m hm
    exact h m (List.mem_flatMap.mpr ⟨l, hl, hm⟩)
  · intro h m hm
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp hm
    exact h l hl m hm

/-- The assignment induced by an actual variance-tree assignment. -/
def normalized (c : Fin n → Bool) (ρ : V k → Tree n) (z : V (2 * k)) : Tree n :=
  Tree.normalize c (sign z) (ρ (base z))

@[simp] theorem normalized_sv (c : Fin n → Bool) (ρ : V k → Tree n) (u : V k) (p : Bool) :
    normalized c ρ (sv u p) = Tree.normalize c p (ρ u) := by simp [normalized]

@[simp] theorem normalize_not (c : Fin n → Bool) (p : Bool) (t : Tree n) :
    Tree.normalize c (!p) t = Tree.dual (Tree.normalize c p t) := by cases p <;> simp

@[simp] theorem normalize_false_eq_bot (c : Fin n → Bool) (t : Tree n) :
    Tree.normalize c false t = Tree.bot ↔ t = Tree.bot := by
  constructor
  · intro h; have := congrArg (Tree.normalize c false) h; simpa using this
  · rintro rfl; simp

@[simp] theorem normalize_false_eq_top (c : Fin n → Bool) (t : Tree n) :
    Tree.normalize c false t = Tree.top ↔ t = Tree.top := by
  constructor
  · intro h; have := congrArg (Tree.normalize c false) h; simpa using this
  · rintro rfl; simp

theorem holds_iff_signedLit (c : Fin n → Bool) (ρ : V k → Tree n) (l : Lit n k) :
    Lit.holds c ρ l ↔ Covariant.Sat (normalized c ρ) (signedLit c l) := by
  cases l <;> simp [signedLit, Covariant.Sat, Covariant.holds, Lit.holds,
    treeLe_iff_normalize, Function.comp_def, ← dual_node]

/-- The two signs are the two normalizations of the same tree. -/
theorem sat_iff_signed (c : Fin n → Bool) (ρ : V k → Tree n) (ϕ : Constraint n k) :
    Sat c ρ ϕ ↔ Covariant.Sat (normalized c ρ) (signed c ϕ) := by
  simp only [sat_signed_iff, Sat, holds_iff_signedLit]

/-- Every variance solution gives a covariant solution of the signed translation. -/
theorem sat_implies_signed_sat (c : Fin n → Bool) (ϕ : Constraint n k)
    (h : Satisfiable c ϕ) : ∃ A, Covariant.Sat A (signed c ϕ) := by
  obtain ⟨ρ, hs⟩ := h
  exact ⟨normalized c ρ, (sat_iff_signed c ρ ϕ).mp hs⟩

end DeciNSSE
