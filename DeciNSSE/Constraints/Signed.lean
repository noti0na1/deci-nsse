import DeciNSSE.Constraints.Basic

/-! # Signed translation of variance

Each variable has positive and negative coordinates. Normalisation turns
variance constraints into a covariant system on these doubled variables;
solutions fixed by sign duality decode to solutions of the original system.
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

/-- Complement the sign, then swap all leaves. -/
def Signed.dual (A : V (2 * k) → Tree n) (z : V (2 * k)) : Tree n :=
  Tree.dual (A (sv (base z) (!(sign z))))

@[simp] theorem signedDual_sv (A : V (2 * k) → Tree n) (u : V k) (p : Bool) :
    Signed.dual A (sv u p) = Tree.dual (A (sv u (!p))) := by simp [Signed.dual]

@[simp] theorem signedDual_involutive (A : V (2 * k) → Tree n) : Signed.dual (Signed.dual A) = A := by
  funext z
  obtain ⟨u, p, rfl⟩ := sv_cases z
  simp

@[simp] theorem dual_eq_bot (t : Tree n) : Tree.dual t = Tree.bot ↔ t = Tree.top := by
  constructor
  · intro h; have := congrArg Tree.dual h; simpa using this
  · rintro rfl; simp

@[simp] theorem dual_eq_top (t : Tree n) : Tree.dual t = Tree.top ↔ t = Tree.bot := by
  constructor
  · intro h; have := congrArg Tree.dual h; simpa using this
  · rintro rfl; simp

@[simp] theorem sat_signed_iff (c : Fin n → Bool) (A : V (2 * k) → Tree n)
    (ϕ : Constraint n k) :
    Covariant.Sat A (signed c ϕ) ↔ ∀ l ∈ ϕ, Covariant.Sat A (signedLit c l) := by
  constructor
  · intro h l hl m hm
    exact h m (List.mem_flatMap.mpr ⟨l, hl, hm⟩)
  · intro h m hm
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp hm
    exact h l hl m hm

theorem sat_signedLit_dual_iff (c : Fin n → Bool) (A : V (2 * k) → Tree n) (l : Lit n k) :
    Covariant.Sat (Signed.dual A) (signedLit c l) ↔ Covariant.Sat A (signedLit c l) := by
  cases l <;> simp [signedLit, Covariant.Sat, Covariant.holds, Function.comp_def, ← dual_node, and_comm]

/-- Sign complementation and leaf duality exchange each pair of translated literals. -/
theorem sat_signedDual (c : Fin n → Bool) {A : V (2 * k) → Tree n} {ϕ : Constraint n k}
    (h : Covariant.Sat A (signed c ϕ)) : Covariant.Sat (Signed.dual A) (signed c ϕ) := by
  rw [sat_signed_iff] at h ⊢
  intro l hl
  exact (sat_signedLit_dual_iff c A l).mpr (h l hl)

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

/-- Every normalised valuation is fixed by sign duality. -/
@[simp] theorem normalized_fixed (c : Fin n → Bool) (ρ : V k → Tree n) :
    Signed.dual (normalized c ρ) = normalized c ρ := by
  funext z
  obtain ⟨u, p, rfl⟩ := sv_cases z
  simp

/-- Recover the original tree from the positive sign. -/
def decoded (c : Fin n → Bool) (A : V (2 * k) → Tree n) (u : V k) : Tree n :=
  Tree.normalize c false (A (sv u false))

theorem normalized_decoded (c : Fin n → Bool) {A : V (2 * k) → Tree n}
    (h : Signed.dual A = A) : normalized c (decoded c A) = A := by
  funext z
  obtain ⟨u, p, rfl⟩ := sv_cases z
  cases p
  · simp [decoded]
  · have hh := congrFun h (sv u true)
    simpa [decoded] using hh

theorem fixed_iff_normalized (c : Fin n → Bool) (A : V (2 * k) → Tree n) :
    Signed.dual A = A ↔ ∃ ρ, A = normalized c ρ := by
  constructor
  · intro h; exact ⟨decoded c A, (normalized_decoded c h).symm⟩
  · rintro ⟨ρ, rfl⟩; exact normalized_fixed c ρ

/-- Exactly the fixed signed solutions arise from variance-tree solutions. -/
theorem fixed_solution_correspondence (c : Fin n → Bool) (ϕ : Constraint n k)
    (A : V (2 * k) → Tree n) :
    (Covariant.Sat A (signed c ϕ) ∧ Signed.dual A = A) ↔
      ∃ ρ, Sat c ρ ϕ ∧ A = normalized c ρ := by
  constructor
  · rintro ⟨hs, hf⟩
    obtain ⟨ρ, rfl⟩ := (fixed_iff_normalized c A).mp hf
    exact ⟨ρ, (sat_iff_signed c ρ ϕ).mpr hs, rfl⟩
  · rintro ⟨ρ, hs, rfl⟩
    exact ⟨(sat_iff_signed c ρ ϕ).mp hs, normalized_fixed c ρ⟩

/-- Every variance solution gives a covariant solution of the signed translation. -/
theorem sat_implies_signed_sat (c : Fin n → Bool) (ϕ : Constraint n k)
    (h : ∃ ρ, Sat c ρ ϕ) : ∃ A, Covariant.Sat A (signed c ϕ) := by
  obtain ⟨ρ, hs⟩ := h
  exact ⟨normalized c ρ, (sat_iff_signed c ρ ϕ).mp hs⟩

end DeciNSSE
