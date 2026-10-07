import DeciNSSE.Constraints.PathBounds

/-! # Dual constraints

Duality exchanges bottom and top, lower and upper constructor literals, and
the direction of the queried inequality. It transports left witnesses to right
witnesses.
-/

namespace DeciNSSE.ConstraintDual

variable {n k : ℕ} {ϕ : Constraint n k} {x y : V k} {π ν : List (Fin n)}

theorem dual_eq_bot_iff (t : Tree n) : Tree.dual t = Tree.bot ↔ t = Tree.top := by
  constructor
  · intro h; simpa using congrArg Tree.dual h
  · rintro rfl; simp

theorem dual_eq_top_iff (t : Tree n) : Tree.dual t = Tree.top ↔ t = Tree.bot := by
  constructor
  · intro h; simpa using congrArg Tree.dual h
  · rintro rfl; simp

/-- Exchange upper and lower constructor literals, and the two constants. -/
def lit : Lit n k → Lit n k
  | .leF x a => .fLe a x
  | .fLe a x => .leF x a
  | .eqBot x => .eqTop x
  | .eqTop x => .eqBot x

@[simp] theorem lit_lit (l : Lit n k) : lit (lit l) = l := by cases l <;> rfl

theorem lit_injective : Function.Injective (lit (n := n) (k := k)) :=
  Function.LeftInverse.injective lit_lit

/-- Exchange upper and lower literals and swap bottom with top. -/
def _root_.DeciNSSE.Constraint.dual (ϕ : Constraint n k) : Constraint n k := ϕ.map lit

@[simp] theorem constraint_constraint (ϕ : Constraint n k) :
    Constraint.dual (Constraint.dual ϕ) = ϕ := by
  simp only [Constraint.dual, List.map_map]
  have h : (lit (n := n) (k := k)) ∘ lit = id := funext lit_lit
  rw [h, List.map_id]

@[simp] theorem lit_mem (l : Lit n k) : lit l ∈ Constraint.dual ϕ ↔ l ∈ ϕ :=
  List.mem_map_of_injective lit_injective

@[simp] theorem holds_lit (ρ : V k → Tree n) (l : Lit n k) :
    Covariant.holds (Tree.dual ∘ ρ) (lit l) ↔ Covariant.holds ρ l := by
  have hn (a : Fin n → V k) : Tree.node ((Tree.dual ∘ ρ) ∘ a) = Tree.dual (Tree.node (ρ ∘ a)) := by
    rw [dual_node]; rfl
  cases l with
  | leF z a =>
    change Tree.node ((Tree.dual ∘ ρ) ∘ a) ≤ Tree.dual (ρ z) ↔ ρ z ≤ Tree.node (ρ ∘ a)
    rw [hn, dual_le_iff]
  | fLe a z =>
    change Tree.dual (ρ z) ≤ Tree.node ((Tree.dual ∘ ρ) ∘ a) ↔ Tree.node (ρ ∘ a) ≤ ρ z
    rw [hn, dual_le_iff]
  | eqBot z => exact dual_eq_top_iff (ρ z)
  | eqTop z => exact dual_eq_bot_iff (ρ z)

/-- Dualising a valuation preserves satisfaction of the dual constraints. -/
@[simp] theorem sat (ρ : V k → Tree n) : Covariant.Sat (Tree.dual ∘ ρ) (Constraint.dual ϕ) ↔ Covariant.Sat ρ ϕ := by
  simp only [Covariant.Sat, Constraint.dual, List.forall_mem_map, holds_lit]

/-- A solution of the dual system yields a solution of the original system. -/
theorem sat_of_dual {ρ : V k → Tree n} (h : Covariant.Sat ρ (Constraint.dual ϕ)) : Covariant.Sat (Tree.dual ∘ ρ) ϕ := by
  simpa only [constraint_constraint] using (sat (ϕ := Constraint.dual ϕ) ρ).mpr h

/-- Every satisfiable system has a satisfiable dual system. -/
theorem satisfiable (h : ∃ ρ, Covariant.Sat ρ ϕ) : ∃ ρ, Covariant.Sat ρ (Constraint.dual ϕ) := by
  obtain ⟨ρ, hs⟩ := h
  exact ⟨_, (sat ρ).mpr hs⟩

theorem derives {a b : V k} (h : Derives ϕ a b) : Derives (Constraint.dual ϕ) b a := by
  induction h with
  | refl => exact .refl _
  | trans _ _ ih ih' => exact ih'.trans ih
  | decomp i hl _ hu ih => exact .decomp i ((lit_mem _).mpr hu) ih ((lit_mem _).mpr hl)

@[simp] theorem derives_iff {a b : V k} : Derives (Constraint.dual ϕ) a b ↔ Derives ϕ b a := by
  constructor
  · intro h; simpa using derives h
  · exact derives

theorem upper {a b : V k} (h : UpperAt ϕ π a b) : LowerAt (Constraint.dual ϕ) π b a := by
  induction h with
  | nil hd => exact .nil (derives hd)
  | cons hd hl _ ih => exact .cons ((lit_mem _).mpr hl) (derives hd) ih

theorem lower {a b : V k} (h : LowerAt ϕ π a b) : UpperAt (Constraint.dual ϕ) π b a := by
  induction h with
  | nil hd => exact .nil (derives hd)
  | cons hl hd _ ih => exact .cons (derives hd) ((lit_mem _).mpr hl) ih

@[simp] theorem lower_iff {a b : V k} :
    LowerAt (Constraint.dual ϕ) π a b ↔ UpperAt ϕ π b a := by
  constructor
  · intro h; simpa using lower h
  · exact upper

@[simp] theorem upper_iff {a b : V k} :
    UpperAt (Constraint.dual ϕ) π a b ↔ LowerAt ϕ π b a := by
  constructor
  · intro h; simpa using upper h
  · exact lower

end DeciNSSE.ConstraintDual
