import DeciNSSE.Complexity.Unary

/-! # Checks of the arity-one deciders

Kernel evaluation of the arity-one deciders on two variables. For covariant
`f`, the literal `x ≤ f(x)` makes `x` a lower spine `f^a(⊥)` and `f(y) ≤ y`
makes `y` an upper spine `f^b(⊤)`, for `a, b ≤ ω`. A lower spine lies below
every upper spine, so `x ≤ f(x), f(y) ≤ y` entails `x ≤ y` in each tree domain;
two lower spines need not be ordered, so `x ≤ f(x), y ≤ f(y)` entails `x ≤ y`
in none (take `x = f(⊥)` and `y = ⊥`). Both systems are satisfiable over finite
trees, so neither answer is vacuous. For contravariant `f` the first system
still entails `x ≤ y`, while `x ≤ f(y), y ≤ f(x)` does not.

The label readers have `2 * 4^4 = 512` states. In the covariant positive case
neither side reaches its target, so both scans read all 512 states. The checks
are `example`s, so they run on every build and export no declarations.
-/

namespace DeciNSSE.Complexity.Unary

/-- `x ≤ f(x)` and `f(y) ≤ y`: a lower spine and an upper spine. -/
private def lowerUpper : Constraint 1 2 := [.leF 0 ![0], .fLe ![1] 1]

/-- `x ≤ f(x)` and `y ≤ f(y)`: two lower spines. -/
private def lowerLower : Constraint 1 2 := [.leF 0 ![0], .leF 1 ![1]]

/-- `x ≤ f(y)` and `y ≤ f(x)`. -/
private def crossed : Constraint 1 2 := [.leF 0 ![1], .leF 1 ![0]]

/-- The covariant variance at arity one. -/
private def covariant : Fin 1 → Bool := fun _ => false

/-- The contravariant variance at arity one. -/
private def contravariant : Fin 1 → Bool := fun _ => true

/-- The first system has a finite solution. -/
example : SatisfiableFin covariant lowerUpper :=
  (satFinB_iff _ _).mp (by decide +kernel)

/-- The second system has a finite solution. -/
example : SatisfiableFin covariant lowerLower :=
  (satFinB_iff _ _).mp (by decide +kernel)

/-- A lower spine lies below an upper spine, over arbitrary trees. -/
example : Entails covariant lowerUpper 0 1 :=
  (decideEntailsUnary_correct _ _ _ _).mp (by decide +kernel)

/-- A lower spine lies below an upper spine, over regular trees. -/
example : EntailsReg covariant lowerUpper 0 1 :=
  (decideEntailsRegUnary_correct _ _ _ _).mp (by decide +kernel)

/-- A lower spine lies below an upper spine, over finite trees. -/
example : EntailsFin covariant lowerUpper 0 1 :=
  (decideEntailsFinUnary_correct _ _ _ _).mp (by decide +kernel)

/-- Two lower spines need not be ordered, over arbitrary trees. -/
example : ¬ Entails covariant lowerLower 0 1 :=
  fun h => absurd ((decideEntailsUnary_correct _ _ _ _).mpr h) (by decide +kernel)

/-- Two lower spines need not be ordered, over regular trees. -/
example : ¬ EntailsReg covariant lowerLower 0 1 :=
  fun h => absurd ((decideEntailsRegUnary_correct _ _ _ _).mpr h) (by decide +kernel)

/-- Two lower spines need not be ordered, over finite trees. -/
example : ¬ EntailsFin covariant lowerLower 0 1 :=
  fun h => absurd ((decideEntailsFinUnary_correct _ _ _ _).mpr h) (by decide +kernel)

/-- The first system has a finite solution for contravariant `f`. -/
example : SatisfiableFin contravariant lowerUpper :=
  (satFinB_iff _ _).mp (by decide +kernel)

/-- The first system also entails `x ≤ y` for contravariant `f`. -/
example : Entails contravariant lowerUpper 0 1 :=
  (decideEntailsUnary_correct _ _ _ _).mp (by decide +kernel)

/-- For contravariant `f`, `x ≤ f(y), y ≤ f(x)` does not entail `x ≤ y`. -/
example : ¬ Entails contravariant crossed 0 1 :=
  fun h => absurd ((decideEntailsUnary_correct _ _ _ _).mpr h) (by decide +kernel)

end DeciNSSE.Complexity.Unary
