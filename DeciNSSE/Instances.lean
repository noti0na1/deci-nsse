import DeciNSSE.Semantics.Normalisation

/-! # Product and arrow variance

Binary products and arrows are special cases of the same variance-parametric
semantics and decision procedures.
-/

namespace DeciNSSE

/-- Both arguments of the product constructor are covariant. -/
def productVariance : Fin 2 → Bool := fun _ => false

/-- The arrow constructor is contravariant in its domain and covariant in its codomain. -/
def arrowVariance : Fin 2 → Bool := ![true, false]

end DeciNSSE
