import DeciNSSE.Holes.Hierarchy.Expansion
import DeciNSSE.Holes.Hierarchy.Derived
import DeciNSSE.Holes.Hierarchy.Canonical
import DeciNSSE.Holes.Hierarchy.Starts
import DeciNSSE.Holes.Hierarchy.Unary
import DeciNSSE.Holes.Hierarchy.Reader

/-! # The canonical hierarchy of words

Repeated decomposition at the last letter produces derived alphabets and
monitors. Expansion preserves holes; each level adds one start core, while
non-unary levels shorten the canonical word. This module imports the six
parts of the development.

## Reading order

1. `Hierarchy/Expansion`: expansion `σ_ℓ`, its cuts and the alignment of its
   comparisons.
2. `Hierarchy/Derived`: the derived monitor `Der(D, ℓ)` and `isHole_der_iff`,
   the one-level desubstitution of holes.
3. `Hierarchy/Canonical`: the tower of derived monitors, the canonical
   hierarchy `hierOf w` and `isHole_hierOf_iff`, which carries holes through
   all levels.
4. `Hierarchy/Starts`: start cores and `startCore_invariants`.
5. `Hierarchy/Unary`: unary levels and the pumping bound
   `exists_unary_hole_iff`.
6. `Hierarchy/Reader`: the lettered monitor `ofReader M R T` of a reader and
   `isHole_ofReader_iff`.

## Main declarations

- `expand`, `alignment`: expansion and its comparisons.
- `der`, `isHole_der_iff`: derived monitors and desubstitution.
- `tower`, `hierOf`, `markOf`, `isHole_tower_iff`, `isHole_hierOf_iff`: the
  canonical hierarchy.
- `sCount`, `startCore_invariants`, `sCount_succ`: start cores.
- `IsUnary`, `InL`, `exists_unary_hole_iff`: unary levels.
- `ofReader`, `isHole_ofReader_iff`: readers as lettered monitors.

All declarations are in the namespace `DeciNSSE.LetteredHierarchy`.
-/
