import DeciNSSE.Complexity.Tiling.Reduction

/-! # Checks on the tiling reduction

A one-cell grid tests the boundary and the authentication of the exposed probe at token
and binary level. An empty tile alphabet also exercises the doubled table and the emitter.

## Main declarations

- `singletonChecks` tests a valid encoding, a forged probe and malformed words.
- `constructionSizes` counts the states, variables and literals in a binary example.
-/

namespace DeciNSSE.Complexity.Tiling.Examples

private def square (left : Finset (Fin 2)) : Square (Fin 2) where
  horizontal := ∅
  vertical := ∅
  p := 0
  initial := []
  rest := Finset.univ
  left := left
  right := Finset.univ
  bottom := Finset.univ

private def hole {α : Type} [DecidableEq α] (M : StoppingTable α) (w : List α) : Bool :=
  letI : Decidable (M.Hole w) := Packets.decHole M.dfa _ _ w
  decide (M.Hole w)

private def singletonChecks :=
  let I := square {0}
  let g : I.Grid := fun _ _ => 0
  let p := gridPacket I g
  let forged := { p with probes := [[.record, .tile 1]] }
  let e := Equiv.refl (Fin 2)
  let M := tokenReader I e
  let B := binaryTable e M
  let w := copies I p
  let bits := binaryWord e w
  (hole M w, hole M (copies I forged), hole (tokenReader (square ∅) e) w,
    hole B bits, hole B bits.dropLast, hole B (bits ++ [0]))

#guard singletonChecks == (true, false, false, true, false, false)


private def constructionSizes :=
  let I : Square (Fin 0) := ⟨⟨∅, ∅⟩, 0, [], ∅, ∅, ∅, ∅⟩
  let e := Equiv.refl (Fin 0)
  let T := tokenReader I e
  let B := tilingReader I e
  let A := doubleTable (n := 2) (by decide) B
  let Z := tilingSystem (n := 2) (by decide) (fun i => i == 0) I e
  (T.size, B.size, A.size, (emit A).vars, Z.vars, Z.system.length)

#guard constructionSizes == (3, 22, 67, 202, 404, 806)

end DeciNSSE.Complexity.Tiling.Examples
