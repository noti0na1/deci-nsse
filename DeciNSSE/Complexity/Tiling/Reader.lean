import DeciNSSE.Complexity.Tiling.Spatial
import DeciNSSE.Complexity.Tiling.Authentication
import DeciNSSE.Complexity.Tiling.GridAuth
import DeciNSSE.Complexity.Tiling.Bits
import DeciNSSE.Complexity.Tiling.Packets

/-! # Reading a tiling in two orders

## Main declarations

- `checks_iff` specifies the regular tests on a repeated packet.
- `tokenReader_hole_iff` identifies the target words that encode valid grids.
- `binary_hole_iff` specifies fixed-width coding on all binary words.
- `tilingReader_hole_iff`, `tilingReader_size` specify the binary reduction.
-/

namespace DeciNSSE.Complexity.Tiling
open CoAlignment Holes
open scoped List

variable {D : Type*} {t : ℕ}

/-- A repeated packet reaches the token reader's target exactly when its master and exposed
probe records pass the order, adjacency and boundary checks. -/
theorem checks_iff [Fintype D] [DecidableEq D] (I : Square D) (e : D ≃ Fin t)
    (P : Packet (CellLetter D)) :
    (tokenReader I e).dfa.eval (copies I P) ∈ (tokenReader I e).target ↔ Checks I P :=
  (Controller.final_iff I e _).trans (Controller.repeated_checks_iff I P)

/-- The token reader's holes are exactly the repeated grid packets of valid square tilings. -/
theorem tokenReader_hole_iff [DecidableEq D] (I : Square D) (e : D ≃ Fin t) (w) :
    (tokenReader I e).Hole w ↔ ∃ g, I.Valid g ∧ w = copies I (gridPacket I g) := by
  let : Fintype D := Fintype.ofEquiv (Fin t) e.symm
  have replicated (P : Packet (CellLetter D)) :
      (List.replicate (2*I.p) P ++ [P]).flatMap Packet.render = copies I P := by
    rw [← List.replicate_succ']; simp [copies,List.flatMap_def]
  constructor
  · intro hole
    have target := ((Holes.isReaderHole_iff ..).mp hole).1
    have final := (Controller.final_iff I e _).mp target
    obtain ⟨ps,hl,rfl⟩ := Controller.render_of_final I final
    obtain rfl | ⟨qs,P,rfl⟩ := List.eq_nil_or_concat' ps
    · simp at hl
    have len : qs.length = 2*I.p := by simpa using hl
    obtain ⟨same,suffix⟩ := (hole_packets_iff I e qs P len final).mp hole
    have eq : qs = List.replicate (2*I.p) P := List.eq_replicate_iff.mpr ⟨len,same⟩
    subst qs
    rw [replicated] at target ⊢
    obtain ⟨g,valid,rfl⟩ := (authenticated_iff I P).mp ⟨(checks_iff I e P).mp target,suffix⟩
    exact ⟨g,valid,rfl⟩
  · rintro ⟨g,hg,rfl⟩
    let P := gridPacket I g
    obtain ⟨checks,suffix⟩ := (authenticated_iff I P).mpr ⟨g,hg,rfl⟩
    have final := (Controller.final_iff I e _).mp ((checks_iff I e P).mpr checks)
    change (tokenReader I e).Hole (copies I P)
    rw [← replicated P] at final ⊢
    exact (hole_packets_iff I e _ P (by simp) final).mpr
      ⟨fun _ h => List.eq_of_mem_replicate h,suffix⟩

/-- Number the two bits, record marker and two delimiters first, followed by the tiles in the
supplied numbering. -/
def tokenNumber (e : D ≃ Fin t) : Token (CellLetter D) → ℕ
  | .data (.bit b) => b.toNat
  | .data .record => 2
  | .stop => 3
  | .bang => 4
  | .data (.tile d) => 5 + (e d).val

/-- Encode every token at the same binary width, most significant bit first. -/
def binaryWord (e : D ≃ Fin t) (w : List (Token (CellLetter D))) : List (Fin 2) :=
  let width := Nat.log2 (t + 4) + 1
  w.flatMap fun a => (List.range width).reverse.map fun i =>
    if (tokenNumber e a).testBit i then 1 else 0

private def tokenOfNumber (e : D ≃ Fin t) : ℕ → Option (Token (CellLetter D))
  | 0 => some (.data (.bit false))
  | 1 => some (.data (.bit true))
  | 2 => some (.data .record)
  | 3 => some .stop
  | 4 => some .bang
  | i + 5 => if hi : i < t then some (.data (.tile (e.symm ⟨i, hi⟩))) else none

/-- Number proper bit prefixes in breadth-first order, with the empty prefix
at zero. The next layer holds all complete codewords in numerical order. -/
def binaryTable (e : D ≃ Fin t) (M : StoppingTable (Token (CellLetter D))) :
    StoppingTable (Fin 2) :=
  let phases := 2 ^ (Nat.log2 (t + 4) + 1) - 1
  M.decode phases fun phase b =>
    let next := 2 * phase + 1 + b.val
    if next < phases then some (.inl next)
    else (tokenOfNumber e (next - phases)).map Sum.inr

/-- The fixed-width token decoder uses at most `2 * (t + 4) * M.size + 1` binary states for `t`
tiles. -/
theorem binaryTable_size (e : D ≃ Fin t) (M : StoppingTable (Token (CellLetter D))) :
    (binaryTable e M).size ≤ 2 * (t + 4) * M.size + 1 := by
  have h := Nat.log2_self_le (by omega : t + 4 ≠ 0)
  unfold binaryTable
  rw [StoppingTable.decode_size _ _ (by rw [pow_succ]; have := Nat.two_pow_pos (t + 4).log2; omega)]
  rw [pow_succ, Nat.mul_comm (2 * (t + 4))]
  gcongr
  omega

/-- A binary word is a hole of the compiled table exactly when it encodes a hole of the token
table. -/
theorem binary_hole_iff (e : D ≃ Fin t) (M : StoppingTable (Token (CellLetter D))) (w) :
    (binaryTable e M).Hole w ↔ ∃ u, M.Hole u ∧ w = binaryWord e u := by
  let k := Nat.log2 (t+4) + 1
  have bound (a : Token (CellLetter D)) : tokenNumber e a < 2 ^ k := by
    have h : t+4 < 2^k := (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
    rcases a with ((_ | _) | _ | d) | _ | _ <;> simp [tokenNumber] <;> omega
  have inv (i : ℕ) (a : Token (CellLetter D)) :
      tokenOfNumber e i = some a ↔ tokenNumber e a = i := by
    constructor
    · intro h
      rcases i with _ | _ | _ | _ | _ | j
      all_goals simp only [tokenOfNumber] at h
      all_goals try (cases h; rfl)
      split at h
      · cases h; simp [tokenNumber]; omega
      · cases h
    · rintro rfl
      rcases a with ((_ | _) | _ | d) | _ | _
      all_goals try rfl
      simp [tokenNumber, Nat.add_comm 5, tokenOfNumber]
  let C := Bits.binaryCode k (by dsimp [k]; omega) (tokenNumber e) (tokenOfNumber e) bound inv
  exact C.hole_iff M w

/-- Compile the square's token reader to a binary stopping table using the supplied tile
numbering. -/
def tilingReader [DecidableEq D] (I : Square D) (e : D ≃ Fin t) :=
  binaryTable e (tokenReader I e)

/-- This polynomial bounds the binary state count in the unary exponent `p`, the number `t` of
tiles and the boundary-prefix length `r`. -/
def stateBound (p t r : ℕ) := 65536 * (p + 1) ^ 2 * (t + 6) ^ 3 * (r + 1)

/-- The binary reader's holes are precisely the fixed-width encodings of repeated packets for
valid grids. -/
theorem tilingReader_hole_iff [DecidableEq D] (I : Square D) (e : D ≃ Fin t) (w) :
    (tilingReader I e).Hole w ↔
      ∃ g, I.Valid g ∧ w = binaryWord e (copies I (gridPacket I g)) := by
  rw [tilingReader, binary_hole_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (tokenReader_hole_iff I e u).mp hu
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, (tokenReader_hole_iff I e _).mpr ⟨g, hg, rfl⟩, rfl⟩

/-- The binary tiling reader has at most `stateBound I.p t I.initial.length` states. -/
theorem tilingReader_size [DecidableEq D] (I : Square D) (e : D ≃ Fin t) :
    (tilingReader I e).size ≤ stateBound I.p t I.initial.length := by
  apply (binaryTable_size e (tokenReader I e)).trans
  calc
    _ ≤ 2 * (t + 4) * (4096 * (I.p + 1) ^ 2 * (t + 6) ^ 2 * (I.initial.length + 1)) + 1 := by
      gcongr; exact tokenReader_size I e
    _ ≤ _ := by unfold stateBound; ring_nf; omega

end DeciNSSE.Complexity.Tiling
