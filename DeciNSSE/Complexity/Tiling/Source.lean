import DeciNSSE.Constraints.Basic

/-! # Torus tilings and open squares with a boundary

Rows increase in the direction of the vertical relation. On the torus both
coordinates wrap. In the square the four boundary tests include the corners.

## Main declarations

- `TorusTiling` is the torus problem with an initial word of tiles.
- `Square.Valid` specifies an open exponential square with a succinct boundary.
- `bridge_iff` transports solutions between the torus and its square of triples.

The fixed-domino-system hardness of tiling the torus of side
`2 ^ (w.length + 1)` with initial word `w` is Tobies, *Complexity Results and
Practical Algorithms for Logics in Knowledge Representation*, Corollary 5.14.
The torus and initial condition are those of Börger, Grädel and Gurevich,
*The Classical Decision Problem*, Definition 6.1.1.
-/

namespace DeciNSSE.Complexity.Tiling

/-- A domino system on tiles of type `D` specifies the allowed ordered pairs of horizontal and
vertical neighbors. -/
structure Domino (D : Type*) where
  /-- Allowed ordered pairs from a tile to its right neighbor. -/
  horizontal : Finset (D × D)
  /-- Allowed ordered pairs from a tile to the tile in the next row. -/
  vertical : Finset (D × D)

/-- A rectangular grid assigns a tile to each column and row. -/
abbrev Grid (D : Type*) (s t : ℕ) := Fin s → Fin t → D

variable {D : Type*}

/-- The modular successor on a nonempty coordinate, including at side one. -/
def next {s : ℕ} (x : Fin s) : Fin s :=
  ⟨(x.val + 1) % s, Nat.mod_lt _ (by have := x.isLt; omega)⟩

/-- A torus tiling respects both directed wraparound edges and the prescribed initial word on
row zero. Both dimensions are positive and the initial word fits the row. -/
def TorusTiling (A : Domino D) (s t : ℕ) (w : List D) (g : Grid D s t) : Prop :=
  0 < s ∧ ∃ ht : 0 < t, w.length ≤ s ∧
    (∀ x y, (g x y, g (next x) y) ∈ A.horizontal ∧ (g x y, g x (next y)) ∈ A.vertical) ∧
    ∀ (i : Fin w.length) (hi : i.val < s), g ⟨i, hi⟩ ⟨0, ht⟩ = w[i]

/-- An open square of side `2 ^ p` has directed adjacency relations and succinct boundary
conditions, with `p` supplied in unary. Row zero uses the listed tile sets and then the default
set. -/
structure Square (D : Type*) extends Domino D where
  /-- The unary exponent giving side length `2 ^ p`. -/
  p : ℕ
  /-- Allowed tiles for the listed initial cells of row zero. -/
  initial : List (Finset D)
  /-- The default set for the remaining cells of row zero. -/
  rest : Finset D
  /-- Allowed tiles in column zero. -/
  left : Finset D
  /-- Allowed tiles in the last column. -/
  right : Finset D
  /-- Allowed tiles in the last row. -/
  bottom : Finset D

/-- The side length of the square with unary exponent `p` is `2 ^ p`. -/
abbrev Square.side (I : Square D) := 2 ^ I.p

/-- A grid on the square has one tile at each pair of coordinates below its side length. -/
abbrev Square.Grid (I : Square D) := Tiling.Grid D I.side I.side

/-- Every interior edge respects its directed tile relation and every boundary cell satisfies
all conditions that apply to it, including at corners. -/
def Square.Valid (I : Square D) (g : I.Grid) : Prop :=
  ∀ x y, (∀ hx : x.val + 1 < I.side, (g x y, g ⟨x.val + 1, hx⟩ y) ∈ I.horizontal) ∧
    (∀ hy : y.val + 1 < I.side, (g x y, g x ⟨y.val + 1, hy⟩) ∈ I.vertical) ∧
    (y.val = 0 → g x y ∈ I.initial[x.val]?.getD I.rest) ∧
    (x.val = 0 → g x y ∈ I.left) ∧ (x.val + 1 = I.side → g x y ∈ I.right) ∧
    (y.val + 1 = I.side → g x y ∈ I.bottom)

/-- Replace each torus tile by a triple remembering the first tile of its row and of its column,
so the square boundary can check both wraparound edges. -/
def bridge [Fintype D] [DecidableEq D] (A : Domino D) (p : ℕ) (w : List D) :
    Square (D × D × D) where
  p := p
  horizontal := Finset.univ.filter fun z =>
    (z.1.1, z.2.1) ∈ A.horizontal ∧ z.1.2.1 = z.2.2.1
  vertical := Finset.univ.filter fun z =>
    (z.1.1, z.2.1) ∈ A.vertical ∧ z.1.2.2 = z.2.2.2
  initial := w.map fun a => Finset.univ.filter fun z => z.1 = a ∧ z.2.2 = a
  rest := Finset.univ.filter fun z => z.1 = z.2.2
  left := Finset.univ.filter fun z => z.1 = z.2.1
  right := Finset.univ.filter fun z => (z.1, z.2.1) ∈ A.horizontal
  bottom := Finset.univ.filter fun z => (z.1, z.2.2) ∈ A.vertical

private theorem initial_mem [Fintype D] [DecidableEq D] (A : Domino D) (p : ℕ) (w : List D)
    (i : ℕ) (z : D × D × D) :
    z ∈ (bridge A p w).initial[i]?.getD (bridge A p w).rest ↔
      z.1 = z.2.2 ∧ ∀ hi : i < w.length, z.1 = w[i] := by
  by_cases hi : i < w.length
  · simp [bridge, List.getElem?_map, List.getElem?_eq_getElem hi]; grind
  · simp [bridge, hi]

private theorem constant_from_zero {s : ℕ} (h : 0 < s) (f : Fin s → D)
    (step : ∀ x : Fin s, ∀ hx : x.val + 1 < s, f x = f ⟨x.val + 1, hx⟩) (x : Fin s) :
    f x = f ⟨0, h⟩ := by
  obtain ⟨i, hi⟩ := x
  induction i with
  | zero => rfl
  | succ i ih => exact (step ⟨i, by omega⟩ hi).symm.trans (ih (by omega))

private theorem next_interior {s : ℕ} (x : Fin s) (hx : x.val + 1 < s) :
    next x = ⟨x.val + 1, hx⟩ := Fin.ext (Nat.mod_eq_of_lt hx)

private theorem next_last {s : ℕ} (hs : 0 < s) (x : Fin s) (hx : x.val + 1 = s) :
    next x = ⟨0, hs⟩ := Fin.ext (by simp [next, hx])

/-- For an initial word that fits on row zero, the square torus has a tiling exactly when the
open square on triple tiles has a valid grid. -/
theorem bridge_iff [Fintype D] [DecidableEq D] (A : Domino D) (p : ℕ) (w : List D)
    (hw : w.length ≤ 2 ^ p) :
    (∃ g, TorusTiling A (2 ^ p) (2 ^ p) w g) ↔ ∃ g, (bridge A p w).Valid g := by
  let s := 2 ^ p
  have hs : 0 < s := Nat.pow_pos (by decide)
  let zero : Fin s := ⟨0, hs⟩
  constructor
  · rintro ⟨g, _, _, _, adj, ini⟩
    refine ⟨fun x y => (g x y, g zero y, g x zero), ?_⟩
    intro x y
    refine ⟨fun hx => ?_, fun hy => ?_, fun hy => ?_, fun hx => ?_, fun hx => ?_, fun hy => ?_⟩
    · have ha := (adj x y).1
      rw [next_interior (s := 2 ^ p) x hx] at ha
      simpa [bridge] using ha
    · have ha := (adj x y).2
      rw [next_interior (s := 2 ^ p) y hy] at ha
      simpa [bridge] using ha
    · have ey : y = zero := Fin.ext hy
      subst y
      exact (initial_mem A p w x _).mpr ⟨rfl, fun hi => ini ⟨x, hi⟩ x.isLt⟩
    · have ex : x = zero := Fin.ext hx
      simp [bridge, ex]
    · simpa [bridge, next_last hs x hx, zero] using (adj x y).1
    · simpa [bridge, next_last hs y hy, zero] using (adj x y).2
  · rintro ⟨g, valid⟩
    have row (x y : Fin s) : (g x y).2.1 = (g zero y).1 := by
      have h := constant_from_zero hs (fun i => (g i y).2.1) (fun i hi =>
        (Finset.mem_filter.mp ((valid i y).1 hi)).2.2) x
      have h0 := (Finset.mem_filter.mp ((valid zero y).2.2.2.1 rfl)).2
      exact h.trans h0.symm
    have col (x y : Fin s) : (g x y).2.2 = (g x zero).1 := by
      have h := constant_from_zero hs (fun i => (g x i).2.2) (fun i hi =>
        (Finset.mem_filter.mp ((valid x i).2.1 hi)).2.2) y
      have h0 := ((initial_mem A p w x _).mp ((valid x zero).2.2.1 rfl)).1
      exact h.trans h0.symm
    refine ⟨fun x y => (g x y).1, hs, hs, hw, ?_, ?_⟩
    · intro x y
      constructor
      · by_cases hx : x.val + 1 < s
        · rw [next_interior x hx]
          exact (Finset.mem_filter.mp ((valid x y).1 hx)).2.1
        · have he : x.val + 1 = s := by omega
          rw [next_last hs x he]
          change ((g x y).1, (g zero y).1) ∈ A.horizontal
          rw [← row x y]
          exact (Finset.mem_filter.mp ((valid x y).2.2.2.2.1 he)).2
      · by_cases hy : y.val + 1 < s
        · rw [next_interior y hy]
          exact (Finset.mem_filter.mp ((valid x y).2.1 hy)).2.1
        · have he : y.val + 1 = s := by omega
          rw [next_last hs y he]
          change ((g x y).1, (g x zero).1) ∈ A.vertical
          rw [← col x y]
          exact (Finset.mem_filter.mp ((valid x y).2.2.2.2.2 he)).2
    · intro i hi
      exact ((initial_mem A p w i _).mp ((valid ⟨i, hi⟩ zero).2.2.1 rfl)).2 i.isLt

end DeciNSSE.Complexity.Tiling
