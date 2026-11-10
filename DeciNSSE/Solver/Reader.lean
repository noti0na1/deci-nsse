import DeciNSSE.Solver.Closure
import DeciNSSE.Certificates

/-! # Packed label readers

The packed reader is the executable counterpart of the label reader `Monitor.reader`:
its states store the two label sets as bit masks, and its transitions use shared
transition matrices. Decoding the two masks commutes with every reader transition and
preserves acceptance and admissions, so the packed reader has the same hole language.

## Main declarations

- `Solver.PackedState`, `Solver.PackedState.decode`: packed label states and their
  decoding into `Monitor.State`.
- `Solver.PackedReader`, `Solver.packedReader`: the packed reader of a covariant system
  and query, `Solver.packedSideReader` for one side of a query, and
  `Solver.packedSideReaders` for both sides over one closure.
- `Solver.admitted`: the packed admission test.
- `Solver.packedReader_eval`: decoding commutes with evaluation.
- `Solver.packedReader_hole`, `Solver.packedSideReader_hole`: the packed and the
  finite-set readers have the same holes.
-/

namespace DeciNSSE.Solver
open Mask Monitor Holes
attribute [-simp] BitVec.getLsbD_eq_getElem
variable {n m k : ℕ}

/-- A packed label state: upper labels, lower labels, and the readiness latch. -/
structure PackedState (m : ℕ) where
  /-- The upper labels, as a bit mask. -/
  upper : BitVec m
  /-- The lower labels, as a bit mask. -/
  lower : BitVec m
  /-- Whether readiness occurred at a strictly earlier cut. -/
  latched : Bool
  deriving DecidableEq, BEq, Hashable, Ord, Inhabited

/-- Decode a packed state into a state of the finite-set reader `Monitor.reader`. -/
def PackedState.decode (s : PackedState m) : Monitor.State m :=
  ⟨Mask.decode s.upper, Mask.decode s.lower, s.latched⟩

/-- The transpose closure rows. -/
def inverseRows (d : Rows m) : Rows m := table fun y =>
  ofList ((List.finRange m).filter fun x => (d x).getLsbD y)

/-- A transposed row holds exactly the sources of a column. -/
@[simp] theorem bit_inverseRows (d : Rows m) (x y : Fin m) :
    (inverseRows d y).getLsbD x = true ↔ (d x).getLsbD y = true := by
  simp [inverseRows]

/-- One-letter upper paths, with the closure shared between rows. -/
def upperRows (ψ : Constraint n m) (d : Rows m) : Table n (Rows m) :=
  table fun i => table fun x => union (upperLits ψ) fun p =>
    if (d x).getLsbD p.1 then d (p.2 i) else BitVec.zero _

/-- One-letter lower paths, with the transposed closure shared between rows. -/
def lowerRows (ψ : Constraint n m) (closure : Rows m) : Table n (Rows m) :=
  let d := inverseRows closure
  table fun i => table fun y => union (lowerLits ψ) fun p =>
    if (d y).getLsbD p.2 then d (p.1 i) else BitVec.zero _

/-- The upper rows of a letter are the one-letter upper path judgments. -/
theorem upperRows_spec (ψ : Constraint n m) (i : Fin n) (x y : V m) :
    (upperRows ψ (derivedRows ψ) i x).getLsbD y = true ↔
      PathDecision.upper ψ (derivedPairs ψ) [i] x y = true := by
  simp only [upperRows, table_eq, bit_union, PathDecision.upper, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, mem_derivedPairs]
  apply exists_congr; intro p
  apply and_congr_right; intro _
  split <;> rename_i h
  · simp only [bit_derivedRows, (bit_derivedRows ψ x p.1).mp h, true_and]
  · have hn : ¬ Derives ψ x p.1 := by simpa only [bit_derivedRows] using h
    simp [hn]

/-- The lower rows of a letter are the one-letter lower path judgments. -/
theorem lowerRows_spec (ψ : Constraint n m) (i : Fin n) (x y : V m) :
    (lowerRows ψ (derivedRows ψ) i y).getLsbD x = true ↔
      PathDecision.lower ψ (derivedPairs ψ) [i] x y = true := by
  simp only [lowerRows, table_eq, bit_union, PathDecision.lower, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, mem_derivedPairs]
  apply exists_congr; intro p
  apply and_congr_right; intro _
  split <;> rename_i h
  · simp only [bit_inverseRows, bit_derivedRows] at h ⊢
    simp [h]
  · have hn : ¬ Derives ψ p.2 y := by simpa only [bit_inverseRows, bit_derivedRows] using h
    simp [hn]

/-- The three readiness intersections. -/
def ready (bot top : BitVec m) (s : PackedState m) : Bool :=
  meets s.upper bot || meets s.lower top || meets s.upper s.lower

/-- The packed readiness test is readiness of the decoded label sets. -/
theorem ready_spec (ψ : Constraint n m) (s : PackedState m) :
    ready (ofList (botVars ψ)) (ofList (topVars ψ)) s = true ↔
      Monitor.Ready ψ s.decode.U s.decode.L := by
  simp only [ready, Bool.or_eq_true, meets_iff, bit_ofList, Monitor.Ready,
    PackedState.decode, mem_decode]
  simp only [or_assoc]

/-- Admission is an intersection with lower or sign-flipped upper labels. -/
def admitted (s t : PackedState (2 * k)) : Bool :=
  meets s.lower t.upper || meets
    (image (fun i => singleton (SignDuality.flipV i)) s.upper) t.upper

/-- The packed admission test is the admission of the decoded states. -/
theorem admitted_spec (s t : PackedState (2 * k)) :
    admitted s t = true ↔ Monitor.admission s.decode t.decode := by
  simp only [admitted, Bool.or_eq_true, meets_iff, bit_image, bit_singleton,
    Monitor.admission, PackedState.decode, mem_decode]
  constructor
  · rintro (h | ⟨i, ⟨j, hj, rfl⟩, hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hi⟩
  · rintro (h | ⟨j, hj, hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨j, hj, rfl⟩, hi⟩

/-- A packed reader with shared transition matrices and constant-time label tests. -/
structure PackedReader (n m : ℕ) where
  /-- For each letter, the one-letter upper extension of each variable. -/
  upper : Table n (Rows m)
  /-- For each letter, the one-letter lower extension of each variable. -/
  lower : Table n (Rows m)
  /-- The variables with a bottom literal. -/
  bot : BitVec m
  /-- The variables with a top literal. -/
  top : BitVec m
  /-- The variables with an upper constructor literal. -/
  child : BitVec m
  /-- The start state. -/
  start : PackedState m

/-- The packed reader of `ψ ⊨? X ≤ Y` over the closure rows `d`. -/
def packedReaderOf (ψ : Constraint n m) (d : Rows m) (X Y : V m) : PackedReader n m :=
  ⟨upperRows ψ d, lowerRows ψ d, ofList (botVars ψ), ofList (topVars ψ),
    ofList ((upperLits ψ).map Prod.fst), ⟨d X, inverseRows d Y, false⟩⟩

/-- The packed reader of `ψ ⊨? X ≤ Y`, the packed counterpart of `Monitor.reader ψ X Y`.
The closure and the transition matrices are computed once. -/
def packedReader (ψ : Constraint n m) (X Y : V m) : PackedReader n m :=
  packedReaderOf ψ (derivedRows ψ) X Y

/-- One reader transition: extend both label sets and update the latch. -/
def PackedReader.step (r : PackedReader n m) (s : PackedState m) (a : Fin n) : PackedState m :=
  ⟨image (r.upper a) s.upper, image (r.lower a) s.lower,
    s.latched || ready r.bot r.top s⟩

/-- Acceptance: the latch, current readiness, or a child. -/
def PackedReader.accept (r : PackedReader n m) (s : PackedState m) : Bool :=
  s.latched || ready r.bot r.top s || meets s.upper r.child

/-- The packed reader as a DFA. Its target is the set of rejected states. -/
def PackedReader.machine (r : PackedReader n m) : DFA (Fin n) (PackedState m) :=
  ⟨r.step, r.start, {s | r.accept s = true}⟩

private theorem state_ext {a b : Monitor.State m} (hu : a.U = b.U)
    (hl : a.L = b.L) (hb : a.b = b.b) : a = b := by
  cases a; cases b; simp_all

/-- Decoding the packed start state gives the start state of the finite-set reader. -/
theorem packedReader_start (ψ : Constraint n m) (X Y : V m) :
    (packedReader ψ X Y).start.decode = (Monitor.reader ψ X Y).start := by
  apply state_ext <;> simp [packedReader, packedReaderOf, PackedState.decode, Monitor.reader_start,
    Finset.ext_iff, mem_derivedPairs]

/-- Decoding commutes with one transition. -/
theorem packedReader_step (ψ : Constraint n m) (X Y : V m) (s : PackedState m) (a : Fin n) :
    ((packedReader ψ X Y).step s a).decode = (Monitor.reader ψ X Y).step s.decode a := by
  apply state_ext
  · ext i
    simp only [PackedReader.step, packedReader, packedReaderOf, PackedState.decode, mem_decode,
      bit_image, Monitor.reader_step, upperStep, Finset.mem_filter, Finset.mem_univ,
      true_and, upperRows_spec]
  · ext i
    simp only [PackedReader.step, packedReader, packedReaderOf, PackedState.decode, mem_decode,
      bit_image, Monitor.reader_step, lowerStep, Finset.mem_filter, Finset.mem_univ,
      true_and, lowerRows_spec]
  · simp only [PackedReader.step, packedReader, packedReaderOf, PackedState.decode,
      Monitor.reader_step]
    congr 1
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq]; exact ready_spec ψ s)

/-- Packed acceptance is acceptance of the decoded state. -/
theorem packedReader_accept (ψ : Constraint n m) (X Y : V m) (s : PackedState m) :
    (packedReader ψ X Y).accept s = true ↔ Monitor.Accept ψ s.decode := by
  simp only [PackedReader.accept, packedReader, packedReaderOf, Bool.or_eq_true, ready_spec,
    meets_iff, bit_ofList, List.mem_map, Monitor.Accept, PackedState.decode, mem_decode]
  aesop

/-- Decoding commutes with evaluation on every word. -/
theorem packedReader_eval (ψ : Constraint n m) (X Y : V m) (w : List (Fin n)) :
    ((packedReader ψ X Y).machine.eval w).decode = (Monitor.reader ψ X Y).eval w := by
  induction w using List.reverseRecOn with
  | nil => exact packedReader_start ψ X Y
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton, DFA.eval_append_singleton]
    exact (packedReader_step ψ X Y _ a).trans
      (congrArg (fun s => (Monitor.reader ψ X Y).step s a) ih)

/-- Decoding preserves the entire hole language. -/
theorem packedReader_hole (ψ : Constraint n (2 * k)) (X Y : V (2 * k)) (w : List (Fin n)) :
    IsReaderHole (packedReader ψ X Y).machine (fun s t => admitted s t = true)
      {s | (packedReader ψ X Y).accept s = false} w ↔
    IsReaderHole (Monitor.reader ψ X Y) Monitor.admission (Monitor.target ψ) w := by
  simp only [isReaderHole_iff, Set.mem_ofPred_eq, Bool.eq_false_iff,
    admitted_spec, packedReader_eval, Monitor.target]
  apply and_congr _ Iff.rfl
  apply not_congr
  exact (packedReader_accept ψ X Y _).trans (by rw [packedReader_eval])

/-- The packed reader of the side `θ` of the query `ϕ ⊨? x ≤ y`, the packed counterpart
of `Monitor.sideReader`. -/
abbrev packedSideReader (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) :
    PackedReader n (2 * k) :=
  packedReader (signed c ϕ) (Events.sideQuery x y θ).1 (Events.sideQuery x y θ).2

/-- The packed side reader has the holes of the label reader of that side. -/
theorem packedSideReader_hole (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) :
    IsReaderHole (packedSideReader c ϕ x y θ).machine (fun s t => admitted s t = true)
      {s | (packedSideReader c ϕ x y θ).accept s = false} w ↔
    IsReaderHole (sideReader c ϕ x y θ) admission (sideTarget c ϕ) w :=
  packedReader_hole _ _ _ w

/-- The packed readers of the top-prefix and the bottom-prefix side. They differ in
the start state only, so the closure and the transition matrices are computed once. -/
def packedSideReaders (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    PackedReader n (2 * k) × PackedReader n (2 * k) :=
  let d := derivedRows (signed c ϕ)
  let l := packedReaderOf (signed c ϕ) d (sv x false) (sv y false)
  (l, { l with start := ⟨d (sv y true), inverseRows d (sv x true), false⟩ })

/-- The shared pair consists of the two packed side readers. -/
theorem packedSideReaders_eq (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    packedSideReaders c ϕ x y =
      (packedSideReader c ϕ x y .l, packedSideReader c ϕ x y .r) := rfl

end DeciNSSE.Solver
