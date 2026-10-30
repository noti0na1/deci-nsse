import DeciNSSE.Solver.Closure
import DeciNSSE.Certificates

/-! # Packed label readers

Decoding the two masks commutes with every reader transition and preserves
acceptance and admissions.
-/

namespace DeciNSSE.Solver
open Mask Monitor Holes
attribute [-simp] BitVec.getLsbD_eq_getElem
variable {n m k : ℕ}

/-- Upper labels, lower labels, and the readiness latch. -/
structure State (m : ℕ) where
  upper : BitVec m
  lower : BitVec m
  latched : Bool
  deriving DecidableEq, BEq, Hashable, Ord, Inhabited

/-- The explicit encoding relation with the finite-set reader. -/
def State.decode (s : State m) : Monitor.State m :=
  ⟨Mask.decode s.upper, Mask.decode s.lower, s.latched⟩

/-- The transpose closure rows. -/
def inverseRows (d : Rows m) : Rows m := table fun y =>
  ofList ((List.finRange m).filter fun x => (d x).getLsbD y)

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
def ready (bot top : BitVec m) (s : State m) : Bool :=
  meets s.upper bot || meets s.lower top || meets s.upper s.lower

theorem ready_spec (ψ : Constraint n m) (s : State m) :
    ready (ofList (botVars ψ)) (ofList (topVars ψ)) s = true ↔
      Monitor.Ready ψ s.decode.U s.decode.L := by
  simp only [ready, Bool.or_eq_true, meets_iff, bit_ofList, Monitor.Ready,
    State.decode, mem_decode]
  simp only [or_assoc]

/-- Admission is an intersection with lower or sign-flipped upper labels. -/
def admitted (s t : State (2 * k)) : Bool :=
  meets s.lower t.upper || meets
    (image (fun i => singleton (FiniteVariance.flipV i)) s.upper) t.upper

theorem admitted_spec (s t : State (2 * k)) :
    admitted s t = true ↔ Monitor.admission s.decode t.decode := by
  simp only [admitted, Bool.or_eq_true, meets_iff, bit_image, bit_singleton,
    Monitor.admission, State.decode, mem_decode]
  constructor
  · rintro (h | ⟨i, ⟨j, hj, rfl⟩, hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hi⟩
  · rintro (h | ⟨j, hj, hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨j, hj, rfl⟩, hi⟩

/-- A reader with shared transition matrices and constant-time label tests. -/
structure Reader (n m : ℕ) where
  upper : Table n (Rows m)
  lower : Table n (Rows m)
  bot : BitVec m
  top : BitVec m
  child : BitVec m
  start : State m

/-- Compile the finite relations once. -/
def reader (ψ : Constraint n m) (X Y : V m) : Reader n m :=
  let d := derivedRows ψ
  ⟨upperRows ψ d, lowerRows ψ d, ofList (botVars ψ), ofList (topVars ψ),
    ofList ((upperLits ψ).map Prod.fst), ⟨d X, inverseRows d Y, false⟩⟩

def Reader.step (r : Reader n m) (s : State m) (a : Fin n) : State m :=
  ⟨image (r.upper a) s.upper, image (r.lower a) s.lower,
    s.latched || ready r.bot r.top s⟩

def Reader.accept (r : Reader n m) (s : State m) : Bool :=
  s.latched || ready r.bot r.top s || meets s.upper r.child

def Reader.machine (r : Reader n m) : DFA (Fin n) (State m) :=
  ⟨r.step, r.start, {s | r.accept s = true}⟩

private theorem state_ext {a b : Monitor.State m} (hu : a.U = b.U)
    (hl : a.L = b.L) (hb : a.b = b.b) : a = b := by
  cases a; cases b; simp_all

theorem reader_start (ψ : Constraint n m) (X Y : V m) :
    (reader ψ X Y).start.decode = (Monitor.reader ψ X Y).start := by
  apply state_ext <;> simp [reader, State.decode, Monitor.reader_start,
    Finset.ext_iff, mem_derivedPairs]

theorem reader_step (ψ : Constraint n m) (X Y : V m) (s : State m) (a : Fin n) :
    ((reader ψ X Y).step s a).decode = (Monitor.reader ψ X Y).step s.decode a := by
  apply state_ext
  · ext i
    simp only [Reader.step, reader, State.decode, mem_decode, bit_image,
      Monitor.reader_step, Monitor.upperStep, Finset.mem_filter, Finset.mem_univ,
      true_and, upperRows_spec]
  · ext i
    simp only [Reader.step, reader, State.decode, mem_decode, bit_image,
      Monitor.reader_step, Monitor.lowerStep, Finset.mem_filter, Finset.mem_univ,
      true_and, lowerRows_spec]
  · simp only [Reader.step, reader, State.decode, Monitor.reader_step]
    congr 1
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq]; exact ready_spec ψ s)

theorem reader_accept (ψ : Constraint n m) (X Y : V m) (s : State m) :
    (reader ψ X Y).accept s = true ↔ Monitor.Accept ψ s.decode := by
  simp only [Reader.accept, reader, Bool.or_eq_true, ready_spec, meets_iff,
    bit_ofList, List.mem_map, Monitor.Accept, State.decode, mem_decode]
  aesop

theorem reader_eval (ψ : Constraint n m) (X Y : V m) (w : List (Fin n)) :
    ((reader ψ X Y).machine.eval w).decode = (Monitor.reader ψ X Y).eval w := by
  induction w using List.reverseRecOn with
  | nil => exact reader_start ψ X Y
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton, DFA.eval_append_singleton]
    exact (reader_step ψ X Y _ a).trans (congrArg (fun s => (Monitor.reader ψ X Y).step s a) ih)

/-- Decoding preserves the entire hole language. -/
theorem reader_hole (ψ : Constraint n (2 * k)) (X Y : V (2 * k)) (w : List (Fin n)) :
    IsReaderHole (reader ψ X Y).machine (fun s t => admitted s t = true)
      {s | (reader ψ X Y).accept s = false} w ↔
    IsReaderHole (Monitor.reader ψ X Y) Monitor.admission (Monitor.target ψ) w := by
  simp only [isReaderHole_iff, Set.mem_ofPred_eq, Bool.eq_false_iff,
    admitted_spec, reader_eval, Monitor.target]
  apply and_congr _ Iff.rfl
  apply not_congr
  exact (reader_accept ψ X Y _).trans (by rw [reader_eval])

end DeciNSSE.Solver
