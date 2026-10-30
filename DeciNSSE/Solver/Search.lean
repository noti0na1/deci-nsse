import DeciNSSE.Solver.Reader

/-! # Certificate search

A scout, an iterative-deepening refuter, and a refining covering-product
search take turns on both sides. Fuel bounds the number of search turns.
-/

namespace DeciNSSE.Solver.Search
open Certificates
variable {n k : ℕ}

abbrev Word (n : ℕ) := List (Fin n)
abbrev Q (k : ℕ) := State (2 * k)

/-- A candidate has no proof until it passes a checker. -/
inductive Candidate (n : ℕ) where
  | refutation (certificate : Refutation n)
  | entailment (certificate : Entailment n)

private instance {α β : Type} [Ord α] [Ord β] : Ord (α × β) where
  compare a b := match compare a.1 b.1 with
    | .eq => compare a.2 b.2
    | o => o

private def canonical {α : Type} [BEq α] [DecidableEq α] [Ord α] (xs : List α) : List α :=
  (xs.mergeSort (fun x y => compare x y != .gt)).dedup

/-- All prefix reader states, including the initial state. -/
def trace (r : Reader n (2 * k)) (w : Word n) : Array (Q k) :=
  w.foldl (fun qs a => qs.push (r.step (qs.back!) a)) #[r.start]

/-- All admitted suffix comparisons of a word. -/
def comparisons (r : Reader n (2 * k)) (w : Word n) : List (ℕ × ℕ) := Id.run do
  let qs := trace r w
  let mut out := []
  for e in [:w.length + 1] do
    for s in [:e] do
      if admitted qs[s]! qs[e]! && (w.drop e).isPrefixOf (w.drop s) then
        out := (s, e) :: out
  return out

private def hole (r : Reader n (2 * k)) (w : Word n) : Bool :=
  !(r.accept (trace r w).back!) && (comparisons r w).isEmpty

/-- A ray stores its source state and the access word used in the certificate. -/
structure SearchRay (n k : ℕ) where
  source : Q k
  certificate : Ray (Fin n)

instance : Inhabited (SearchRay n k) := ⟨⟨default, ⟨[], []⟩⟩⟩

/-- Memory of the reader, terminal comparisons, and ray positions. -/
structure Product (n k : ℕ) where
  reader : Q k
  roots : List (Q k × Word n)
  residuals : List (Word n)
  active : List (ℕ × ℕ × Bool)
  deriving BEq, Hashable, Inhabited

private def starts (rs : Array (SearchRay n k)) (q : Q k) : List (ℕ × ℕ × Bool) :=
  (List.range rs.size).filterMap fun j =>
    if rs[j]!.source == q then some (j, 0, false) else none

private def initial (r : Reader n (2 * k)) (rs : Array (SearchRay n k)) : Product n k :=
  ⟨r.start, [], [], starts rs r.start⟩

private def covered (r : Reader n (2 * k)) (s : Product n k) : Bool :=
  r.accept s.reader || !s.residuals.isEmpty || s.active.any (·.2.2)

private def step (r : Reader n (2 * k)) (b : ℕ) (rs : Array (SearchRay n k))
    (s : Product n k) (a : Fin n) : Product n k := Id.run do
  let q := r.step s.reader a
  let roots := canonical ((s.reader, [a].take b) ::
    s.roots.map (fun p => (p.1, (p.2 ++ [a]).take b)))
  let tails := s.residuals.filterMap fun t => match t with
    | [] => none
    | c :: t => if c == a then some t else none
  let fresh := roots.filterMap fun p =>
    if admitted p.1 q then some ((List.replicate b p.2).flatten.take b) else none
  let active := s.active.filterMap fun (j, off, mature) =>
    let v := rs[j]!.certificate.period
    if v[off]? == some a then
      let done := off + 1 == v.length
      some (j, if done then 0 else off + 1, mature || done)
    else none
  return ⟨q, roots, canonical (tails ++ fresh), canonical (active ++ starts rs q)⟩

/-- Breadth-first product traversal with access words. -/
structure Prover (n k : ℕ) where
  rays : Array (SearchRay n k)
  queue : Array (Product n k × Word n)
  seen : Std.HashSet (Product n k)
  cursor : ℕ := 0

private def newProver (r : Reader n (2 * k)) (rs : Array (SearchRay n k)) : Prover n k :=
  let s := initial r rs
  ⟨rs, #[(s, [])], .emptyWithCapacity |>.insert s, 0⟩

private def proverTurn (r : Reader n (2 * k)) (window : ℕ) (p : Prover n k) :
    Prover n k × Option (Sum (Word n) (Cover (Fin n))) := Id.run do
  if p.cursor ≥ p.queue.size then
    return (p, some (.inr ⟨window, p.rays.toList.map (·.certificate),
      p.queue.toList.map (·.2)⟩))
  let (s, w) := p.queue[p.cursor]!
  if !covered r s then
    let cs := comparisons r w
    if cs.isEmpty then return (p, some (.inl w))
    let qs := trace r w
    let mut rays := p.rays
    for (a, b) in cs do
      let source := qs[a]!
      let period := (w.drop a).take (b - a)
      if !rays.any (fun r => r.source == source && r.certificate.period == period) then
        rays := rays.push ⟨source, ⟨w.take a, period⟩⟩
    return (newProver r rays, none)
  let mut p := {p with cursor := p.cursor + 1}
  for a in List.finRange n do
    let t := step r window p.rays s a
    if !p.seen.contains t then
      p := {p with queue := p.queue.push (t, w ++ [a]), seen := p.seen.insert t}
  return (p, none)

/-- A depth-first node stores the active-period mask. -/
structure Node (n k : ℕ) where
  word : Array (Fin n)
  run : Array (Q k)
  periods : Nat

structure Refuter (n k : ℕ) where
  depth : ℕ := 0
  stack : List (Node n k)

private def root (r : Reader n (2 * k)) : Node n k := ⟨#[], #[r.start], 0⟩

private def refuterTurn (r : Reader n (2 * k)) (d : Refuter n k) :
    Refuter n k × Option (Word n) := Id.run do
  match d.stack with
  | [] => return (⟨d.depth + 1, [root r]⟩, none)
  | s :: rest =>
    let mut d := {d with stack := rest}
    if !r.accept s.run.back! && s.periods == 0 then return (d, some s.word.toList)
    if s.word.size < d.depth && !s.run.back!.latched then
      for a in (List.finRange n).reverse do
        let q := r.step s.run.back! a
        let mut periods := 0
        for gap in [1:s.word.size + 1] do
          if s.periods.testBit gap && s.word[s.word.size - gap]? == some a then
            periods := periods ||| (1 <<< gap)
        for j in [:s.run.size] do
          if admitted s.run[j]! q then
            periods := periods ||| (1 <<< (s.word.size + 1 - j))
        d := {d with stack := ⟨s.word.push a, s.run.push q, periods⟩ :: d.stack}
    return (d, none)

structure Scout (n k : ℕ) where
  queue : Array (Q k × Word n)
  seen : Std.HashSet (Q k)
  cursor : ℕ := 0

private def scoutTurn (r : Reader n (2 * k)) (s : Scout n k) :
    Scout n k × Option (Word n) := Id.run do
  if s.cursor ≥ s.queue.size then return (s, none)
  let (q, w) := s.queue[s.cursor]!
  if !r.accept q && hole r w then return (s, some w)
  let mut s := {s with cursor := s.cursor + 1}
  for a in List.finRange n do
    let t := r.step q a
    if !s.seen.contains t then
      s := {s with queue := s.queue.push (t, w ++ [a]), seen := s.seen.insert t}
  return (s, none)

structure SideSearch (n k : ℕ) where
  reader : Reader n (2 * k)
  prover : Prover n k
  refuter : Refuter n k
  scout : Scout n k
  cover : Option (Cover (Fin n)) := none

private def newSide (r : Reader n (2 * k)) : SideSearch n k :=
  ⟨r, newProver r #[], ⟨0, [root r]⟩,
    ⟨#[(r.start, [])], .emptyWithCapacity |>.insert r.start, 0⟩, none⟩

private def sideTurn (s : SideSearch n k) (window turn : ℕ) :
    SideSearch n k × Option (Word n) := Id.run do
  if s.cover.isSome then return (s, none)
  match turn % 3 with
  | 0 =>
    let (scout, w) := scoutTurn s.reader s.scout
    return ({s with scout}, w)
  | 1 =>
    let (prover, result) := proverTurn s.reader window s.prover
    match result with
    | none => return ({s with prover}, none)
    | some (.inl w) => return ({s with prover}, some w)
    | some (.inr cover) => return ({s with prover, cover := some cover}, none)
  | _ =>
    let (refuter, w) := refuterTurn s.reader s.refuter
    return ({s with refuter}, w)

private def interleave (window : ℕ) : ℕ → ℕ → SideSearch n k → SideSearch n k →
    Option (Candidate n)
  | 0, _, _, _ => none
  | fuel + 1, turn, l, r =>
    let (l, lw) := sideTurn l window turn
    let (r, rw) := sideTurn r window turn
    match lw, rw, l.cover, r.cover with
    | some w, _, _, _ => some (.refutation ⟨.l, w⟩)
    | _, some w, _, _ => some (.refutation ⟨.r, w⟩)
    | _, _, some lc, some rc => some (.entailment (.cover lc rc))
    | _, _, _, _ => interleave window fuel (turn + 1) l r

/-- Fairly interleave the three searches on each side. -/
def search (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (fuel : ℕ) (window : ℕ := 0) : Option (Candidate n) :=
  let l := newSide (reader (Events.sideSystem c ϕ .l)
    (Events.sideQuery x y .l).1 (Events.sideQuery x y .l).2)
  let r := newSide (reader (Events.sideSystem c ϕ .r)
    (Events.sideQuery x y .r).1 (Events.sideQuery x y .r).2)
  interleave window fuel 0 l r

end DeciNSSE.Solver.Search
