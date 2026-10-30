import DeciNSSE.Countermodels

/-! # Restricting graphs to reachable states

An untrusted breadth-first traversal supplies a finite closed list. Membership
checks justify the restriction, whose unfolding is unchanged.
-/

namespace DeciNSSE.RGraph
variable {n : ℕ}

/-- A closed list contains the root and all constructor successors. -/
abbrev Closed (g : RGraph n) (qs : List (Fin g.size)) : Prop :=
  g.root ∈ qs ∧ ∀ q ∈ qs, g.label q = .f → ∀ a, g.child q a ∈ qs

/-- Check closure by traversing the supplied list only. -/
def closedB (g : RGraph n) (qs : List (Fin g.size)) : Bool :=
  decide (g.root ∈ qs) && qs.all (fun q => if g.label q = .f then
    (List.finRange n).all (fun a => decide (g.child q a ∈ qs)) else true)

theorem closedB_iff (g : RGraph n) (qs : List (Fin g.size)) :
    closedB g qs = true ↔ Closed g qs := by
  simp only [closedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Closed]
  apply and_congr_right
  intro _
  apply forall_congr'; intro q
  apply forall_congr'; intro _
  by_cases h : g.label q = .f <;> simp [h]

/-- The position of a state in a checked list. -/
def locate {g : RGraph n} (qs : List (Fin g.size)) (q : Fin g.size) (h : q ∈ qs) :
    Fin qs.length := ⟨qs.idxOf q, List.idxOf_lt_length_iff.mpr h⟩

@[simp] theorem get_locate {g : RGraph n} (qs : List (Fin g.size))
    (q : Fin g.size) (h : q ∈ qs) : qs.get (locate qs q h) = q := by
  simp [locate, List.get_eq_getElem]

/-- Number a closed list by its positions. -/
@[implicit_reducible] def restrict (g : RGraph n) (qs : List (Fin g.size)) (h : Closed g qs) : RGraph n where
  size := qs.length
  root := locate qs g.root h.1
  label i := g.label (qs.get i)
  child i a := if hf : g.label (qs.get i) = .f then
      locate qs (g.child (qs.get i) a) (h.2 _ (List.get_mem ..) hf a)
    else locate qs g.root h.1

/-- Graph restriction preserves every path label. -/
theorem unfold_restrict (g : RGraph n) (qs : List (Fin g.size)) (h : Closed g qs) :
    (restrict g qs h).unfold = g.unfold := by
  have walk (i : Fin qs.length) (w : List (Fin n)) :
      ((restrict g qs h).walkFrom i w).map qs.get = g.walkFrom (qs.get i) w := by
    induction w generalizing i with
    | nil => rfl
    | cons a w ih =>
      simp only [walkFrom, restrict]
      split <;> rename_i hf
      · simpa only [restrict, dite_eq_left hf, get_locate] using ih
          (locate qs (g.child (qs.get i) a) (h.2 _ (List.get_mem ..) hf a))
      · rfl
  apply Tree.ext
  funext w
  have hw := walk (locate qs g.root h.1) w
  rw [get_locate] at hw
  change ((restrict g qs h).walkFrom (locate qs g.root h.1) w).map
    (g.label ∘ qs.get) = (g.walkFrom g.root w).map g.label
  simpa only [Option.map_map] using congrArg (Option.map g.label) hw

/-- Enumerate constructor successors with a finite budget. -/
def reachable (g : RGraph n) : ℕ → Array (Fin g.size) → Std.HashSet (Fin g.size) →
    ℕ → Array (Fin g.size)
  | 0, qs, _, _ => qs
  | fuel + 1, qs, seen, cursor =>
    if h : cursor < qs.size then
      let q := qs[cursor]
      let (qs, seen) := if g.label q = .f then
        (List.finRange n).foldl (fun (acc : Array (Fin g.size) × Std.HashSet (Fin g.size)) a =>
          let t := g.child q a
          if acc.2.contains t then acc else (acc.1.push t, acc.2.insert t)) (qs, seen)
        else (qs, seen)
      reachable g fuel qs seen (cursor + 1)
    else qs

/-- Use a checked reachable subgraph, or retain the original graph. -/
def compact (g : RGraph n) (fuel : ℕ := 100000) : RGraph n :=
  let qs := (reachable g fuel #[g.root] (.emptyWithCapacity |>.insert g.root) 0).toList
  if h : closedB g qs = true then restrict g qs ((closedB_iff g qs).mp h) else g

/-- Compaction is exact even if the traversal exhausts its budget. -/
theorem unfold_compact (g : RGraph n) (fuel : ℕ) :
    (compact g fuel).unfold = g.unfold := by
  unfold compact
  dsimp only
  split
  · exact unfold_restrict ..
  · rfl

end DeciNSSE.RGraph
