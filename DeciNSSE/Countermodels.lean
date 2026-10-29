import DeciNSSE.Main

/-! # Computable countermodel extraction

A side and a word determine a regular assignment. Satisfiability and a hole
check certify that it refutes the query. Under finite satisfiability, bounded
truncation of the same assignment gives a finite countermodel.
-/

namespace DeciNSSE

open scoped Monitor

variable {n k : ℕ}

/-- The regular assignment selected by a side and a word. -/
def extractRegular (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) : V k → RGraph n :=
  RegularTransfer.countermodel c ϕ x y θ w

/-- An unsafe word makes the extracted regular assignment a countermodel. -/
theorem extractRegular_of_unsafe {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hu : Unsafe c ϕ x y θ w) :
    Sat c (RGraph.unfold ∘ extractRegular c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (extractRegular c ϕ x y θ w x).unfold
        (extractRegular c ϕ x y θ w y).unfold := by
  obtain ⟨hs, hw⟩ := RegularTransfer.countermodel_spec hu
  exact ⟨hs, fun hle => hw ((treeLe_iff_safe c _ _).mp hle w)⟩

/-- In a satisfiable system, a monitor hole certifies the regular countermodel. -/
theorem extractRegular_spec {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hs : Monitor.satB c ϕ = true)
    (hw : (Monitor.sideMonitor c ϕ x y θ).Hole w) :
    Sat c (RGraph.unfold ∘ extractRegular c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (extractRegular c ϕ x y θ w x).unfold
        (extractRegular c ϕ x y θ w y).unfold :=
  extractRegular_of_unsafe
    (((Monitor.sideMonitor c ϕ x y θ).hole_iff_unsafe ((Monitor.satB_iff c ϕ).mp hs) w).mp hw)

/-- Check satisfiability and whether the supplied word is a hole of its side. -/
def refutesB (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) : Bool :=
  let ψ := Events.sideSystem c ϕ θ
  let q := Events.sideQuery x y θ
  Monitor.satB c ϕ && decide (Holes.IsReaderHole
    (Monitor.reader ψ q.1 q.2) Monitor.admission (Monitor.target ψ) w)

/-- The Boolean certificate holds exactly for unsafe words. -/
theorem refutesB_iff_unsafe (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) :
    refutesB c ϕ x y θ w = true ↔ Unsafe c ϕ x y θ w := by
  simp only [refutesB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hw⟩
    exact ((Monitor.sideMonitor c ϕ x y θ).hole_iff_unsafe
      ((Monitor.satB_iff c ϕ).mp hs) w).mp hw
  · intro hu
    have hs : ∃ ρ, Sat c ρ ϕ := ⟨_, (extractRegular_of_unsafe hu).1⟩
    exact ⟨(Monitor.satB_iff c ϕ).mpr hs,
      ((Monitor.sideMonitor c ϕ x y θ).hole_iff_unsafe hs w).mpr hu⟩

/-- A successful Boolean certificate refutes unrestricted entailment. -/
theorem refutesB_correct {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}
    {θ : Side} {w : List (Fin n)} (h : refutesB c ϕ x y θ w = true) :
    ¬ Entails c ϕ x y := by
  obtain ⟨hs, hn⟩ := extractRegular_of_unsafe ((refutesB_iff_unsafe c ϕ x y θ w).mp h)
  exact fun he => hn (he _ hs)

/-- Every failure of entailment has a side and a word passing the Boolean check. -/
theorem not_entails_iff_refutesB (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    ¬ Entails c ϕ x y ↔ ∃ θ w, refutesB c ϕ x y θ w = true := by
  simp only [refutesB_iff_unsafe, entails_iff_not_sideUnsafe, not_forall, not_not]

private theorem witnessGraph_depth {c : Fin n → Bool} {ψ : Constraint n (2 * k)}
    {X Y : V (2 * k)} {w : List (Fin n)} (hf : FiniteVariance.FlipClosed ψ)
    (hcy : ¬ CycleClash ψ) (z : V (2 * k)) (π : List (Fin n))
    (hπ : ((RegularTransfer.witnessGraph c ψ X Y w z).unfold.fn π).isSome) :
    π.length ≤ (2 * (k + (2 * w.length + 2))) ^ 2 + 1 := by
  have hcy' : ¬ CycleClash (Spine.extension c ψ X Y w) :=
    fun h => hcy ((Spine.Closure.extension_ranked c X Y w ψ).cycleClash_iff.mp h)
  have he := congrFun
    (unfold_selectGraph_shapeGraph c (ψ := Spine.extension c ψ X Y w)
      (Spine.Closure.extension_flipClosed hf))
    (Spine.Closure.lift z)
  change (RegularTransfer.witnessGraph c ψ X Y w z).unfold = _ at he
  rw [he] at hπ
  simpa only [Nat.pow_two] using
    FiniteVariance.select_depth c _ _ (leastShape_depth hcy') _ π hπ

private theorem extractRegular_depth {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hs : SatisfiableFin c ϕ)
    (z : V k) (π : List (Fin n))
    (hπ : ((extractRegular c ϕ x y θ w z).unfold.fn π).isSome) :
    π.length ≤ (2 * (k + (2 * w.length + 2))) ^ 2 + 1 := by
  have hcy := FiniteTransfer.sideSystem_not_cycleClash hs θ
  have hf := Events.sideSystem_flipClosed (c := c) (ϕ := ϕ) θ
  cases θ <;>
    simp only [extractRegular, RegularTransfer.countermodel, decodedGraph,
      RGraph.unfold_normalize, normalize_domain, Function.comp_apply] at hπ
  · exact witnessGraph_depth hf hcy _ π hπ
  · exact witnessGraph_depth hf hcy _ π hπ

/-- Truncate the regular assignment at the depth bound of its four-spine extension. -/
def extractFinite (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) (z : V k) : FTree n :=
  FTree.ofTree ((2 * (k + (2 * w.length + 2))) ^ 2 + 1)
    (extractRegular c ϕ x y θ w z).unfold

/-- Under finite satisfiability, truncation preserves the extracted regular trees. -/
theorem extractFinite_toTree {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hs : SatisfiableFin c ϕ) (z : V k) :
    (extractFinite c ϕ x y θ w z).toTree = (extractRegular c ϕ x y θ w z).unfold :=
  FTree.toTree_ofTree (extractRegular_depth hs z)

/-- An unsafe word in a finitely satisfiable system yields a finite countermodel. -/
theorem extractFinite_of_unsafe {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hs : SatisfiableFin c ϕ)
    (hu : Unsafe c ϕ x y θ w) :
    Sat c (FTree.toTree ∘ extractFinite c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (extractFinite c ϕ x y θ w x).toTree
        (extractFinite c ϕ x y θ w y).toTree := by
  have he : FTree.toTree ∘ extractFinite c ϕ x y θ w =
      RGraph.unfold ∘ extractRegular c ϕ x y θ w := funext (extractFinite_toTree hs)
  rw [he, extractFinite_toTree hs, extractFinite_toTree hs]
  exact extractRegular_of_unsafe hu

/-- A monitor hole in a finitely satisfiable system certifies the finite countermodel. -/
theorem extractFinite_spec {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hs : SatisfiableFin c ϕ)
    (hw : (Monitor.sideMonitor c ϕ x y θ).Hole w) :
    Sat c (FTree.toTree ∘ extractFinite c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (extractFinite c ϕ x y θ w x).toTree
        (extractFinite c ϕ x y θ w y).toTree := by
  obtain ⟨σ, hσ⟩ := hs
  exact extractFinite_of_unsafe ⟨σ, hσ⟩
    (((Monitor.sideMonitor c ϕ x y θ).hole_iff_unsafe ⟨_, hσ⟩ w).mp hw)

end DeciNSSE
