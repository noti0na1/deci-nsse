import DeciNSSE.Main

/-! # Computable countermodel extraction

A side and a word determine a regular assignment. Satisfiability and a hole
check certify that it refutes the query. Under finite satisfiability, bounded
truncation of the same assignment gives a finite countermodel.

The Boolean check `refutesB` is the semantic entry point for refutations. The
certificate checker `Certificates.checkRefutation` is `refutesB` by definition, and
the packed checker `Solver.Checked.checkRefutationPacked` is proved equal to it.

## Main declarations

- `extractRegular`, `extractRegular_of_unsafe`, `extractRegular_spec`: the regular
  countermodel of an unsafe word, or of a hole of a side reader.
- `refutesB`: satisfiability and a hole of the reader of one side.
- `refutesB_iff_unsafe`, `refutesB_correct`, `not_entails_iff_refutesB`: `refutesB`
  holds exactly for unsafe words, so it refutes entailment, and every failure of
  entailment has a word passing it.
- `extractFinite`, `extractFinite_of_unsafe`, `extractFinite_spec`: the finite
  countermodel under finite satisfiability.
-/

namespace DeciNSSE

variable {n k : ℕ}

/-- The regular assignment determined by a side and a word. -/
def extractRegular (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) : V k → RGraph n :=
  RegularTransfer.countermodel c ϕ x y θ w

/-- An unsafe word makes the extracted regular assignment a countermodel. -/
theorem extractRegular_of_unsafe {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hu : Unsafe c ϕ x y θ w) :
    Sat c (RGraph.unfold ∘ extractRegular c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (extractRegular c ϕ x y θ w x).unfold
        (extractRegular c ϕ x y θ w y).unfold :=
  RegularTransfer.countermodel_not_le hu

/-- In a satisfiable system, a hole of the side reader certifies the regular countermodel. -/
theorem extractRegular_spec {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hs : satB c ϕ = true)
    (hw : Monitor.SideHole c ϕ x y θ w) :
    Sat c (RGraph.unfold ∘ extractRegular c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (extractRegular c ϕ x y θ w x).unfold
        (extractRegular c ϕ x y θ w y).unfold :=
  extractRegular_of_unsafe
    ((Monitor.hole_iff_unsafe ((satB_iff c ϕ).mp hs) θ w).mp hw)

/-- Check satisfiability and whether the supplied word is a hole of its side. -/
def refutesB (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) : Bool :=
  satB c ϕ && decide (Holes.IsReaderHole
    (Monitor.sideReader c ϕ x y θ) Monitor.admission (Monitor.sideTarget c ϕ) w)

/-- The Boolean certificate holds exactly for unsafe words. -/
theorem refutesB_iff_unsafe (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) :
    refutesB c ϕ x y θ w = true ↔ Unsafe c ϕ x y θ w := by
  simp only [refutesB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hw⟩
    exact (Monitor.hole_iff_unsafe ((satB_iff c ϕ).mp hs) θ w).mp hw
  · intro hu
    have hs : ∃ ρ, Sat c ρ ϕ := ⟨_, (extractRegular_of_unsafe hu).1⟩
    exact ⟨(satB_iff c ϕ).mpr hs,
      (Monitor.hole_iff_unsafe hs θ w).mpr hu⟩

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

/-- The finite assignment determined by a side and a word: the regular assignment,
truncated at the depth bound of its four-spine extension. -/
def extractFinite (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) (z : V k) : FTree n :=
  FiniteTransfer.countermodel c ϕ x y θ w z

/-- Under finite satisfiability, truncation preserves the extracted regular trees. -/
theorem extractFinite_toTree {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hs : SatisfiableFin c ϕ) (z : V k) :
    (extractFinite c ϕ x y θ w z).toTree = (extractRegular c ϕ x y θ w z).unfold :=
  FiniteTransfer.countermodel_toTree hs z

/-- An unsafe word in a finitely satisfiable system yields a finite countermodel. -/
theorem extractFinite_of_unsafe {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hs : SatisfiableFin c ϕ)
    (hu : Unsafe c ϕ x y θ w) :
    Sat c (FTree.toTree ∘ extractFinite c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (extractFinite c ϕ x y θ w x).toTree
        (extractFinite c ϕ x y θ w y).toTree :=
  FiniteTransfer.countermodel_spec hs hu

/-- In a finitely satisfiable system, a hole of the side reader certifies the finite
countermodel. -/
theorem extractFinite_spec {c : Fin n → Bool} {ϕ : Constraint n k}
    {x y : V k} {θ : Side} {w : List (Fin n)} (hs : SatisfiableFin c ϕ)
    (hw : Monitor.SideHole c ϕ x y θ w) :
    Sat c (FTree.toTree ∘ extractFinite c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (extractFinite c ϕ x y θ w x).toTree
        (extractFinite c ϕ x y θ w y).toTree := by
  obtain ⟨σ, hσ⟩ := hs
  exact extractFinite_of_unsafe ⟨σ, hσ⟩
    ((Monitor.hole_iff_unsafe ⟨_, hσ⟩ θ w).mp hw)

end DeciNSSE
