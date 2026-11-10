import DeciNSSE.Complexity.SummaryTables

/-! # Boolean column summaries

The Boolean column automaton reads a right-aligned padded column word using
admissions from a finite table. Its semantic summary records exits, terminal
admissions, track equality, and ladders. A summary of pairwise distinct blocks
determines the table of the derived monitor on these blocks.

## Main declarations

- `Summary.ColumnSummary.step`, `Summary.ColumnSummary.start`: table instances of the
  column automaton.
- `Summary.ColumnSummary.eval`: the run computes the semantic summary.
- `Summary.started`, `Summary.valid_snoc_iff`: the tracks that have started, which
  decide whether a column extends a valid column word.
- `Summary.derivedTable`, `Summary.derivedTable_agree`: the derived table of a summary,
  which agrees with the derived monitor on the blocks.
-/

namespace DeciNSSE.Complexity.Summary
open CoAlignment LetteredHierarchy BoundedDepth Packets
open scoped List

namespace ColumnSummary
variable {Γ C : Type*} (T : Table Γ C) (ℓ : Γ) {k : ℕ}

/-- The column summary of empty tracks for a table. -/
abbrev start (k : ℕ) : BoundedDepth.ColumnSummary C k :=
  BoundedDepth.ColumnSummary.start T.start T.κ T.Λ T.Λf ℓ k

/-- The column transition using the table's Boolean admissions. -/
abbrev step [DecidableEq Γ] : BoundedDepth.ColumnSummary C k →
    (Fin k → Option Γ) → BoundedDepth.ColumnSummary C k :=
  BoundedDepth.ColumnSummary.step T.κ T.Λ T.Λf ℓ

/-- A valid column word computes its semantic summary. -/
theorem eval [DecidableEq Γ] (w : List (Fin k → Option Γ)) (hw : Valid w) :
    w.foldl (step T ℓ) (start T ℓ k) = summ T.toLettered ℓ k (dec w) :=
  colEval T.toLettered ℓ k T.Λ T.Λf (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) w hw

end ColumnSummary

section Started
variable {σ : Type*} {k : ℕ}

/-- The tracks of a column word that carry a letter. -/
def started (w : List (Fin k → Option σ)) (a : Fin k) : Bool := !(dec w a).isEmpty

theorem started_nil (a : Fin k) : started ([] : List (Fin k → Option σ)) a = false := rfl

theorem started_snoc (w : List (Fin k → Option σ)) (col : Fin k → Option σ) (a : Fin k) :
    started (w ++ [col]) a = (started w a || (col a).isSome) := by
  simp only [started, dec_snoc]
  rcases col a with _ | z <;> simp

theorem started_eq_true {w : List (Fin k → Option σ)} {a : Fin k} :
    started w a = true ↔ dec w a ≠ [] := by
  simp [started]

/-- A padded track stays padded under one more entry iff padding does not follow a letter. -/
theorem padPre_snoc_iff {l : List (Option σ)} (hl : PadPre l) (x : Option σ) :
    PadPre (l ++ [x]) ↔ (l.reduceOption ≠ [] → x.isSome) := by
  obtain ⟨m, P, rfl⟩ := hl
  rw [reduceOption_pad]
  constructor
  · rintro ⟨m', P', h⟩ hP
    rcases x with _ | z
    · exfalso
      rcases List.eq_nil_or_concat P' with rfl | ⟨P'', y, rfl⟩
      · exact hP (by simpa [List.reduceOption_append, List.reduceOption_replicate_none,
          reduceOption_map_some] using congrArg List.reduceOption h)
      · simp only [List.concat_eq_append, List.map_append, List.map_singleton,
          ← List.append_assoc] at h
        exact absurd (List.append_inj_right' h rfl) (by simp)
    · rfl
  · intro h
    rcases x with _ | z
    · have hP : P = [] := by
        by_contra hP
        exact absurd (h hP) (by simp)
      subst hP
      exact ⟨m + 1, [], by simp [List.replicate_succ']⟩
    · exact ⟨m, P ++ [z], by simp⟩

/-- A column extends a valid column word iff it carries a letter on every started track. -/
theorem valid_snoc_iff {w : List (Fin k → Option σ)} (hw : Valid w) (col : Fin k → Option σ) :
    Valid (w ++ [col]) ↔ ∀ a, started w a = true → (col a).isSome := by
  have htr : ∀ a, tr (w ++ [col]) a = tr w a ++ [col a] := fun a => by
    simp [tr]
  refine forall_congr' fun a => ?_
  rw [htr, padPre_snoc_iff (hw a), started_eq_true]
  rfl

theorem mem_dec {w : List (Fin k → Option σ)} {a : Fin k} {z : σ} :
    z ∈ dec w a ↔ ∃ col ∈ w, col a = some z := by
  simp [dec, tr, List.reduceOption_mem_iff]

end Started

section Derived
variable {Γ C : Type*} (T : Table Γ C) (ℓ : Γ) {k : ℕ}

/-- The table of the derived monitor on `k` blocks, read off their summary: letter `a` is
block `a`, and the start core is the new core `none`. -/
def derivedTable (s : ColumnSummary C k) : Table (Fin k) (Option C) where
  start := none
  κ a c := some (s.exit a c)
  Λ L L' := match L, L' with
    | some (c, a), some (c', b) => s.ladderAdmission a b c c'
    | _, _ => false
  Λf L L' := match L, L' with
    | some (c, a), some (c', b) =>
      s.ladderAdmission a b c c' || s.terminalAdmission a c (s.exit b c')
    | _, _ => false
  Tf c a := T.Tf (s.exit a c) ℓ && !s.terminalAdmission a c (s.exit a c)

/-- The summary of pairwise distinct blocks `Ys` determines the derived monitor on them:
the derived table agrees with `Der(T, ℓ)` along `Ys`. -/
theorem derivedTable_agree {s : ColumnSummary C k} {Ys : Fin k → List Γ}
    (hs : s = summ T.toLettered ℓ k Ys) (hd : ∀ a b, s.equalTracks a b = true → a = b) :
    Agree (derivedTable T ℓ s).toLettered (der T.toLettered ℓ) Ys (List.finRange k) := by
  have h1 : ∀ a c, s.exit a c = fcore T.toLettered ℓ c (Ys a) := fun a c =>
    congrArg (fun s => s.exit a c) hs
  have h2 : ∀ a c d, s.terminalAdmission a c d = true ↔
      ∃ p ≤ (Ys a).length, T.toLettered.Λf (zlab T.toLettered ℓ c (Ys a) p) (some (d, ℓ)) :=
    fun a c d => by
      simpa only [summ, decide_eq_true_eq] using
        Bool.eq_iff_iff.mp (congrArg (fun s => s.terminalAdmission a c d) hs)
  have h3 : ∀ a b, s.equalTracks a b = true ↔ Ys a = Ys b := fun a b => by
    simpa only [summ, decide_eq_true_eq] using
      Bool.eq_iff_iff.mp (congrArg (fun s => s.equalTracks a b) hs)
  have h4 : ∀ a b c c', s.ladderAdmission a b c c' = true ↔
      derΛ T.toLettered ℓ (some (c, Ys a)) (some (c', Ys b)) := fun a b c c' => by
    simpa only [summ, decide_eq_true_eq] using
      Bool.eq_iff_iff.mp (congrArg (fun s => s.ladderAdmission a b c c') hs)
  refine ⟨rfl, fun a _ b _ hab => hd a b ((h3 a b).mpr hab), fun a _ c => ?_, fun a _ c => ?_,
    fun L L' _ _ => ?_, fun L L' _ _ => ?_⟩
  · simp [der_κ, derivedTable, h1]
  · simp only [der_Tf, derTf, Table.toLettered_Tf, derivedTable, Bool.and_eq_true,
      Bool.not_eq_true', ← h1, ← h2, Bool.not_eq_true]
  · rcases L with _ | ⟨c, a⟩ <;> rcases L' with _ | ⟨c', b⟩
    · simp [derΛ, derivedTable]
    · simp [derΛ, derivedTable]
    · simp [derΛ, derivedTable]
    · simp only [mapLab_some, der_Λ, Table.toLettered_Λ, derivedTable]
      exact (h4 a b c c').symm
  · rcases L with _ | ⟨c, a⟩ <;> rcases L' with _ | ⟨c', b⟩
    · simp [derΛf, derivedTable]
    · simp [derΛf, derivedTable]
    · simp [derΛf, derivedTable]
    · simp only [mapLab_some, der_Λf, derΛf, Table.toLettered_Λf, derivedTable,
        Bool.or_eq_true, ← h4, ← h1, h2]

end Derived


end DeciNSSE.Complexity.Summary
