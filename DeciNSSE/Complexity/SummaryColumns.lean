import DeciNSSE.Complexity.SummaryTables

/-! # Boolean column summaries

The column automaton of `BoundedDepth` reads a right-aligned padded column word
and keeps, for each track, the exits, the blocks' terminal admissions, the
equality pattern of the tracks and the ladders. Over a table these fields are
Boolean, so the automaton has finitely many states and can be run. A final
summary of pairwise distinct blocks determines the table of the derived monitor
on these blocks.

## Main declarations

- `Summary.ColumnSummary`: Boolean column summaries, with `ColumnSummary.step` and
  `ColumnSummary.start`.
- `Summary.ColumnSummary.toProp_eval`: the Boolean run computes the column automaton.
- `Summary.card_columnSummary`: the number of summaries is `colBound`.
- `Summary.started`, `Summary.valid_snoc_iff`: the tracks that have started, which
  decide whether a column extends a valid column word.
- `Summary.derivedTable`, `Summary.derivedTable_agree`: the derived table of a summary,
  which agrees with the derived monitor on the blocks.
-/

namespace DeciNSSE.Complexity.Summary
open CoAlignment LetteredHierarchy BoundedDepth Packets
open scoped List

/-- Boolean column summaries with `k` tracks over cores `C`: the four fields of
`BoundedDepth.CS`, with Boolean relations. -/
structure ColumnSummary (C : Type*) (k : ℕ) where
  /-- The exit core of each track from each start core. -/
  exit : Fin k → Option C → C
  /-- `terminalAdmission a c d`: some label of the shifted block of track `a` from `c` is
  admitted against the final label `(d, ℓ)`. -/
  terminalAdmission : Fin k → Option C → C → Bool
  /-- `equalTracks a b`: tracks `a` and `b` carry the same block. -/
  equalTracks : Fin k → Fin k → Bool
  /-- `ladderAdmission a b c c'`: the ladder relates block `a` from `c` and block `b`
  from `c'`. -/
  ladderAdmission : Fin k → Fin k → Option C → Option C → Bool

namespace ColumnSummary
variable {Γ C : Type*}

/-- The column-automaton state denoted by a Boolean summary. -/
def toProp {k : ℕ} (s : ColumnSummary C k) : CS C k :=
  (s.exit, fun a c d => s.terminalAdmission a c d = true, fun a b => s.equalTracks a b = true,
    fun a b c c' => s.ladderAdmission a b c c' = true)

variable (T : Table Γ C) (ℓ : Γ) {k : ℕ}

/-- The initial Boolean summary (all tracks empty), as `BoundedDepth.colStart`. -/
def start (k : ℕ) : ColumnSummary C k where
  exit _ c := fcore T.toLettered ℓ c []
  terminalAdmission _ c d := T.Λf (lab0 ℓ c) (some (d, ℓ))
  equalTracks _ _ := true
  ladderAdmission _ _ c c' := T.Λ (lab0 ℓ c) (lab0 ℓ c')

theorem toProp_start : (start T ℓ k).toProp = colStart T.toLettered ℓ k := by
  simp only [start, toProp, colStart]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp

variable [DecidableEq Γ]

/-- The transition of the Boolean column automaton (as `BoundedDepth.colStep`). -/
def step (x : ColumnSummary C k) (col : Fin k → Option Γ) : ColumnSummary C k where
  exit a c := match col a with
    | none => x.exit a c
    | some z => T.κ z (x.exit a c)
  terminalAdmission a c d := match col a with
    | none => x.terminalAdmission a c d
    | some z => x.terminalAdmission a c d || T.Λf (some (x.exit a c, z)) (some (d, ℓ))
  equalTracks a b := x.equalTracks a b && decide (col a = col b)
  ladderAdmission a b c c' := match col a, col b with
    | none, none => x.ladderAdmission a b c c'
    | none, some z' => T.Λ (lab0 ℓ c) (some (x.exit b c', z'))
    | some z, none => T.Λ (some (x.exit a c, z)) (lab0 ℓ c')
    | some z, some z' =>
        T.Λ (some (x.exit a c, z)) (some (x.exit b c', z')) ||
          (decide (z = z') && x.ladderAdmission a b c c')

theorem toProp_step (x : ColumnSummary C k) (col : Fin k → Option Γ) :
    (step T ℓ x col).toProp = colStep T.toLettered ℓ k x.toProp col := by
  simp only [step, toProp, colStep, CS.exit_mk, CS.terminalAdmission_mk, CS.equalTracks_mk,
    CS.ladderAdmission_mk]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext a c
    dsimp only
    rcases col a with _ | z <;> rfl
  · funext a c d
    dsimp only
    rcases col a with _ | z <;> simp
  · funext a b
    simp
  · funext a b c c'
    dsimp only
    rcases col a with _ | z <;> rcases col b with _ | z' <;> simp

/-- The Boolean run computes the column automaton. -/
theorem toProp_eval (w : List (Fin k → Option Γ)) :
    (w.foldl (step T ℓ) (start T ℓ k)).toProp = (colDFA T.toLettered ℓ k).eval w := by
  suffices h : ∀ x : ColumnSummary C k, (w.foldl (step T ℓ) x).toProp =
      (colDFA T.toLettered ℓ k).evalFrom x.toProp w by
    rw [h, toProp_start]; rfl
  induction w with
  | nil => intro x; rfl
  | cons col w ih =>
    intro x
    rw [List.foldl_cons, ih, DFA.evalFrom_cons, toProp_step]
    rfl

/-- Summaries as tuples of their fields. -/
def equivProd : ColumnSummary C k ≃ (Fin k → Option C → C) × (Fin k → Option C → C → Bool) ×
    (Fin k → Fin k → Bool) × (Fin k → Fin k → Option C → Option C → Bool) where
  toFun s := (s.exit, s.terminalAdmission, s.equalTracks, s.ladderAdmission)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ColumnSummary

section Card
variable {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ)

/-- The product of the fields, with its `Fintype` instance spelled out. -/
@[instance_reducible] private def fieldsFintype :
    Fintype ((Fin k → Option C → C) × (Fin k → Option C → C → Bool) ×
      (Fin k → Fin k → Bool) × (Fin k → Fin k → Option C → Option C → Bool)) :=
  @instFintypeProd _ _ inferInstance
    (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance inferInstance))

instance instFintypeColumnSummary : Fintype (ColumnSummary C k) :=
  @Fintype.ofEquiv _ _ (fieldsFintype k) ColumnSummary.equivProd.symm

instance instDecEqColumnSummary : DecidableEq (ColumnSummary C k) := fun s s' =>
  decidable_of_iff (s.exit = s'.exit ∧ s.terminalAdmission = s'.terminalAdmission ∧
      s.equalTracks = s'.equalTracks ∧ s.ladderAdmission = s'.ladderAdmission)
    (by cases s; cases s'; simp)

/-- The number of Boolean summaries is the number of column-automaton states. -/
theorem card_columnSummary : Fintype.card (ColumnSummary C k) = colBound (Fintype.card C) k := by
  rw [@Fintype.card_congr _ _ _ (fieldsFintype k) ColumnSummary.equivProd, fieldsFintype,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  simp [Fintype.card_option, colBound, mul_assoc]

end Card

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
    (hs : s.toProp = summ T.toLettered ℓ k Ys) (hd : ∀ a b, s.equalTracks a b = true → a = b) :
    Agree (derivedTable T ℓ s).toLettered (der T.toLettered ℓ) Ys (List.finRange k) := by
  have h1 : ∀ a c, s.exit a c = fcore T.toLettered ℓ c (Ys a) := fun a c =>
    congrFun (congrFun (congrArg CS.exit hs) a) c
  have h2 : ∀ a c d, s.terminalAdmission a c d = true ↔
      ∃ p ≤ (Ys a).length, T.toLettered.Λf (zlab T.toLettered ℓ c (Ys a) p) (some (d, ℓ)) :=
    fun a c d => Iff.of_eq (congrFun (congrFun (congrFun
      (congrArg CS.terminalAdmission hs) a) c) d)
  have h3 : ∀ a b, s.equalTracks a b = true ↔ Ys a = Ys b := fun a b =>
    Iff.of_eq (congrFun (congrFun (congrArg CS.equalTracks hs) a) b)
  have h4 : ∀ a b c c', s.ladderAdmission a b c c' = true ↔
      derΛ T.toLettered ℓ (some (c, Ys a)) (some (c', Ys b)) := fun a b c c' =>
    Iff.of_eq (congrFun (congrFun (congrFun (congrFun
      (congrArg CS.ladderAdmission hs) a) b) c) c')
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
