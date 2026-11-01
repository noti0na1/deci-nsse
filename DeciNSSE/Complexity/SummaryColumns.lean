import DeciNSSE.Complexity.SummaryTables

/-! # Boolean column summaries

The column automaton of `BoundedDepth` reads a right-aligned padded column word
and keeps, for each track, the exits, the blocks' terminal admissions, the
equality pattern of the tracks and the ladders. Over a table these fields are
Boolean, so the automaton has finitely many states and can be run. A final
summary of pairwise distinct blocks determines the table of the derived monitor
on these blocks.

## Main declarations

- `Summary.Summ`: Boolean column summaries, with `Summ.step` and `Summ.start`.
- `Summary.Summ.toProp_eval`: the Boolean run computes the column automaton.
- `Summary.card_summ`: the number of summaries is `colBound`.
- `Summary.started`, `Summary.valid_snoc_iff`: the tracks that have started, which
  decide whether a column extends a valid column word.
- `Summary.derTable`, `Summary.derTable_agree`: the derived table of a summary,
  which agrees with the derived monitor on the blocks.
-/

set_option autoImplicit false

namespace DeciNSSE.Complexity.Summary
open CoAlignment LetteredHierarchy BoundedDepth Packets
open scoped List

section Summ
variable {Γ C : Type*}

/-- Boolean column summaries with `k` tracks over cores `C`: the four fields of
`BoundedDepth.CS`, with Boolean relations. -/
abbrev Summ (C : Type*) (k : ℕ) :=
  (Fin k → Option C → C) × (Fin k → Option C → C → Bool) × (Fin k → Fin k → Bool) ×
    (Fin k → Fin k → Option C → Option C → Bool)

/-- The column-automaton state denoted by a Boolean summary. -/
def Summ.toProp {k : ℕ} (s : Summ C k) : CS C k :=
  (s.1, fun a c d => s.2.1 a c d = true, fun a b => s.2.2.1 a b = true,
    fun a b c c' => s.2.2.2 a b c c' = true)

variable (T : Table Γ C) (ℓ : Γ) {k : ℕ}

/-- The initial Boolean summary (all tracks empty), as `BoundedDepth.colStart`. -/
def Summ.start (k : ℕ) : Summ C k :=
  (fun _ c => fcore T.toLettered ℓ c [], fun _ c d => T.Λf (lab0 ℓ c) (some (d, ℓ)),
    fun _ _ => true, fun _ _ c c' => T.Λ (lab0 ℓ c) (lab0 ℓ c'))

theorem Summ.toProp_start : (Summ.start T ℓ k).toProp = colStart T.toLettered ℓ k := by
  simp only [Summ.start, Summ.toProp, colStart]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp

variable [DecidableEq Γ]

/-- The transition of the Boolean column automaton (as `BoundedDepth.colStep`). -/
def Summ.step (x : Summ C k) (col : Fin k → Option Γ) : Summ C k :=
  (fun a c => match col a with
      | none => x.1 a c
      | some z => T.κ z (x.1 a c),
   fun a c d => match col a with
      | none => x.2.1 a c d
      | some z => x.2.1 a c d || T.Λf (some (x.1 a c, z)) (some (d, ℓ)),
   fun a b => x.2.2.1 a b && decide (col a = col b),
   fun a b c c' => match col a, col b with
      | none, none => x.2.2.2 a b c c'
      | none, some z' => T.Λ (lab0 ℓ c) (some (x.1 b c', z'))
      | some z, none => T.Λ (some (x.1 a c, z)) (lab0 ℓ c')
      | some z, some z' =>
          T.Λ (some (x.1 a c, z)) (some (x.1 b c', z')) || (decide (z = z') && x.2.2.2 a b c c'))

theorem Summ.toProp_step (x : Summ C k) (col : Fin k → Option Γ) :
    (Summ.step T ℓ x col).toProp = colStep T.toLettered ℓ k x.toProp col := by
  simp only [Summ.step, Summ.toProp, colStep]
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
theorem Summ.toProp_eval (w : List (Fin k → Option Γ)) :
    (w.foldl (Summ.step T ℓ) (Summ.start T ℓ k)).toProp = (colDFA T.toLettered ℓ k).eval w := by
  suffices h : ∀ x : Summ C k, (w.foldl (Summ.step T ℓ) x).toProp =
      (colDFA T.toLettered ℓ k).evalFrom x.toProp w by
    rw [h, Summ.toProp_start]; rfl
  induction w with
  | nil => intro x; rfl
  | cons col w ih =>
    intro x
    rw [List.foldl_cons, ih, DFA.evalFrom_cons, Summ.toProp_step]
    rfl

end Summ

section Card
variable {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ)

instance instFintypeSumm : Fintype (Summ C k) :=
  @instFintypeProd _ _ inferInstance
    (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance inferInstance))

instance instDecEqSumm : DecidableEq (Summ C k) :=
  @instDecidableEqProd _ _ inferInstance
    (@instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance inferInstance))

/-- The number of Boolean summaries is the number of column-automaton states. -/
theorem card_summ : Fintype.card (Summ C k) = colBound (Fintype.card C) k := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
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
def derTable (s : Summ C k) : Table (Fin k) (Option C) where
  start := none
  κ a c := some (s.1 a c)
  Λ L L' := match L, L' with
    | some (c, a), some (c', b) => s.2.2.2 a b c c'
    | _, _ => false
  Λf L L' := match L, L' with
    | some (c, a), some (c', b) => s.2.2.2 a b c c' || s.2.1 a c (s.1 b c')
    | _, _ => false
  Tf c a := T.Tf (s.1 a c) ℓ && !s.2.1 a c (s.1 a c)

/-- The summary of pairwise distinct blocks `Ys` determines the derived monitor on them:
the derived table agrees with `Der(T, ℓ)` along `Ys`. -/
theorem derTable_agree {s : Summ C k} {Ys : Fin k → List Γ}
    (hs : s.toProp = summ T.toLettered ℓ k Ys) (hd : ∀ a b, s.2.2.1 a b = true → a = b) :
    Agree (derTable T ℓ s).toLettered (der T.toLettered ℓ) Ys (List.finRange k) := by
  have h1 : ∀ a c, s.1 a c = fcore T.toLettered ℓ c (Ys a) := fun a c =>
    congrFun (congrFun (congrArg Prod.fst hs) a) c
  have h2 : ∀ a c d, s.2.1 a c d = true ↔
      ∃ p ≤ (Ys a).length, T.toLettered.Λf (zlab T.toLettered ℓ c (Ys a) p) (some (d, ℓ)) :=
    fun a c d => Iff.of_eq (congrFun (congrFun (congrFun (congrArg (fun s => s.2.1) hs) a) c) d)
  have h3 : ∀ a b, s.2.2.1 a b = true ↔ Ys a = Ys b := fun a b =>
    Iff.of_eq (congrFun (congrFun (congrArg (fun s => s.2.2.1) hs) a) b)
  have h4 : ∀ a b c c', s.2.2.2 a b c c' = true ↔
      derΛ T.toLettered ℓ (some (c, Ys a)) (some (c', Ys b)) := fun a b c c' =>
    Iff.of_eq (congrFun (congrFun (congrFun (congrFun
      (congrArg (fun s => s.2.2.2) hs) a) b) c) c')
  refine ⟨rfl, fun a _ b _ hab => hd a b ((h3 a b).mpr hab), fun a _ c => ?_, fun a _ c => ?_,
    fun L L' _ _ => ?_, fun L L' _ _ => ?_⟩
  · simp [der_κ, derTable, h1]
  · simp only [der_Tf, derTf, Table.toLettered_Tf, derTable, Bool.and_eq_true, Bool.not_eq_true',
      ← h1, ← h2, Bool.not_eq_true]
  · rcases L with _ | ⟨c, a⟩ <;> rcases L' with _ | ⟨c', b⟩
    · simp [derΛ, derTable]
    · simp [derΛ, derTable]
    · simp [derΛ, derTable]
    · simp only [mapLab_some, der_Λ, Table.toLettered_Λ, derTable]
      exact (h4 a b c c').symm
  · rcases L with _ | ⟨c, a⟩ <;> rcases L' with _ | ⟨c', b⟩
    · simp [derΛf, derTable]
    · simp [derΛf, derTable]
    · simp [derΛf, derTable]
    · simp only [mapLab_some, der_Λf, derΛf, Table.toLettered_Λf, derTable, Bool.or_eq_true,
        ← h4, ← h1, h2]

end Derived

end DeciNSSE.Complexity.Summary
