import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import DeciNSSE.Holes.Agree
import DeciNSSE.Holes.Packets

/-! # The column automaton

Fix a lettered monitor `D` over cores `C` and a marker `ℓ`. A `k`-tuple of
blocks is read as a right-aligned padded word of columns. The column automaton
keeps, for each track and start core, the exit core and the terminal
admissions of the shifted block, and for each pair of tracks their equality
and their ladder `Λ'`. This summary determines the atomic type of the tuple in
`Der(D, ℓ)`, and a finite automaton has short representatives for each of its
states.

## Main declarations

- `CS`: the states, with projections `CS.exit`, `CS.terminalAdmission`,
  `CS.equalTracks` and `CS.ladderAdmission`.
- `colStep`, `colStart`, `colDFA`: the column automaton.
- `summ`, `colEval`: the intended summary of a tuple, computed by the automaton.
- `colBound`, `card_CS`: the number of states.
- `der_type_of_summ`: the summary determines the derived atomic type.
- `exists_short_tuple`, `exists_short_letters`: short tuples with the same
  summary, and short letters with the same derived atomic type.

The declarations are in the namespace `DeciNSSE.BoundedDepth`.
-/

namespace DeciNSSE.BoundedDepth
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.Packets
open scoped List

section Column
variable {Γ C : Type*} (D : Lettered Γ C) (ℓ : Γ)

/-- The label of position `0` of a shifted block: `(c, ℓ)`, or `S` for the new start core. -/
def lab0 (c : Option C) : Lab Γ C := c.map fun c => (c, ℓ)

/-- Position `0` of a shifted block carries `lab0`. -/
theorem zlab_zero (c : Option C) (X : List Γ) : zlab D ℓ c X 0 = lab0 ℓ c := by
  rcases c with _ | c
  · rfl
  · simp [zlab, labFrom, lab0]

/-- Appending a letter to a block moves its exit core by `κ`. -/
theorem fcore_snoc (c : Option C) (X : List Γ) (z : Γ) :
    fcore D ℓ c (X ++ [z]) = D.κ z (fcore D ℓ c X) := by
  rcases c with _ | c
  · simp only [fcore, kst_append]; rfl
  · simp only [fcore]; rw [← List.cons_append, kst_append]; rfl

/-- Appending a letter keeps the earlier labels of a shifted block. -/
theorem zlab_snoc_le (c : Option C) (X : List Γ) (z : Γ) {p : ℕ} (hp : p ≤ X.length) :
    zlab D ℓ c (X ++ [z]) p = zlab D ℓ c X p := by
  rcases c with _ | c
  · exact labFrom_append_le D _ X [z] hp
  · simp only [zlab]
    rw [← List.cons_append]
    exact labFrom_append_le D _ (ℓ :: X) [z] (by simp; omega)

/-- The label of an appended letter is read from the old exit core. -/
theorem zlab_snoc_last (c : Option C) (X : List Γ) (z : Γ) :
    zlab D ℓ c (X ++ [z]) (X.length + 1) = some (fcore D ℓ c X, z) := by
  rcases c with _ | c
  · simp [zlab, labFrom, fcore]
  · simp [zlab, labFrom, fcore]

/-- The terminal admissions of a block extended by one letter. -/
theorem blockΛf_snoc (c : Option C) (X : List Γ) (z : Γ) (L : Lab Γ C) :
    (∃ p ≤ (X ++ [z]).length, D.Λf (zlab D ℓ c (X ++ [z]) p) L) ↔
      (∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) L) ∨ D.Λf (some (fcore D ℓ c X, z)) L := by
  constructor
  · rintro ⟨p, hp, hΛ⟩
    rw [List.length_append, List.length_singleton] at hp
    rcases Nat.lt_or_ge X.length p with h | h
    · obtain rfl : p = X.length + 1 := by omega
      rw [zlab_snoc_last] at hΛ; exact Or.inr hΛ
    · rw [zlab_snoc_le D ℓ c X z h] at hΛ; exact Or.inl ⟨p, h, hΛ⟩
  · rintro (⟨p, hp, hΛ⟩ | hΛ)
    · exact ⟨p, by simp; omega, by rw [zlab_snoc_le D ℓ c X z hp]; exact hΛ⟩
    · exact ⟨X.length + 1, by simp, by rw [zlab_snoc_last]; exact hΛ⟩

/-- The terminal admissions of the empty block. -/
theorem blockΛf_nil (c : Option C) (L : Lab Γ C) :
    (∃ p ≤ ([] : List Γ).length, D.Λf (zlab D ℓ c [] p) L) ↔ D.Λf (lab0 ℓ c) L := by
  constructor
  · rintro ⟨p, hp, hΛ⟩
    obtain rfl : p = 0 := by simpa using hp
    rwa [zlab_zero] at hΛ
  · intro hΛ; exact ⟨0, le_rfl, by rwa [zlab_zero]⟩

/-- The ladder of two empty blocks. -/
theorem derΛ_nil_nil (c c' : Option C) :
    derΛ D ℓ (some (c, [])) (some (c', [])) ↔ D.Λ (lab0 ℓ c) (lab0 ℓ c') := by
  simp only [derΛ]
  constructor
  · rintro ⟨x, x', y, hx, hx', hΛ⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
    obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hx'.symm
    simpa [zlab_zero] using hΛ
  · intro hΛ; exact ⟨[], [], [], rfl, rfl, by simpa [zlab_zero] using hΛ⟩

/-- The ladder of an empty block and an extended block. -/
theorem derΛ_nil_snoc (c c' : Option C) (Y : List Γ) (z' : Γ) :
    derΛ D ℓ (some (c, [])) (some (c', Y ++ [z'])) ↔
      D.Λ (lab0 ℓ c) (some (fcore D ℓ c' Y, z')) := by
  simp only [derΛ]
  constructor
  · rintro ⟨x, x', y, hx, hx', hΛ⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
    rw [List.append_nil] at hx'
    subst hx'
    rwa [List.length_nil, zlab_zero, List.length_append, List.length_singleton,
      zlab_snoc_last] at hΛ
  · intro hΛ
    refine ⟨[], Y ++ [z'], [], rfl, (List.append_nil _).symm, ?_⟩
    rwa [List.length_nil, zlab_zero, List.length_append, List.length_singleton, zlab_snoc_last]

/-- The ladder of an extended block and an empty block. -/
theorem derΛ_snoc_nil (c c' : Option C) (X : List Γ) (z : Γ) :
    derΛ D ℓ (some (c, X ++ [z])) (some (c', [])) ↔
      D.Λ (some (fcore D ℓ c X, z)) (lab0 ℓ c') := by
  simp only [derΛ]
  constructor
  · rintro ⟨x, x', y, hx, hx', hΛ⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx'.symm
    rw [List.append_nil] at hx
    subst hx
    rwa [List.length_nil, zlab_zero, List.length_append, List.length_singleton,
      zlab_snoc_last] at hΛ
  · intro hΛ
    refine ⟨X ++ [z], [], [], (List.append_nil _).symm, rfl, ?_⟩
    rwa [List.length_nil, zlab_zero, List.length_append, List.length_singleton, zlab_snoc_last]

/-- The ladder of two extended blocks: a mismatch at the new letters, or equal new letters and the
ladder of the shorter blocks. -/
theorem derΛ_snoc_snoc (c c' : Option C) (X Y : List Γ) (z z' : Γ) :
    derΛ D ℓ (some (c, X ++ [z])) (some (c', Y ++ [z'])) ↔
      D.Λ (some (fcore D ℓ c X, z)) (some (fcore D ℓ c' Y, z')) ∨
        (z = z' ∧ derΛ D ℓ (some (c, X)) (some (c', Y))) := by
  simp only [derΛ]
  constructor
  · rintro ⟨x, x', y, hx, hy, hΛ⟩
    rcases List.eq_nil_or_concat y with rfl | ⟨y0, u, rfl⟩
    · rw [List.append_nil] at hx hy
      subst hx; subst hy
      left
      rwa [List.length_append, List.length_singleton, zlab_snoc_last,
        List.length_append, List.length_singleton, zlab_snoc_last] at hΛ
    · rw [List.concat_eq_append, ← List.append_assoc] at hx hy
      obtain ⟨hX, hz⟩ := List.append_inj' hx rfl
      obtain ⟨hY, hz'⟩ := List.append_inj' hy rfl
      simp only [List.cons.injEq, and_true] at hz hz'
      right
      refine ⟨hz.trans hz'.symm, x, x', y0, hX, hY, ?_⟩
      rwa [zlab_snoc_le D ℓ c X z (p := x.length) (by rw [hX]; simp),
        zlab_snoc_le D ℓ c' Y z' (p := x'.length) (by rw [hY]; simp)] at hΛ
  · rintro (hΛ | ⟨hzz, x, x', y, hX, hY, hΛ⟩)
    · refine ⟨X ++ [z], Y ++ [z'], [], (List.append_nil _).symm, (List.append_nil _).symm, ?_⟩
      rwa [List.length_append, List.length_singleton, zlab_snoc_last,
        List.length_append, List.length_singleton, zlab_snoc_last]
    · refine ⟨x, x', y ++ [z], by rw [hX, List.append_assoc], by
        rw [hY, List.append_assoc, hzz], ?_⟩
      rwa [zlab_snoc_le D ℓ c X z (p := x.length) (by rw [hX]; simp),
        zlab_snoc_le D ℓ c' Y z' (p := x'.length) (by rw [hY]; simp)]

/-- States of the column automaton for `k` tracks over cores `C`: the exits `fc(c, X_a)`, the
sets `B_a(c) ∋ d` (some label of the shifted block `Ẑ_a(c)` is `Λ^f`-related to `(d, ℓ)`),
the equality relation of the tracks, and the ladders `Λ'` for all pairs of tracks and start
cores. The components are `CS.exit`, `CS.terminalAdmission`, `CS.equalTracks` and
`CS.ladderAdmission`. -/
abbrev CS (C : Type*) (k : ℕ) :=
  (Fin k → Option C → C) × (Fin k → Option C → C → Prop) × (Fin k → Fin k → Prop) ×
    (Fin k → Fin k → Option C → Option C → Prop)

namespace CS
variable {k : ℕ}

/-- The exit core `fc(c, X_a)` of track `a` from start core `c`. -/
def exit (x : CS C k) : Fin k → Option C → C := x.1

/-- `x.terminalAdmission a c d`: some label of the shifted block `Ẑ_a(c)` is `Λ^f`-related to
the final label `(d, ℓ)`. -/
def terminalAdmission (x : CS C k) : Fin k → Option C → C → Prop := x.2.1

/-- `x.equalTracks a b`: tracks `a` and `b` carry the same block. -/
def equalTracks (x : CS C k) : Fin k → Fin k → Prop := x.2.2.1

/-- `x.ladderAdmission a b c c'`: the ladder `Λ'` relates block `a` from `c` and block `b`
from `c'`. -/
def ladderAdmission (x : CS C k) : Fin k → Fin k → Option C → Option C → Prop := x.2.2.2

variable (e : Fin k → Option C → C) (t : Fin k → Option C → C → Prop)
  (q : Fin k → Fin k → Prop) (l : Fin k → Fin k → Option C → Option C → Prop)

/-- The exits of a state given as a tuple. -/
@[simp] theorem exit_mk : exit ((e, t, q, l) : CS C k) = e := rfl

/-- The terminal admissions of a state given as a tuple. -/
@[simp] theorem terminalAdmission_mk : terminalAdmission ((e, t, q, l) : CS C k) = t := rfl

/-- The track equalities of a state given as a tuple. -/
@[simp] theorem equalTracks_mk : equalTracks ((e, t, q, l) : CS C k) = q := rfl

/-- The ladders of a state given as a tuple. -/
@[simp] theorem ladderAdmission_mk : ladderAdmission ((e, t, q, l) : CS C k) = l := rfl

end CS

variable (k : ℕ)

/-- The transition of the column automaton on a column (`none` = padding; columns are
right-aligned, so a padded track is still empty). -/
def colStep (x : CS C k) (col : Fin k → Option Γ) : CS C k :=
  (fun a c => match col a with
      | none => x.exit a c
      | some z => D.κ z (x.exit a c),
   fun a c d => match col a with
      | none => x.terminalAdmission a c d
      | some z => x.terminalAdmission a c d ∨ D.Λf (some (x.exit a c, z)) (some (d, ℓ)),
   fun a b => x.equalTracks a b ∧ col a = col b,
   fun a b c c' => match col a, col b with
      | none, none => x.ladderAdmission a b c c'
      | none, some z' => D.Λ (lab0 ℓ c) (some (x.exit b c', z'))
      | some z, none => D.Λ (some (x.exit a c, z)) (lab0 ℓ c')
      | some z, some z' =>
          D.Λ (some (x.exit a c, z)) (some (x.exit b c', z')) ∨
            (z = z' ∧ x.ladderAdmission a b c c'))

/-- The initial state (all tracks empty). -/
def colStart : CS C k :=
  (fun _ c => fcore D ℓ c [], fun _ c d => D.Λf (lab0 ℓ c) (some (d, ℓ)), fun _ _ => True,
    fun _ _ c c' => D.Λ (lab0 ℓ c) (lab0 ℓ c'))

/-- The finite reader that accumulates a summary of padded word columns. -/
def colDFA : DFA (Fin k → Option Γ) (CS C k) where
  step := colStep D ℓ k
  start := colStart D ℓ k
  accept := ∅

/-- The intended value of the column automaton on a tuple of level-`(j+1)` letters. -/
def summ (Ws : Fin k → List Γ) : CS C k :=
  (fun a c => fcore D ℓ c (Ws a),
   fun a c d => ∃ p ≤ (Ws a).length, D.Λf (zlab D ℓ c (Ws a) p) (some (d, ℓ)),
   fun a b => Ws a = Ws b,
   fun a b c c' => derΛ D ℓ (some (c, Ws a)) (some (c', Ws b)))

/-- On a valid column word, the column automaton computes the summary of the decoded tuple. -/
theorem colEval (w : List (Fin k → Option Γ)) (hw : Valid w) :
    (colDFA D ℓ k).eval w = summ D ℓ k (dec w) := by
  induction w using List.reverseRecOn with
  | nil =>
    have hd : ∀ a, dec ([] : List (Fin k → Option Γ)) a = [] := fun _ => rfl
    show colStart D ℓ k = summ D ℓ k (dec [])
    simp only [colStart, summ, hd]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext a c d; exact propext (blockΛf_nil D ℓ c _).symm
    · funext a b; simp
    · funext a b c c'; exact propext (derΛ_nil_nil D ℓ c c').symm
  | append_singleton w col ih =>
    rw [DFA.eval_append_singleton, ih (hw.sublist (List.sublist_append_left _ _))]
    have hpad : ∀ a, col a = none → dec w a = [] := dec_eq_nil_of_pad hw
    show colStep D ℓ k (summ D ℓ k (dec w)) col = summ D ℓ k (dec (w ++ [col]))
    simp only [colStep, summ, dec_snoc, CS.exit_mk, CS.terminalAdmission_mk, CS.equalTracks_mk,
      CS.ladderAdmission_mk]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext a c
      dsimp only
      rcases col a with _ | z
      · simp
      · simp [fcore_snoc]
    · funext a c d
      dsimp only
      rcases col a with _ | z
      · simp
      · simp only [Option.toList_some]
        exact propext (blockΛf_snoc D ℓ c _ z _).symm
    · funext a b
      dsimp only
      apply propext
      rcases hca : col a with _ | z <;> rcases hcb : col b with _ | z'
      · rw [hpad a hca, hpad b hcb]; simp
      · rw [hpad a hca]; simp
      · rw [hpad b hcb]; simp
      · simp only [Option.toList_some, Option.some.injEq]
        constructor
        · rintro ⟨h1, rfl⟩; rw [h1]
        · intro h
          obtain ⟨e1, e2⟩ := List.append_inj' h rfl
          simp only [List.cons.injEq, and_true] at e2
          exact ⟨e1, e2⟩
    · funext a b c c'
      dsimp only
      apply propext
      rcases hca : col a with _ | z <;> rcases hcb : col b with _ | z'
      · simp
      · rw [hpad a hca]
        simp only [Option.toList_none, Option.toList_some, List.append_nil]
        exact (derΛ_nil_snoc D ℓ c c' _ z').symm
      · rw [hpad b hcb]
        simp only [Option.toList_none, Option.toList_some, List.append_nil]
        exact (derΛ_snoc_nil D ℓ c c' _ z).symm
      · simp only [Option.toList_some]
        exact (derΛ_snoc_snoc D ℓ c c' _ _ z z').symm

/-- The column automaton has finitely many states. -/
instance instFintypeCS [Fintype C] [DecidableEq C] : Fintype (CS C k) :=
  @instFintypeProd _ _ inferInstance
    (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance inferInstance))

/-- The number of column-automaton states for `N` cores and `k` tracks. -/
def colBound (N k : ℕ) : ℕ :=
  (N ^ (N + 1)) ^ k * ((2 ^ N) ^ (N + 1)) ^ k * (2 ^ k) ^ k *
    (((2 ^ (N + 1)) ^ (N + 1)) ^ k) ^ k

/-- The column automaton has `colBound |C| k` states. -/
theorem card_CS [Fintype C] [DecidableEq C] :
    Fintype.card (CS C k) = colBound (Fintype.card C) k := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  simp [Fintype.card_option, colBound, mul_assoc]

/-- The summary determines the atomic type at level `j + 1`:
two `k`-tuples with the same column summary have the same equality pattern and the same
`κ'`, `Tf'`, `Λ'`, `Λ'^f` in `Der(D, ℓ)` (all start cores). -/
theorem der_type_of_summ {Ws Ws' : Fin k → List Γ} (hs : summ D ℓ k Ws' = summ D ℓ k Ws)
    (a b : Fin k) :
    (Ws' a = Ws' b ↔ Ws a = Ws b) ∧
    (∀ c, (der D ℓ).κ (Ws' a) c = (der D ℓ).κ (Ws a) c) ∧
    (∀ c, (der D ℓ).Tf c (Ws' a) ↔ (der D ℓ).Tf c (Ws a)) ∧
    (∀ c c', (der D ℓ).Λ (some (c, Ws' a)) (some (c', Ws' b)) ↔
      (der D ℓ).Λ (some (c, Ws a)) (some (c', Ws b))) ∧
    (∀ c c', (der D ℓ).Λf (some (c, Ws' a)) (some (c', Ws' b)) ↔
      (der D ℓ).Λf (some (c, Ws a)) (some (c', Ws b))) := by
  have h1 : ∀ a c, fcore D ℓ c (Ws' a) = fcore D ℓ c (Ws a) := fun a c =>
    congrFun (congrFun (congrArg CS.exit hs) a) c
  have h2 : ∀ a c d, (∃ p ≤ (Ws' a).length, D.Λf (zlab D ℓ c (Ws' a) p) (some (d, ℓ))) ↔
      ∃ p ≤ (Ws a).length, D.Λf (zlab D ℓ c (Ws a) p) (some (d, ℓ)) := fun a c d =>
    Iff.of_eq (congrFun (congrFun (congrFun (congrArg CS.terminalAdmission hs) a) c) d)
  have h3 : ∀ a b, Ws' a = Ws' b ↔ Ws a = Ws b := fun a b =>
    Iff.of_eq (congrFun (congrFun (congrArg CS.equalTracks hs) a) b)
  have h4 : ∀ a b c c', derΛ D ℓ (some (c, Ws' a)) (some (c', Ws' b)) ↔
      derΛ D ℓ (some (c, Ws a)) (some (c', Ws b)) := fun a b c c' =>
    Iff.of_eq (congrFun (congrFun (congrFun (congrFun
      (congrArg CS.ladderAdmission hs) a) b) c) c')
  refine ⟨h3 a b, fun c => ?_, fun c => ?_, fun c c' => h4 a b c c', fun c c' => ?_⟩
  · rw [der_κ, der_κ, h1]
  · simp only [der_Tf, derTf]
    rw [h1, h2]
  · simp only [der_Λf, derΛf]
    rw [h4, h1, h2]

/-- Short realizers of a summary. Every `k`-tuple of level-`(j+1)` letters has a tuple of
sub-words, each shorter than `colBound |C| k`, with the same column summary. -/
theorem exists_short_tuple [Fintype C] [DecidableEq C] (Ws : Fin k → List Γ) :
    ∃ Ws' : Fin k → List Γ, (∀ a, (Ws' a).Sublist (Ws a)) ∧
      (∀ a, (Ws' a).length < colBound (Fintype.card C) k) ∧ summ D ℓ k Ws' = summ D ℓ k Ws := by
  obtain ⟨Ws', h1, h2, h3⟩ := exists_short_conv (fun x => (colDFA D ℓ k).eval x)
    (fun x y a h => by simp only [DFA.eval_append_singleton]; rw [h]) Ws
  refine ⟨Ws', h1, fun a => (h2 a).trans_eq (card_CS k), ?_⟩
  have e1 := colEval D ℓ k _ (valid_conv Ws')
  have e2 := colEval D ℓ k _ (valid_conv Ws)
  rw [dec_conv] at e1 e2
  rw [← e1, ← e2]
  exact h3

/-- For every list `E` of at most `k`
level-`(j+1)` letters (words over the level-`j` alphabet) there is a map `ψ` sending each
`X ∈ E` to a sub-word of `X` of length `< colBound |C| k` and preserving the atomic type of `E`
in `Der(D, ℓ)`. -/
theorem exists_short_letters [Fintype C] [DecidableEq C] (E : List (List Γ))
    (hk : E.length ≤ k) :
    ∃ ψ : List Γ → List Γ, Agree (der D ℓ) (der D ℓ) ψ E ∧
      ∀ X ∈ E, (ψ X).Sublist X ∧ (ψ X).length < colBound (Fintype.card C) k := by
  classical
  set Ws : Fin k → List Γ := fun a => E.getD a.1 [] with hWs
  obtain ⟨Ws', hsub, hlen, hsumm⟩ := exists_short_tuple D ℓ k Ws
  have hT := der_type_of_summ D ℓ k hsumm
  have hidx : ∀ X ∈ E, E.idxOf X < k := fun X hX =>
    (List.idxOf_lt_length_of_mem hX).trans_le hk
  let idx : ∀ X ∈ E, Fin k := fun X hX => ⟨E.idxOf X, hidx X hX⟩
  have hWsidx : ∀ X (hX : X ∈ E), Ws (idx X hX) = X := fun X hX => by
    simp only [hWs, idx]
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hX), List.getElem_idxOf]
  let ψ : List Γ → List Γ := fun X => if hX : X ∈ E then Ws' (idx X hX) else X
  have hψ : ∀ X (hX : X ∈ E), ψ X = Ws' (idx X hX) := fun X hX => dite_eq_left hX
  refine ⟨ψ, ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, fun X hX => ?_⟩
  · intro X hX Y hY hXY
    rw [hψ X hX, hψ Y hY, (hT (idx X hX) (idx Y hY)).1, hWsidx X hX, hWsidx Y hY] at hXY
    exact hXY
  · intro X hX c
    rw [hψ X hX, (hT (idx X hX) (idx X hX)).2.1, hWsidx X hX]
  · intro X hX c
    rw [hψ X hX, (hT (idx X hX) (idx X hX)).2.2.1, hWsidx X hX]
  · intro L L' hL hL'
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · simp [derΛ]
    · simp [derΛ]
    · simp [derΛ]
    · simp only [mapLab_some]
      rw [hψ X hL, hψ Y hL', (hT (idx X hL) (idx Y hL')).2.2.2.1, hWsidx X hL, hWsidx Y hL']
  · intro L L' hL hL'
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · simp [derΛf]
    · simp [derΛf]
    · simp [derΛf]
    · simp only [mapLab_some]
      rw [hψ X hL, hψ Y hL', (hT (idx X hL) (idx Y hL')).2.2.2.2, hWsidx X hL, hWsidx Y hL']
  · rw [hψ X hX]
    refine ⟨?_, hlen _⟩
    have := hsub (idx X hX)
    rwa [hWsidx X hX] at this

end Column

end DeciNSSE.BoundedDepth
