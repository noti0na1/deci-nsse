import DeciNSSE.Complexity.Tiling.EmitterHoles
import DeciNSSE.Complexity.Tiling.Doubled
import DeciNSSE.Complexity.Tiling.Reader
import DeciNSSE.Complexity.Directions
import DeciNSSE.Monitor.Decision
import DeciNSSE.Shortening.Readers

/-! # Reduction of exponential tiling to non-entailment

The source is the tiling of an open square of side `2 ^ p` with a succinct boundary
(`Square.Valid`). Tobies, Corollary 5.14, gives a fixed domino system for which tiling
the torus of side `2 ^ (w.length + 1)` with initial word `w` is NEXPTIME-hard.
`Tiling.bridge_iff` reduces this torus problem to the open square.

A tiling gives non-entailment over arbitrary, regular and finite trees in the signature
with bottom and top. Lean proves reduction correctness and bounds its output size
in `torusSystem_size`. The torus hardness theorem is cited, and the polynomial running
time of the reduction is not formalized.

## Main declarations

- `emit_correct` characterizes the query emitted from a covariant stopping table.
- `lifted`, `lifted_holes` use doubled letters before the variance lift.
- `tilingSystem`, `tilingSystem_correct`, `tilingSystem_size` give the
  reduction and its polynomial bounds.
- `torusSystem_correct`, `torusSystem_size` compose the reduction with the torus bridge.
-/

namespace DeciNSSE.Complexity.Tiling
open Monitor
variable {n t : ℕ} {D : Type*}

/-- Reaching a table target precludes reaching any target after a nonempty continuation. -/
theorem StoppingTable.stopping {α : Type*} (M : StoppingTable α) :
    Shortening.Stopping M.dfa (↑M.target : Set (Fin M.size)) := by
  have sink (w : List α) : M.dfa.evalFrom M.sink w = M.sink := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa [DFA.evalFrom_cons, StoppingTable.dfa, M.absorb] using ih
  intro q hq w hw
  cases w with
  | nil => contradiction
  | cons a w =>
    change M.dfa.evalFrom (M.step q a) w ∉ M.target
    rw [M.stop q hq, sink]; exact M.sink_clear

/-- At every positive arity the covariant emitted system has a finite solution, its left holes
are exactly the table holes, and its right side has no hole. Entailment in each tree domain is
equivalent to absence of a table hole. -/
theorem emit_correct (hn : 0 < n) (M : StoppingTable (Fin n)) :
    let Z := emit M
    let c : Fin n → Bool := fun _ => false
    SatisfiableFin c Z.system ∧
    (∀ w, SideHole c Z.system Z.x Z.y .l w ↔ M.Hole w) ∧
    (∀ w, ¬ SideHole c Z.system Z.x Z.y .r w) ∧
    (Entails c Z.system Z.x Z.y ↔ ¬ ∃ w, M.Hole w) ∧
    (EntailsReg c Z.system Z.x Z.y ↔ ¬ ∃ w, M.Hole w) ∧
    (EntailsFin c Z.system Z.x Z.y ↔ ¬ ∃ w, M.Hole w) := by
  let c : Fin n → Bool := fun _ => false
  let Z := emit M
  have sat := (Emitter.polarized M).finite c
  have sep := (Emitter.separated M).signed c
  have left (w) : SideHole c Z.system Z.x Z.y .l w ↔ M.Hole w := by
    apply (Emitter.left_hole M hn (singleTrack _ false) sep w).trans
    simp only [StoppingTable.Hole, Holes.isReaderHole_iff, Finset.mem_coe, CoAlignment.IsComp,
      singleTrack, forall_true_left, and_imp]
  have right (w) : ¬ SideHole c Z.system Z.x Z.y .r w :=
    Emitter.right_clear M hn (singleTrack _ true) sep w
  have hs : Satisfiable c Z.system := by
    obtain ⟨σ,h⟩ := sat; exact ⟨FTree.toTree ∘ σ,h⟩
  have he : Entails c Z.system Z.x Z.y ↔ ¬ ∃ w, M.Hole w := by
    rw [entails_iff_no_holes ((satB_iff ..).mpr hs)]
    simp [left,right]
  exact ⟨sat,left,right,he,(entailsReg_iff_entails ..).trans he,
    (entailsFin_iff c Z.system Z.x Z.y).trans
      ⟨fun h => h.elim (fun h => (h sat).elim) he.mp, fun h => Or.inr (he.mpr h)⟩⟩

/-- Encode a binary word by repeating each bit twice in the first two constructor directions. -/
def doubleWord (hn : 2 ≤ n) (u : List (Fin 2)) :=
  u.flatMap fun b => [Directions.embedDir hn b, Directions.embedDir hn b]

/-- Compile a binary table to read doubled directions, remembering the first bit until its
matching direction is read. -/
def doubleTable (_hn : 2 ≤ n) (M : StoppingTable (Fin 2)) : StoppingTable (Fin n) :=
  M.decode 3 fun phase a =>
    if h : a.val < 2 then
      if phase = 0 then some (.inl (a.val + 1))
      else if phase = a.val + 1 then some (.inr ⟨a.val, h⟩) else none
    else none

/-- Pairing each state with the three doubled-letter phases requires at most `3 * M.size + 1`
states including the sink. -/
theorem doubleTable_size (hn : 2 ≤ n) (M : StoppingTable (Fin 2)) :
    (doubleTable hn M).size ≤ 3 * M.size + 1 := by
  unfold doubleTable
  rw [StoppingTable.decode_size _ _ (by decide), Nat.mul_comm]

/-- The doubled table's holes are exactly the doubled encodings of binary table holes. -/
theorem doubleTable_hole_iff (hn : 2 ≤ n) (M : StoppingTable (Fin 2)) (w) :
    (doubleTable hn M).Hole w ↔ ∃ u, M.Hole u ∧ w = doubleWord hn u :=
  (doubledCode hn).hole_iff M w

/-- Emit the doubled-letter table and take two signed copies of its variables to implement the
specified variance. -/
def lifted (hn : 2 ≤ n) (c : Fin n → Bool) (M : StoppingTable (Fin 2)) : Query n :=
  let Z := emit (doubleTable hn M)
  ⟨2 * Z.vars, signed c Z.system, sv Z.x false, sv Z.y false⟩

/-- The variance lift has a finite solution, its left holes are the doubled binary holes, and
its right side has no holes. -/
theorem lifted_holes (hn : 2 ≤ n) (c : Fin n → Bool) (M : StoppingTable (Fin 2)) :
    let Z := lifted hn c M
    SatisfiableFin c Z.system ∧
    (∀ w, SideHole c Z.system Z.x Z.y .l w ↔ ∃ u, M.Hole u ∧ w = doubleWord hn u) ∧
    ∀ w, ¬ SideHole c Z.system Z.x Z.y .r w := by
  let B := doubleTable hn M
  let Z := lifted hn c M
  have sep := ((Emitter.separated B).signed c).signed c
  have zero (u : List (Fin 2)) : polarity c (doubleWord hn u) = false := by
    induction u with
    | nil => rfl
    | cons a u ih =>
      change (c (Directions.embedDir hn a) ^^
        (c (Directions.embedDir hn a) ^^ polarity c (doubleWord hn u))) = false
      rw [ih]; cases c (Directions.embedDir hn a) <;> rfl
  have even (a b : List (Fin n)) (h : (B.dfa.eval a,B.dfa.eval b) ∈ B.pairs) :
      polarity c a = polarity c b := by
    obtain ⟨u,v,hu,hv⟩ := (doubledCode hn).pair_boundaries M a b h
    change a = doubleWord hn u at hu
    change b = doubleWord hn v at hv
    rw [hu,hv,zero,zero]
  refine ⟨((Emitter.polarized B).signed c).finite c, ?_,
    Emitter.right_clear B (by omega) (doubleTrack _ c true) sep⟩
  intro w
  apply (Emitter.left_hole B (by omega) (doubleTrack _ c false) sep w).trans
  apply Iff.trans _ (doubleTable_hole_iff hn M w)
  rw [StoppingTable.Hole, Holes.isReaderHole_iff]
  apply and_congr_right
  intro _
  constructor
  · exact fun h s e hs he hp hr => h s e ⟨hs,he,hp⟩ (even _ _ hr) hr
  · exact fun h s e hc _ => h s e hc.1 hc.2.1 hc.2.2

/-- Compile a boundary-constrained square into a flat system and query at the given arity and
variance. -/
def tilingSystem [DecidableEq D] (hn : 2 ≤ n) (c : Fin n → Bool)
    (I : Square D) (e : D ≃ Fin t) :=
  lifted hn c (tilingReader I e)

/-- The emitted system has a finite solution and entails its query over arbitrary, regular and
finite trees exactly when the square has no valid tiling. -/
theorem tilingSystem_correct [DecidableEq D] (hn : 2 ≤ n) (c : Fin n → Bool) (I : Square D)
    (e : D ≃ Fin t) :
    let Z := tilingSystem hn c I e
    SatisfiableFin c Z.system ∧
    (Entails c Z.system Z.x Z.y ↔ ¬ ∃ g, I.Valid g) ∧
    (EntailsReg c Z.system Z.x Z.y ↔ ¬ ∃ g, I.Valid g) ∧
    (EntailsFin c Z.system Z.x Z.y ↔ ¬ ∃ g, I.Valid g) := by
  let Z := tilingSystem hn c I e
  obtain ⟨hf, hl, hr⟩ := lifted_holes hn c (tilingReader I e)
  have sat : Satisfiable c Z.system := by
    obtain ⟨σ, hσ⟩ := hf
    exact ⟨FTree.toTree ∘ σ, hσ⟩
  have left : (∃ w, SideHole c Z.system Z.x Z.y .l w) ↔ ∃ g, I.Valid g := by
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨u, hu, _⟩ := (hl w).mp hw
      obtain ⟨g, hg, _⟩ := (tilingReader_hole_iff I e u).mp hu
      exact ⟨g, hg⟩
    · rintro ⟨g, hg⟩
      have hb := (tilingReader_hole_iff I e _).mpr ⟨g, hg, rfl⟩
      exact ⟨_, (hl _).mpr ⟨_, hb, rfl⟩⟩
  have right : ¬ ∃ w, SideHole c Z.system Z.x Z.y .r w := fun ⟨w, hw⟩ => hr w hw
  have he : Entails c Z.system Z.x Z.y ↔ ¬ ∃ g, I.Valid g := by
    rw [entails_iff_no_holes ((satB_iff c Z.system).mpr sat), left]
    simp [right]
  exact ⟨hf, he, (entailsReg_iff_entails ..).trans he,
    (entailsFin_iff c Z.system Z.x Z.y).trans ⟨
      fun h => h.elim (fun hn => (hn hf).elim) he.mp, fun h => Or.inr (he.mpr h)⟩⟩

/-- For the binary state allowance `m`, the emitted system uses at most `18*m+8` variables and
`128*(n+1)*(m+1)^2` literals. -/
theorem tilingSystem_size [DecidableEq D] (hn : 2 ≤ n) (c : Fin n → Bool) (I : Square D)
    (e : D ≃ Fin t) :
    let Z := tilingSystem hn c I e
    let m := stateBound I.p t I.initial.length
    Z.vars ≤ 18 * m + 8 ∧ Z.system.length ≤ 128 * (n + 1) * (m + 1) ^ 2 := by
  let m := stateBound I.p t I.initial.length
  let B := doubleTable hn (tilingReader I e)
  have hb : B.size ≤ 3 * m + 1 := (doubleTable_size ..).trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (tilingReader_size I e)) 1)
  obtain ⟨hv, hl⟩ := emit_size B
  change 2 * (emit B).vars ≤ _ ∧ (signed c (emit B).system).length ≤ _
  refine ⟨by rw [hv]; omega, ?_⟩
  apply (flatMap_length_le _ (signedLit c) 2 (fun a _ => by cases a <;> rfl)).trans
  calc
    _ ≤ ((3 * m + 1) * (1 + n * (3 * m + 1 + 3)) + 1) * 2 := by
      gcongr; exact hl.trans (by gcongr)
    _ ≤ 128 * (n + 1) * (m + 1) ^ 2 := by ring_nf; omega

/-- Number the three tile coordinates explicitly. -/
def tripleNumber (e : D ≃ Fin t) : (D × D × D) ≃ Fin (t * (t * t)) :=
  (e.prodCongr ((e.prodCongr e).trans finProdFinEquiv)).trans finProdFinEquiv

/-- Apply the triple-tile bridge at unary exponent `p` and compile the resulting square to an
entailment query. Correctness requires the initial word to fit the side, `w.length ≤ 2 ^ p`. -/
def torusSystem [Fintype D] [DecidableEq D] (hn : 2 ≤ n) (c : Fin n → Bool) (A : Domino D)
    (p : ℕ) (w : List D) (e : D ≃ Fin t) :=
  tilingSystem hn c (bridge A p w) (tripleNumber e)

/-- For a fitting initial word the emitted torus system has a finite solution, and its query
holds in each tree domain exactly when no torus tiling satisfies that word. -/
theorem torusSystem_correct [Fintype D] [DecidableEq D] (hn : 2 ≤ n) (c : Fin n → Bool)
    (A : Domino D) (p : ℕ) (w : List D) (hw : w.length ≤ 2 ^ p) (e : D ≃ Fin t) :
    let Z := torusSystem hn c A p w e
    let solution := ∃ g, TorusTiling A (2 ^ p) (2 ^ p) w g
    SatisfiableFin c Z.system ∧ (Entails c Z.system Z.x Z.y ↔ ¬ solution) ∧
      (EntailsReg c Z.system Z.x Z.y ↔ ¬ solution) ∧
      (EntailsFin c Z.system Z.x Z.y ↔ ¬ solution) := by
  dsimp only
  rw [bridge_iff A p w hw]
  exact tilingSystem_correct hn c (bridge A p w) (tripleNumber e)

/-- The variable and literal bounds for a torus use the cubic tile alphabet of the bridge and
the length of the initial word. -/
theorem torusSystem_size [Fintype D] [DecidableEq D] (hn : 2 ≤ n) (c : Fin n → Bool)
    (A : Domino D) (p : ℕ) (w : List D) (e : D ≃ Fin t) :
    let Z := torusSystem hn c A p w e
    let m := stateBound p (t * (t * t)) w.length
    Z.vars ≤ 18 * m + 8 ∧ Z.system.length ≤ 128 * (n + 1) * (m + 1) ^ 2 := by
  simpa only [torusSystem, bridge, List.length_map] using
    tilingSystem_size hn c (bridge A p w) (tripleNumber e)

/-- At side `2 ^ (w.length + 1)` the emitted system has a finite solution and entails its query
in each domain exactly when the torus has no tiling with initial word `w`. -/
theorem initialWordSystem_correct [Fintype D] [DecidableEq D] (hn : 2 ≤ n) (c : Fin n → Bool)
    (A : Domino D) (w : List D) (e : D ≃ Fin t) :
    let p := w.length + 1
    let Z := torusSystem hn c A p w e
    let solution := ∃ g, TorusTiling A (2 ^ p) (2 ^ p) w g
    SatisfiableFin c Z.system ∧ (Entails c Z.system Z.x Z.y ↔ ¬ solution) ∧
      (EntailsReg c Z.system Z.x Z.y ↔ ¬ solution) ∧
      (EntailsFin c Z.system Z.x Z.y ↔ ¬ solution) :=
  torusSystem_correct hn c A _ w (Nat.le_of_lt ((Nat.lt_succ_self _).trans Nat.lt_two_pow_self)) e

/-- The polynomial output bounds apply to the initial-word family with exponent `w.length + 1`
and the bridge's cubic tile alphabet. -/
theorem initialWordSystem_size [Fintype D] [DecidableEq D] (hn : 2 ≤ n) (c : Fin n → Bool)
    (A : Domino D) (w : List D) (e : D ≃ Fin t) :
    let p := w.length + 1
    let Z := torusSystem hn c A p w e
    let m := stateBound p (t * (t * t)) w.length
    Z.vars ≤ 18 * m + 8 ∧ Z.system.length ≤ 128 * (n + 1) * (m + 1) ^ 2 :=
  torusSystem_size hn c A _ w e

end DeciNSSE.Complexity.Tiling
