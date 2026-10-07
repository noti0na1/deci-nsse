import DeciNSSE.Satisfiability.LeastGraph
import DeciNSSE.Satisfiability.Regular
import DeciNSSE.Transfer.Spines

/-! # Regular countermodel transfer

A regular solution of the finite spine extension, followed by regular median
symmetrisation and decoding, preserves an unsafe word. Regular entailment
therefore coincides with unrestricted entailment.
-/

namespace DeciNSSE

variable {n k : ℕ}

namespace RegularTransfer

open Safety Spine RegularVariance

/-- A left-unsafety block on `x, y` followed by a right-unsafety block on `ym, xm`. -/
def fourSpine (ψ : Constraint n k) (x y xm ym : V k) (w : List (Fin n)) :
    Constraint n ((k + (2 * w.length + 2)) + (2 * w.length + 2)) :=
  rUnsafe (lUnsafe ψ x y w) (Fin.castAdd _ ym) (Fin.castAdd _ xm) w

/-- Exact semantics of the composite: four prefix requirements on old variables. -/
theorem fourSpine_restrict_iff (ψ : Constraint n k) (x y xm ym : V k)
    (w : List (Fin n)) (ρ : V k → Tree n) :
    (∃ ρ'', (ρ'' ∘ Fin.castAdd _) ∘ Fin.castAdd _ = ρ ∧
        Covariant.Sat ρ'' (fourSpine ψ x y xm ym w)) ↔
      Covariant.Sat ρ ψ ∧ covPrefTop w (ρ x) ∧ ¬ covPrefTop w (ρ y) ∧
        ¬ covPrefBot w (ρ ym) ∧ covPrefBot w (ρ xm) := by
  constructor
  · rintro ⟨ρ'', hr, hs⟩
    obtain ⟨hl, hym, hxm⟩ :=
      (rUnsafe_restrict_iff _ _ _ w (ρ'' ∘ Fin.castAdd _)).mp ⟨ρ'', rfl, hs⟩
    obtain ⟨hψ, hx, hy⟩ := (lUnsafe_restrict_iff ψ x y w ρ).mp ⟨_, hr, hl⟩
    have e₁ : ρ'' (Fin.castAdd _ (Fin.castAdd _ ym)) = ρ ym := congrFun hr ym
    have e₂ : ρ'' (Fin.castAdd _ (Fin.castAdd _ xm)) = ρ xm := congrFun hr xm
    simp only [Function.comp_apply, e₁, e₂] at hym hxm
    exact ⟨hψ, hx, hy, hym, hxm⟩
  · rintro ⟨hψ, hx, hy, hym, hxm⟩
    obtain ⟨ρ', hr, hl⟩ := (lUnsafe_restrict_iff ψ x y w ρ).mpr ⟨hψ, hx, hy⟩
    have e₁ : ρ' (Fin.castAdd _ ym) = ρ ym := congrFun hr ym
    have e₂ : ρ' (Fin.castAdd _ xm) = ρ xm := congrFun hr xm
    obtain ⟨ρ'', hr', hs⟩ := (rUnsafe_restrict_iff _ _ _ w ρ').mpr
      ⟨hl, by rw [e₁]; exact hym, by rw [e₂]; exact hxm⟩
    exact ⟨ρ'', by rw [hr', hr], hs⟩

/-- A word cannot meet both a top and a bottom of the same tree. -/
theorem covPrefTop_not_covPrefBot {w : List (Fin n)} {t : Tree n}
    (h : covPrefTop w t) : ¬ covPrefBot w t := by
  intro hb
  have h₁ := (trace_eq_top_iff t w).mpr h
  have h₂ := (trace_eq_bot_iff t w).mpr hb
  rw [h₁] at h₂
  exact Tree.top_ne_bot h₂

/-- The least-solution graph of the four-spine extension, restricted to the old
variables (executable). -/
def spineGraph (ψ : Constraint n k) (x y xm ym : V k) (w : List (Fin n)) (u : V k) :
    RGraph n :=
  leastGraph (fourSpine ψ x y xm ym w) (Fin.castAdd _ (Fin.castAdd _ u))

/-- Four covariant prefix requirements met by some solution are met by the regular
`spineGraph`: the four-spine extension is satisfiable, so its least-solution graph
solves it, and the restriction keeps the requirements. -/
theorem regular_fourSpine {ψ : Constraint n k} {x y xm ym : V k} {w : List (Fin n)}
    {A : V k → Tree n} (hs : Covariant.Sat A ψ) (hx : covPrefTop w (A x))
    (hy : ¬ covPrefTop w (A y)) (hym : ¬ covPrefBot w (A ym))
    (hxm : covPrefBot w (A xm)) :
    Covariant.Sat (RGraph.unfold ∘ spineGraph ψ x y xm ym w) ψ ∧
      covPrefTop w (spineGraph ψ x y xm ym w x).unfold ∧
      ¬ covPrefTop w (spineGraph ψ x y xm ym w y).unfold ∧
      ¬ covPrefBot w (spineGraph ψ x y xm ym w ym).unfold ∧
      covPrefBot w (spineGraph ψ x y xm ym w xm).unfold := by
  obtain ⟨ρ'', -, hs''⟩ :=
    (fourSpine_restrict_iff ψ x y xm ym w A).mpr ⟨hs, hx, hy, hym, hxm⟩
  have hσ' := leastGraph_sat (satisfiable_iff_not_labelClash.mp ⟨ρ'', hs''⟩)
  exact (fourSpine_restrict_iff ψ x y xm ym w _).mp
    ⟨RGraph.unfold ∘ leastGraph (fourSpine ψ x y xm ym w), rfl, hσ'⟩

theorem unfold_decodeGraph_apply (c : Fin n → Bool) (τ : V (2 * k) → RGraph n)
    (u : V k) :
    (decodeGraph c τ u).unfold = Tree.normalize c false (Signed.symmetrize (RGraph.unfold ∘ τ) (sv u false)) :=
  congrFun (unfold_decodeGraph c τ) u

/-- The decoded graph meets a polarized top exactly when the positive block meets a top
and the negative block meets a bottom. -/
theorem prefTop_decodeGraph (c : Fin n → Bool) (τ : V (2 * k) → RGraph n) (u : V k)
    (w : List (Fin n)) :
    prefTop c w (decodeGraph c τ u).unfold ↔
      covPrefTop w (τ (sv u false)).unfold ∧ covPrefBot w (τ (sv u true)).unfold := by
  rw [unfold_decodeGraph_apply, prefTop_iff_normalize, normalize_involutive]
  exact symmetrize_prefTop (RGraph.unfold ∘ τ) u w

/-- The dual statement for polarized bottoms. -/
theorem prefBot_decodeGraph (c : Fin n → Bool) (τ : V (2 * k) → RGraph n) (u : V k)
    (w : List (Fin n)) :
    prefBot c w (decodeGraph c τ u).unfold ↔
      covPrefBot w (τ (sv u false)).unfold ∧ covPrefTop w (τ (sv u true)).unfold := by
  rw [unfold_decodeGraph_apply, prefBot_iff_normalize, normalize_involutive]
  exact symmetrize_prefBot (RGraph.unfold ∘ τ) u w

/-- The explicit regular left witness at `w`: decode the restricted least-solution graph
of the extension requiring `⊤` on `x⁺`, `⊥` on `x⁻` and no `⊤` on `y⁺`. -/
def lCountermodel (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (w : List (Fin n)) : V k → RGraph n :=
  decodeGraph c (spineGraph (signed c ϕ) (sv x false) (sv y false) (sv x true)
    (sv x false) w)

/-- The explicit regular right witness at `w`: decode the restricted least-solution graph
of the extension requiring `⊥` on `y⁺`, `⊤` on `y⁻` and no `⊥` on `x⁺`. -/
def rCountermodel (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (w : List (Fin n)) : V k → RGraph n :=
  decodeGraph c (spineGraph (signed c ϕ) (sv y true) (sv y false) (sv y false)
    (sv x false) w)

/-- A left-unsafe solution at `w` makes `lCountermodel` a regular left-unsafe solution
at the same `w`. -/
theorem lCountermodel_spec (c : Fin n → Bool) {ϕ : Constraint n k} {x y : V k}
    {w : List (Fin n)}
    (h : ∃ ρ, Sat c ρ ϕ ∧ prefTop c w (ρ x) ∧ ¬ prefTop c w (ρ y)) :
    Sat c (RGraph.unfold ∘ lCountermodel c ϕ x y w) ϕ ∧
      prefTop c w (lCountermodel c ϕ x y w x).unfold ∧
      ¬ prefTop c w (lCountermodel c ϕ x y w y).unfold := by
  obtain ⟨ρ, hρ, hx, hy⟩ := h
  rw [prefTop_iff_normalize] at hx hy
  have hx₁ : covPrefTop w (normalized c ρ (sv x false)) := by rwa [normalized_sv]
  obtain ⟨hτ, hx', hy', -, hq'⟩ := regular_fourSpine (x := sv x false)
    (y := sv y false) (xm := sv x true) (ym := sv x false) ((sat_iff_signed c ρ ϕ).mp hρ) hx₁
    (by rwa [normalized_sv]) (covPrefTop_not_covPrefBot hx₁)
    (by rwa [normalized_sv, normalize_true, covPrefBot_dual])
  exact ⟨sat_decodeGraph c hτ, (prefTop_decodeGraph c _ x w).mpr ⟨hx', hq'⟩,
    fun h => hy' ((prefTop_decodeGraph c _ y w).mp h).1⟩

/-- A right-unsafe solution at `w` makes `rCountermodel` a regular right-unsafe solution
at the same `w`. -/
theorem rCountermodel_spec (c : Fin n → Bool) {ϕ : Constraint n k} {x y : V k}
    {w : List (Fin n)}
    (h : ∃ ρ, Sat c ρ ϕ ∧ prefBot c w (ρ y) ∧ ¬ prefBot c w (ρ x)) :
    Sat c (RGraph.unfold ∘ rCountermodel c ϕ x y w) ϕ ∧
      prefBot c w (rCountermodel c ϕ x y w y).unfold ∧
      ¬ prefBot c w (rCountermodel c ϕ x y w x).unfold := by
  obtain ⟨ρ, hρ, hy, hx⟩ := h
  rw [prefBot_iff_normalize] at hx hy
  have hy₁ : covPrefBot w (normalized c ρ (sv y false)) := by rwa [normalized_sv]
  obtain ⟨hτ, hq', -, hx', hy'⟩ := regular_fourSpine (x := sv y true)
    (y := sv y false) (xm := sv y false) (ym := sv x false) ((sat_iff_signed c ρ ϕ).mp hρ)
    (by rwa [normalized_sv, normalize_true, covPrefTop_dual])
    (fun h' => covPrefTop_not_covPrefBot h' hy₁) (by rwa [normalized_sv]) hy₁
  exact ⟨sat_decodeGraph c hτ, (prefBot_decodeGraph c _ y w).mpr ⟨hy', hq'⟩,
    fun h => hx' ((prefBot_decodeGraph c _ x w).mp h).1⟩

end RegularTransfer

open RegularTransfer RegularVariance

/-- The countermodel can be taken from the explicit executable family `lCountermodel` /
`rCountermodel`, indexed by the unsafe word. -/
theorem explicit_countermodel (c : Fin n → Bool) {ϕ : Constraint n k} {x y : V k}
    (hn : ¬ Entails c ϕ x y) :
    ∃ w : List (Fin n),
      (Sat c (RGraph.unfold ∘ lCountermodel c ϕ x y w) ϕ ∧
        ¬ Tree.Le c (lCountermodel c ϕ x y w x).unfold (lCountermodel c ϕ x y w y).unfold) ∨
      (Sat c (RGraph.unfold ∘ rCountermodel c ϕ x y w) ϕ ∧
        ¬ Tree.Le c (rCountermodel c ϕ x y w x).unfold (rCountermodel c ϕ x y w y).unfold) := by
  classical
  by_contra hno
  apply hn
  rw [entails_iff_safe]
  intro w ρ hs
  refine ⟨fun hx => ?_, fun hy => ?_⟩
  · by_contra hy
    obtain ⟨hσ, hx', hy'⟩ := lCountermodel_spec c ⟨ρ, hs, hx, hy⟩
    exact hno ⟨w, Or.inl ⟨hσ, fun hle => hy' (((treeLe_iff_safe c _ _).mp hle w).1 hx')⟩⟩
  · by_contra hx
    obtain ⟨hσ, hy', hx'⟩ := rCountermodel_spec c ⟨ρ, hs, hy, hx⟩
    exact hno ⟨w, Or.inr ⟨hσ, fun hle => hx' (((treeLe_iff_safe c _ _).mp hle w).2 hy')⟩⟩

/-- Every non-entailment, at any arity and variance, has a regular countermodel. -/
theorem regular_countermodel (c : Fin n → Bool) {ϕ : Constraint n k} {x y : V k}
    (hn : ¬ Entails c ϕ x y) :
    ∃ σ : V k → RGraph n, Sat c (RGraph.unfold ∘ σ) ϕ ∧
      ¬ Tree.Le c (σ x).unfold (σ y).unfold := by
  obtain ⟨w, h | h⟩ := explicit_countermodel c hn
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

/-- Regular entailment equals entailment over all trees, for any arity and variance. -/
theorem entailsReg_iff_entails (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    EntailsReg c ϕ x y ↔ Entails c ϕ x y := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨σ, hσ, hle⟩ := regular_countermodel c hn
    exact hle (h σ hσ)
  · intro h σ hσ
    exact h _ hσ

end DeciNSSE
