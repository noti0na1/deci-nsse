import DeciNSSE.Complexity.HardnessAutomaton

/-! # The constraint system of the hardness reduction

From a binary automaton `M` with states `Fin m`, the system `hardnessSystem n M`
over one covariant constructor of arity `n` reads codes of words along the
first two directions. Its automaton `N` accepts the codes of the words of `M`:
each transition `p →a q` of `M` becomes `p →0 t →a q` through a middle state `t`,
and each final state of `M` reads the closing `1` into a final state of `N`.
The variables are

- `x` and `r`, the queried pair, and `r'`, the partner of `r`;
- `d`, an unconstrained filler, and `b`, equal to bottom;
- `z`, the middle of the sandwich `f(x, b, …) ≤ z ≤ f(X_p, b, …)` that expresses
  `x ≤ X_p` for every initial state `p`, since flat literals have no
  variable-to-variable inequality;
- `X_p` for each state `p` of `M` and `Y_t` for each transition `t`, the middle
  states of `N`. The final state of `N` would equal bottom, so `b` stands for it.

So there are `m + T + 6` variables for `T` transitions, five more than the
`m + T + 1` states of `N`, and at most `2 m + 2 T + 4` literals.

## Main declarations
- `hardnessSystem`, with the variables `Hardness.xVar` and `Hardness.rVar`
- `hardnessSystem_length_le`, the size bound
- `covSat_hardnessSystem_iff`, the solutions literal by literal
-/

namespace DeciNSSE.Complexity

namespace Hardness

variable {n m : ℕ} (M : BinNFA m)

/-- Six auxiliary variables, one variable per state and one per transition. -/
abbrev numVars : ℕ := 6 + m + M.trans.length

/-- The auxiliary variable with the given index. -/
def auxVar (i : Fin 6) : V (numVars M) := Fin.castAdd _ (Fin.castAdd m i)

/-- The left side `x` of the query. -/
def xVar : V (numVars M) := auxVar M 0
/-- The filler `d`. -/
def dVar : V (numVars M) := auxVar M 1
/-- The variable `b`, equal to bottom. -/
def bVar : V (numVars M) := auxVar M 2
/-- The right side `r` of the query. -/
def rVar : V (numVars M) := auxVar M 3
/-- The partner `r'` of `r`. -/
def rVar' : V (numVars M) := auxVar M 4
/-- The middle `z` of the sandwich below the initial states. -/
def zVar : V (numVars M) := auxVar M 5
/-- The variable `X_p` of a state. -/
def stateVar (p : Fin m) : V (numVars M) := Fin.castAdd _ (Fin.natAdd 6 p)
/-- The variable `Y_t` of the middle state of a transition. -/
def transVar (j : Fin M.trans.length) : V (numVars M) := Fin.natAdd (6 + m) j

/-- The children `(u, v, w, …, w)` of a constructor: variables in a flat literal, or
their values. -/
def kids {α : Type*} (u v w : α) : Fin n → α :=
  fun i => if i.val = 0 then u else if i.val = 1 then v else w

theorem comp_kids {α β : Type*} (g : α → β) (u v w : α) :
    g ∘ (kids u v w : Fin n → α) = kids (g u) (g v) (g w) := by
  funext i
  simp only [Function.comp_apply, kids]
  split_ifs <;> rfl

@[simp] theorem kids_dir_zero (hn : 2 ≤ n) {α : Type*} (u v w : α) :
    kids u v w (dir hn 0) = u := by simp [kids, dir]

@[simp] theorem kids_dir_one (hn : 2 ≤ n) {α : Type*} (u v w : α) :
    kids u v w (dir hn 1) = v := by simp [kids, dir]

/-- The children read by the middle state of a transition: its target in the
direction of its letter, the filler in the other binary direction, and `b` elsewhere. -/
def readKids (j : Fin M.trans.length) : Fin n → V (numVars M) :=
  fun i => if i.val = M.trans[j].2.1.val then stateVar M M.trans[j].2.2
    else if i.val < 2 then dVar M else bVar M

/-- A valuation from its auxiliary, state and transition values. -/
def valuation {α : Type*} (aux : Fin 6 → α) (X : Fin m → α) (Y : Fin M.trans.length → α) :
    V (numVars M) → α :=
  Fin.append (Fin.append aux X) Y

section Valuation
variable {α : Type*} (aux : Fin 6 → α) (X : Fin m → α) (Y : Fin M.trans.length → α)

@[simp] theorem valuation_auxVar (i : Fin 6) : valuation M aux X Y (auxVar M i) = aux i := by
  simp [valuation, auxVar]

@[simp] theorem valuation_stateVar (p : Fin m) :
    valuation M aux X Y (stateVar M p) = X p := by
  simp [valuation, stateVar]

@[simp] theorem valuation_transVar (j : Fin M.trans.length) :
    valuation M aux X Y (transVar M j) = Y j := by
  simp [valuation, transVar]

end Valuation

end Hardness

open Hardness

/-- The system `χ(M)` whose entailment `x ≤ r` holds exactly when `M` is universal. -/
def hardnessSystem (n : ℕ) {m : ℕ} (M : BinNFA m) : Constraint n (numVars M) :=
  [.eqBot (bVar M), .fLe (kids (rVar' M) (bVar M) (bVar M)) (rVar M),
    .fLe (kids (rVar M) (rVar M) (bVar M)) (rVar' M),
    .fLe (kids (xVar M) (bVar M) (bVar M)) (zVar M)] ++
  ((List.finRange m).filter M.init).map
    (fun p => .leF (zVar M) (kids (stateVar M p) (bVar M) (bVar M))) ++
  ((List.finRange m).filter M.final).map
    (fun p => .leF (stateVar M p) (kids (dVar M) (bVar M) (bVar M))) ++
  (List.finRange M.trans.length).map
    (fun j => .leF (stateVar M M.trans[j].1) (kids (transVar M j) (dVar M) (bVar M))) ++
  (List.finRange M.trans.length).map (fun j => .leF (transVar M j) (readKids M j))

/-- The variables are the `m + T + 1` states of the code automaton and five more. -/
theorem numVars_eq {m : ℕ} (M : BinNFA m) : numVars M = (m + M.trans.length + 1) + 5 := by
  unfold numVars; omega

/-- The system has at most `2 m + 2 T + 4` literals for `m` states and `T` transitions. -/
theorem hardnessSystem_length_le (n : ℕ) {m : ℕ} (M : BinNFA m) :
    (hardnessSystem n M).length ≤ 2 * m + 2 * M.trans.length + 4 := by
  have hi := List.length_filter_le M.init (List.finRange m)
  have hf := List.length_filter_le M.final (List.finRange m)
  simp only [List.length_finRange] at hi hf
  simp only [hardnessSystem, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_finRange]
  omega

/-- The solutions of the system, literal by literal. -/
theorem covSat_hardnessSystem_iff {n m : ℕ} (M : BinNFA m) (ρ : V (numVars M) → Tree n) :
    Covariant.Sat ρ (hardnessSystem n M) ↔
      ρ (bVar M) = Tree.bot ∧
      Tree.node (ρ ∘ kids (rVar' M) (bVar M) (bVar M)) ≤ ρ (rVar M) ∧
      Tree.node (ρ ∘ kids (rVar M) (rVar M) (bVar M)) ≤ ρ (rVar' M) ∧
      Tree.node (ρ ∘ kids (xVar M) (bVar M) (bVar M)) ≤ ρ (zVar M) ∧
      (∀ p, M.init p = true →
        ρ (zVar M) ≤ Tree.node (ρ ∘ kids (stateVar M p) (bVar M) (bVar M))) ∧
      (∀ p, M.final p = true →
        ρ (stateVar M p) ≤ Tree.node (ρ ∘ kids (dVar M) (bVar M) (bVar M))) ∧
      (∀ j, ρ (stateVar M M.trans[j].1) ≤
        Tree.node (ρ ∘ kids (transVar M j) (dVar M) (bVar M))) ∧
      (∀ j, ρ (transVar M j) ≤ Tree.node (ρ ∘ readKids M j)) := by
  simp only [Covariant.Sat, hardnessSystem, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_filter, List.mem_finRange, true_and, List.not_mem_nil, or_false]
  constructor
  · intro h
    exact ⟨h (.eqBot _) (.inl (.inl (.inl (.inl (.inl rfl))))),
      h (.fLe _ _) (.inl (.inl (.inl (.inl (.inr (.inl rfl)))))),
      h (.fLe _ _) (.inl (.inl (.inl (.inl (.inr (.inr (.inl rfl))))))),
      h (.fLe _ _) (.inl (.inl (.inl (.inl (.inr (.inr (.inr rfl))))))),
      fun p hp => h (.leF _ _) (.inl (.inl (.inl (.inr ⟨p, hp, rfl⟩)))),
      fun p hp => h (.leF _ _) (.inl (.inl (.inr ⟨p, hp, rfl⟩))),
      fun j => h (.leF _ _) (.inl (.inr ⟨j, rfl⟩)), fun j => h (.leF _ _) (.inr ⟨j, rfl⟩)⟩
  · rintro ⟨hb, hr, hr', hz, hinit, hfinal, henter, hread⟩ l hl
    rcases hl with ((((((rfl | rfl | rfl | rfl) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) |
      ⟨j, rfl⟩) | ⟨j, rfl⟩))
    · exact hb
    · exact hr
    · exact hr'
    · exact hz
    · exact hinit p hp
    · exact hfinal p hp
    · exact henter j
    · exact hread j

end DeciNSSE.Complexity
