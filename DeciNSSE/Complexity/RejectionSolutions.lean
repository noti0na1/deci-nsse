import DeciNSSE.Complexity.RejectionSystem
import DeciNSSE.Transfer.Safety
import DeciNSSE.Words

/-! # Unsafe words of the rejection system

Let `A` be a binary automaton and `ρ` a solution of `rejectionSystem n A`, for
`n ≥ 2` and the covariant constructor.

- `x` and `g` lie below `f(g, g, ⊥, …)`, so `x` is top at no path and bottom
  along every path that leaves the binary directions (`trace_confined`). So no
  word is left unsafe.
- Along a run of `A` from `q` on `u`, the tree of `Y_q` is not bottom at `u`, and
  along every word accepted by `A`, the tree of `y` is not bottom.

So every unsafe word is right unsafe and is the image of a binary word that `A`
rejects (`exists_of_unsafe`). If `A` accepts every word without the prefix `W`,
every unsafe word extends `W` (`prefix_of_unsafe`).

## Main declarations
- `Rejection.trace_confined`
- `Rejection.not_unsafe_left`, `Rejection.exists_of_unsafe`, `Rejection.prefix_of_unsafe`
-/

namespace DeciNSSE.Complexity.Rejection

open Safety Directions

variable {n m : ℕ}

/-- Below `f(g, g, ⊥, …)`, for `g` itself below `f(g, g, ⊥, …)`, a tree is top at no path,
and bottom along every path with a direction other than `0` and `1`. -/
theorem trace_confined {g t : Tree n} (hg : g ≤ Tree.node (binaryChildren g g Tree.bot))
    (ht : t ≤ Tree.node (binaryChildren g g Tree.bot)) (π : List (Fin n)) :
    trace t π ≠ Tree.top ∧ (trace t π ≠ Tree.bot → ∀ i ∈ π, i.val < 2) := by
  induction π generalizing t with
  | nil => exact ⟨ne_top_of_le_node ht, by simp⟩
  | cons i π ih =>
    rw [trace_cons]
    by_cases hi : i.val < 2
    · have hd : descend t i ≤ g := by
        refine le_of_le_of_eq
          (descend_node (binaryChildren g g Tree.bot) i ▸ descend_mono ht i) ?_
        simp only [binaryChildren]
        split_ifs <;> first | rfl | omega
      obtain ⟨h1, h2⟩ := ih (le_trans hd hg)
      refine ⟨h1, fun h j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact h2 h j hj
    · have hd : descend t i = Tree.bot :=
        descend_eq_bot_of_le ht (by simp only [binaryChildren]; split_ifs <;> first | rfl | omega)
      rw [hd, trace_bot]
      exact ⟨Tree.bot_ne_top, fun h => absurd rfl h⟩

section Solution

variable (hn : 2 ≤ n) {A : BinNFA m} {ρ : V (m + 4) → Tree n}
  (hρ : Covariant.Sat ρ (rejectionSystem n A))
include hρ

/-- The tree of `x` is top at no path, and bottom along every path that leaves the binary
directions. -/
theorem trace_xVar (π : List (Fin n)) :
    trace (ρ xVar) π ≠ Tree.top ∧
      (trace (ρ xVar) π ≠ Tree.bot → ∀ i ∈ π, i.val < 2) := by
  obtain ⟨hb, hg, hx, -⟩ := (covSat_rejectionSystem_iff A ρ).mp hρ
  rw [hb] at hg hx
  exact trace_confined hg hx π

omit hρ in
/-- Above `f(t @ a, …)`, a tree is not bottom along `a π` where `t` is not bottom along `π`. -/
theorem trace_ne_bot_of_node_le {t u v : Tree n} {a : Fin 2}
    (h : Tree.node (letterChildren a t v) ≤ u) {π : List (Fin n)} (hπ : trace t π ≠ Tree.bot) :
    trace u (embedDir hn a :: π) ≠ Tree.bot := by
  have hd : t ≤ descend u (embedDir hn a) := by
    simpa using descend_mono h (embedDir hn a)
  intro hb
  have := trace_mono hd π
  rw [← trace_cons, hb, Tree.le_bot_iff] at this
  exact hπ this

/-- Along a run of `A` from `q`, the tree of `Y_q` is not bottom. -/
theorem trace_stateVar_ne_bot {q r : Fin m} {u : List (Fin 2)} (hu : A.Path q u r) :
    trace (ρ (stateVar q)) (u.map (embedDir hn)) ≠ Tree.bot := by
  obtain ⟨-, -, -, -, hY, htr, -⟩ := (covSat_rejectionSystem_iff A ρ).mp hρ
  induction u generalizing q with
  | nil => simpa using ne_bot_of_node_le (hY q)
  | cons a u ih =>
    obtain ⟨p, hp, hu⟩ := hu
    exact trace_ne_bot_of_node_le hn (htr q a p hp) (ih hu)

/-- Along every word accepted by `A`, the tree of `y` is not bottom. -/
theorem trace_yVar_ne_bot {u : List (Fin 2)} (hu : A.Accepts u) :
    trace (ρ yVar) (u.map (embedDir hn)) ≠ Tree.bot := by
  obtain ⟨-, -, -, hy, -, -, hinit⟩ := (covSat_rejectionSystem_iff A ρ).mp hρ
  obtain ⟨p, hp, r, -, hpath⟩ := hu
  cases u with
  | nil => simpa using ne_bot_of_node_le hy
  | cons a u =>
    obtain ⟨p', ht, hpath⟩ := hpath
    exact trace_ne_bot_of_node_le hn (hinit p a p' ht hp) (trace_stateVar_ne_bot hn hρ hpath)

end Solution

section Unsafe

variable {A : BinNFA m}

/-- No word is left unsafe, since `x` is top at no path. -/
theorem not_unsafe_left (w : List (Fin n)) :
    ¬ Unsafe (fun _ => false) (rejectionSystem n A) xVar yVar .l w := by
  rintro ⟨ρ, hρ, hx, -⟩
  rw [sat_false] at hρ
  rw [prefTop_false_iff] at hx
  exact (trace_xVar hρ w).1 hx

variable (hn : 2 ≤ n)

/-- Every unsafe word is right unsafe, and it is the image of a binary word that `A`
rejects. -/
theorem exists_of_unsafe {θ : Side} {w : List (Fin n)}
    (h : Unsafe (fun _ => false) (rejectionSystem n A) xVar yVar θ w) :
    θ = .r ∧ ∃ u, ¬ A.Accepts u ∧ w = u.map (embedDir hn) := by
  cases θ with
  | l => exact absurd h (not_unsafe_left w)
  | r =>
    obtain ⟨ρ, hρ, hy, hx⟩ := h
    rw [sat_false] at hρ
    rw [prefBot_false_iff] at hy hx
    obtain ⟨u, rfl, -⟩ := Words.exists_map_eq (f := embedDir hn) (S := List.finRange 2)
      fun i hi => ⟨⟨i.val, (trace_xVar hρ w).2 hx i hi⟩, List.mem_finRange _, rfl⟩
    exact ⟨rfl, u, fun hu => trace_yVar_ne_bot hn hρ hu hy, rfl⟩

/-- If `A` accepts every word without the prefix `W`, every unsafe word extends `W`. -/
theorem prefix_of_unsafe {W : List (Fin 2)} (hA : ∀ u, ¬ W <+: u → A.Accepts u) {θ : Side}
    {w : List (Fin n)} (h : Unsafe (fun _ => false) (rejectionSystem n A) xVar yVar θ w) :
    W.map (embedDir hn) <+: w := by
  obtain ⟨-, u, hu, rfl⟩ := exists_of_unsafe hn h
  by_contra hW
  exact hu (hA u fun h => hW (h.map _))

end Unsafe

end DeciNSSE.Complexity.Rejection
