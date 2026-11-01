import DeciNSSE.Complexity.WitnessSystem
import DeciNSSE.Countermodels
import DeciNSSE.Solver.Checked

/-! # Unsafe words of the witness system

Let `A` be a binary automaton and `ρ` a solution of `witnessSystem n A`, for
`n ≥ 2` and the covariant constructor.

- `x` and `g` lie below `f(g, g, ⊥, …)`, so `x` is top at no path and bottom
  along every path that leaves the binary directions (`trace_confined`). So no
  word is left unsafe.
- Along a run of `A` from `q` on `u`, the tree of `Y_q` is not bottom at `u`, and
  along every word accepted by `A`, the tree of `y` is not bottom.

So every unsafe word is right unsafe and is the image of a binary word that `A`
rejects (`exists_of_unsafe`). If `A` accepts every word without the prefix `W`,
every unsafe word extends `W` (`unsafe_prefix`).

Conversely, let all states be final, and let `A` accept the empty word but not
a prefix `u` of the binary word `w`. A finite solution of depth `h = |w| + 1`
takes for `x` the path tree of `w`, for `g` the full binary tree of depth `h`,
and for `Y_q` and `y` the truncations at depth `h` of the languages accepted
from `q` and by `A` (`trunc`): constructors at the accepted words shorter than
`h`, top at those of length `h`, and bottom elsewhere. In it, `x` is a
constructor along `w` and `y` is bottom at `u` (`unsafe_of_not_accepts`). One
finite countermodel thus refutes entailment over finite, regular and arbitrary
trees.

For the language of the words without the prefix `W`, with `W` nonempty, the
unsafe words, the holes of the side monitors, the words passing `refutesB` and
the words of the refutations passing the solver's checker are exactly the
binary words that extend `W`, all on the right side.

## Main declarations
- `Witness.not_unsafe_left`, `Witness.unsafe_prefix`, `Witness.unsafe_word`,
  `Witness.unsafe_iff`
- `Witness.satisfiableFin_witness`
- `Witness.not_entailsFin_witness`, `Witness.not_entailsReg_witness`,
  `Witness.not_entails_witness`
- `Witness.hole_iff`, `Witness.refutesB_iff`, `Witness.checkRefutation_iff`,
  and the prefix forms `Witness.hole_prefix`, `Witness.refutesB_prefix`,
  `Witness.checkRefutation_prefix`
-/

namespace DeciNSSE.Complexity.Witness

open Safety
open Hardness (dir dir_injective kids avoid avoid_succ avoid_mono pathTree pathTree_le_avoid
  trace_pathTree ne_top_of_le_node ne_bot_of_node_le descend_eq_bot_of_le ftree_bot_le)

variable {n m : ℕ}

/-- Covariant top prefixes are top traces. -/
theorem prefTop_false_iff (w : List (Fin n)) (t : Tree n) :
    prefTop (fun _ => false) w t ↔ trace t w = Tree.top := by
  rw [trace_eq_top_iff]
  simp only [prefTop, polarity_false, Sym.flip_false, HasLabel]

/-- Covariant bottom prefixes are bottom traces. -/
theorem prefBot_false_iff (w : List (Fin n)) (t : Tree n) :
    prefBot (fun _ => false) w t ↔ trace t w = Tree.bot := by
  rw [trace_eq_bot_iff]
  simp only [prefBot, polarity_false, Sym.flip_false, HasLabel]

/-- Below `f(g, g, ⊥, …)`, for `g` itself below `f(g, g, ⊥, …)`, a tree is top at no path,
and bottom along every path with a direction other than `0` and `1`. -/
theorem trace_confined {g t : Tree n} (hg : g ≤ Tree.node (kids g g Tree.bot))
    (ht : t ≤ Tree.node (kids g g Tree.bot)) (π : List (Fin n)) :
    trace t π ≠ Tree.top ∧ (trace t π ≠ Tree.bot → ∀ i ∈ π, i.val < 2) := by
  induction π generalizing t with
  | nil => exact ⟨ne_top_of_le_node ht, by simp⟩
  | cons i π ih =>
    rw [trace_cons]
    by_cases hi : i.val < 2
    · have hd : descend t i ≤ g := by
        refine le_of_le_of_eq (descend_node (kids g g Tree.bot) i ▸ descend_mono ht i) ?_
        simp only [kids]
        split_ifs <;> first | rfl | omega
      obtain ⟨h1, h2⟩ := ih (le_trans hd hg)
      refine ⟨h1, fun h j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact h2 h j hj
    · have hd : descend t i = Tree.bot :=
        descend_eq_bot_of_le ht (by simp only [kids]; split_ifs <;> first | rfl | omega)
      rw [hd, trace_bot]
      exact ⟨Tree.bot_ne_top, fun h => absurd rfl h⟩

/-- A path in the directions `0` and `1` is the image of a binary word. -/
theorem exists_map_dir (hn : 2 ≤ n) : ∀ {π : List (Fin n)}, (∀ i ∈ π, i.val < 2) →
    ∃ u : List (Fin 2), π = u.map (dir hn)
  | [], _ => ⟨[], rfl⟩
  | i :: π, h => by
    obtain ⟨u, rfl⟩ := exists_map_dir hn fun j hj => h j (List.mem_cons_of_mem _ hj)
    exact ⟨⟨i.val, h i List.mem_cons_self⟩ :: u, by rw [List.map_cons]; rfl⟩

section Solution

variable (hn : 2 ≤ n) {A : BinNFA m} {ρ : V (m + 4) → Tree n}
  (hρ : Covariant.Sat ρ (witnessSystem n A))
include hρ

/-- The tree of `x` is top at no path, and bottom along every path that leaves the binary
directions. -/
theorem trace_xVar (π : List (Fin n)) :
    trace (ρ xVar) π ≠ Tree.top ∧
      (trace (ρ xVar) π ≠ Tree.bot → ∀ i ∈ π, i.val < 2) := by
  obtain ⟨hb, hg, hx, -⟩ := (covSat_witnessSystem_iff A ρ).mp hρ
  rw [hb] at hg hx
  exact trace_confined hg hx π

omit hρ in
/-- Above `f(t @ a, …)`, a tree is not bottom along `a π` where `t` is not bottom along `π`. -/
theorem trace_ne_bot_of_node_le {t u v : Tree n} {a : Fin 2}
    (h : Tree.node (letterKids a t v) ≤ u) {π : List (Fin n)} (hπ : trace t π ≠ Tree.bot) :
    trace u (dir hn a :: π) ≠ Tree.bot := by
  have hd : t ≤ descend u (dir hn a) := by
    simpa [letterKids] using descend_mono h (dir hn a)
  intro hb
  have := trace_mono hd π
  rw [← trace_cons, hb, Tree.le_bot_iff] at this
  exact hπ this

/-- Along a run of `A` from `q`, the tree of `Y_q` is not bottom. -/
theorem trace_stateVar_ne_bot {q r : Fin m} {u : List (Fin 2)} (hu : A.Path q u r) :
    trace (ρ (stateVar q)) (u.map (dir hn)) ≠ Tree.bot := by
  obtain ⟨-, -, -, -, hY, htr, -⟩ := (covSat_witnessSystem_iff A ρ).mp hρ
  induction u generalizing q with
  | nil => simpa using ne_bot_of_node_le (hY q)
  | cons a u ih =>
    obtain ⟨p, hp, hu⟩ := hu
    exact trace_ne_bot_of_node_le hn (htr q a p hp) (ih hu)

/-- Along every word accepted by `A`, the tree of `y` is not bottom. -/
theorem trace_yVar_ne_bot {u : List (Fin 2)} (hu : A.Accepts u) :
    trace (ρ yVar) (u.map (dir hn)) ≠ Tree.bot := by
  obtain ⟨-, -, -, hy, -, -, hinit⟩ := (covSat_witnessSystem_iff A ρ).mp hρ
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
    ¬ Unsafe (fun _ => false) (witnessSystem n A) xVar yVar .l w := by
  rintro ⟨ρ, hρ, hx, -⟩
  rw [sat_false] at hρ
  rw [prefTop_false_iff] at hx
  exact (trace_xVar hρ w).1 hx

variable (hn : 2 ≤ n)

/-- Every unsafe word is right unsafe, and it is the image of a binary word that `A`
rejects. -/
theorem exists_of_unsafe {θ : Side} {w : List (Fin n)}
    (h : Unsafe (fun _ => false) (witnessSystem n A) xVar yVar θ w) :
    θ = .r ∧ ∃ u, ¬ A.Accepts u ∧ w = u.map (dir hn) := by
  cases θ with
  | l => exact absurd h (not_unsafe_left w)
  | r =>
    obtain ⟨ρ, hρ, hy, hx⟩ := h
    rw [sat_false] at hρ
    rw [prefBot_false_iff] at hy hx
    obtain ⟨u, rfl⟩ := exists_map_dir hn ((trace_xVar hρ w).2 hx)
    exact ⟨rfl, u, fun hu => trace_yVar_ne_bot hn hρ hu hy, rfl⟩

/-- If `A` accepts every word without the prefix `W`, every unsafe word extends `W`. -/
theorem unsafe_prefix {W : List (Fin 2)} (hA : ∀ u, ¬ W <+: u → A.Accepts u) {θ : Side}
    {w : List (Fin n)} (h : Unsafe (fun _ => false) (witnessSystem n A) xVar yVar θ w) :
    W.map (dir hn) <+: w := by
  obtain ⟨-, u, hu, rfl⟩ := exists_of_unsafe hn h
  by_contra hW
  exact hu (hA u fun h => hW (h.map _))

end Unsafe

section Truncation

open Classical in
/-- The truncation at depth `h` of a set `L` of paths: constructors at the paths shorter
than `h` all of whose prefixes lie in `L`, top at such paths of length `h`, and bottom
elsewhere. -/
noncomputable def trunc (L : List (Fin n) → Prop) : ℕ → FTree n
  | 0 => if L [] then .top else .bot
  | h + 1 => if L [] then .node fun i => trunc (fun σ => L (i :: σ)) h else .bot

/-- Without the root in `L`, the truncation is bottom. -/
theorem trunc_of_not_nil {L : List (Fin n) → Prop} (hL : ¬ L []) (h : ℕ) :
    trunc L h = .bot := by
  cases h <;> simp [trunc, hL]

/-- With the root in `L`, the truncation at a positive depth is a constructor. -/
theorem trunc_succ {L : List (Fin n) → Prop} (hL : L []) (h : ℕ) :
    trunc L (h + 1) = .node fun i => trunc (fun σ => L (i :: σ)) h := by
  simp [trunc, hL]

/-- The top term is greatest. -/
theorem ftree_le_top (t : FTree n) : t ≤ FTree.top := Tree.le_top t.toTree

/-- A larger set of paths and a smaller depth give a larger truncation. -/
theorem trunc_mono : ∀ {L L' : List (Fin n) → Prop} {h h' : ℕ},
    (∀ σ, L σ → L' σ) → h' ≤ h → trunc L h ≤ trunc L' h'
  | L, L', h, 0, hL, _ => by
    by_cases h0 : L []
    · rw [show trunc L' 0 = .top by simp [trunc, hL _ h0]]
      exact ftree_le_top _
    · rw [trunc_of_not_nil h0]
      exact ftree_bot_le _
  | L, L', h + 1, h' + 1, hL, hh => by
    by_cases h0 : L []
    · rw [trunc_succ h0, trunc_succ (hL _ h0), FTree.node_le_node_iff]
      exact fun i => trunc_mono (fun σ => hL (i :: σ)) (by omega)
    · rw [trunc_of_not_nil h0]
      exact ftree_bot_le _
  | _, _, 0, _ + 1, _, hh => absurd hh (by omega)

/-- At a path of length at most `h` outside `L`, the truncation is bottom. -/
theorem trace_trunc_of_not_mem : ∀ {L : List (Fin n) → Prop} {h : ℕ} {σ : List (Fin n)},
    σ.length ≤ h → ¬ L σ → trace (trunc L h).toTree σ = Tree.bot
  | _, h, [], _, hσ => by rw [trunc_of_not_nil hσ]; rfl
  | L, h + 1, i :: σ, hlen, hσ => by
    by_cases h0 : L []
    · rw [trunc_succ h0, trace_cons, FTree.toTree_node, descend_node]
      exact trace_trunc_of_not_mem (by simpa using hlen) hσ
    · rw [trunc_of_not_nil h0]
      simp
  | _, 0, _ :: _, hlen, _ => absurd hlen (by simp)

end Truncation

section Countermodel

variable (hn : 2 ≤ n) (A : BinNFA m)

/-- The images of the words accepted from `q`. -/
def stateLang (q : Fin m) (σ : List (Fin n)) : Prop :=
  ∃ u, A.AcceptsFrom q u ∧ σ = u.map (dir hn)

/-- The images of the words accepted by `A`. -/
def lang (σ : List (Fin n)) : Prop :=
  ∃ u, A.Accepts u ∧ σ = u.map (dir hn)

/-- The finite countermodel for the binary word `w`, of depth `|w| + 1`. -/
noncomputable def counterValuation (w : List (Fin 2)) : V (m + 4) → FTree n :=
  valuation (pathTree (w.map (dir hn))) (trunc (lang hn A) (w.length + 1))
    (avoid (fun _ => False) (w.length + 1)) .bot
    (fun q => trunc (stateLang hn A q) (w.length + 1))

/-- The full binary tree of depth `h + 1` is `f(F, F, ⊥, …)` for the full binary tree `F`
of depth `h`. -/
theorem avoid_false_succ (h : ℕ) :
    avoid (fun _ : List (Fin n) => False) (h + 1) =
      .node (kids (avoid (fun _ => False) h) (avoid (fun _ => False) h) .bot) := by
  rw [avoid_succ not_false]
  congr 1
  funext i
  simp only [kids]
  split_ifs <;> first | rfl | omega

/-- The embedding of finite terms commutes with `f(u, v, w, …)`. -/
theorem node_kids_toTree (a b c : FTree n) :
    Tree.node (kids a.toTree b.toTree c.toTree) = (FTree.node (kids a b c)).toTree := by
  rw [FTree.toTree_node, ← Hardness.comp_kids]
  rfl

/-- The embedding of finite terms commutes with `f(u @ a, v, …)`. -/
theorem node_letterKids_toTree (a : Fin 2) (u v : FTree n) :
    Tree.node (letterKids a u.toTree v.toTree) = (FTree.node (letterKids a u v)).toTree := by
  rw [FTree.toTree_node, ← comp_letterKids]
  rfl

/-- The constructor `f(t @ a, ⊥, …)` lies below the truncation of `L` at depth `h + 1`
whenever `L` contains the root and the truncation of `L'` at depth `h + 1` lies below the
truncation of the residual of `L` at `a`, for instance when `a L' ⊆ L`. -/
theorem node_letterKids_le_trunc {L L' : List (Fin n) → Prop} (hL : L []) (a : Fin 2)
    (hL' : ∀ σ, L' σ → L (dir hn a :: σ)) (h : ℕ) :
    FTree.node (letterKids a (trunc L' (h + 1)) .bot) ≤ trunc L (h + 1) := by
  rw [trunc_succ hL, FTree.node_le_node_iff]
  intro i
  simp only [letterKids]
  split_ifs with hi
  · obtain rfl : i = dir hn a := Fin.ext hi
    exact trunc_mono hL' (Nat.le_succ h)
  · exact ftree_bot_le _

/-- The constructor `f(⊥, …, ⊥)` lies below the truncation of `L` at a positive depth if `L`
contains the root. -/
theorem node_bot_le_trunc {L : List (Fin n) → Prop} (hL : L []) (h : ℕ) :
    FTree.node (kids .bot .bot .bot) ≤ trunc L (h + 1) := by
  rw [trunc_succ hL, FTree.node_le_node_iff]
  intro i
  simp only [kids]
  split_ifs <;> exact ftree_bot_le _

/-- If all states are final and `A` accepts the empty word, the countermodel is a
solution. -/
theorem sat_counterValuation (hfin : ∀ q, A.final q = true) (hnil : A.Accepts [])
    (w : List (Fin 2)) :
    Covariant.Sat (FTree.toTree ∘ counterValuation hn A w) (witnessSystem n A) := by
  rw [covSat_witnessSystem_iff]
  simp only [Function.comp_apply, node_kids_toTree, node_letterKids_toTree,
    FTree.toTree_le_iff]
  simp only [counterValuation, valuation_xVar, valuation_yVar, valuation_gVar,
    valuation_bVar, valuation_stateVar, FTree.toTree_bot, true_and]
  have hstate : ∀ q, stateLang hn A q [] :=
    fun q => ⟨[], (A.acceptsFrom_nil q).mpr (hfin q), rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `g` is the full binary tree
    rw [← avoid_false_succ]
    exact avoid_mono (fun _ h => h) (Nat.le_succ _)
  · -- `x` is the path tree of `w`
    rw [← avoid_false_succ]
    refine pathTree_le_avoid _ (by simp only [List.length_map]; omega) ?_ (fun _ _ h => h)
    intro i hi
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hi
    exact a.isLt
  · exact node_bot_le_trunc ⟨[], hnil, rfl⟩ _
  · exact fun q => node_bot_le_trunc (hstate q) _
  · intro q a r ht
    refine node_letterKids_le_trunc hn (hstate q) a ?_ _
    rintro σ ⟨u, hu, rfl⟩
    exact ⟨a :: u, A.acceptsFrom_cons ht hu, rfl⟩
  · intro q a r ht hq
    refine node_letterKids_le_trunc hn ⟨[], hnil, rfl⟩ a ?_ _
    rintro σ ⟨u, hu, rfl⟩
    exact ⟨a :: u, ⟨q, hq, A.acceptsFrom_cons ht hu⟩, rfl⟩

variable {A}

/-- In the countermodel, `x` is a constructor along `w`, and `y` is bottom along `w` if `A`
rejects a prefix of `w`. -/
theorem trace_counterValuation {u w : List (Fin 2)} (hu : ¬ A.Accepts u) (huw : u <+: w) :
    trace (counterValuation hn A w xVar).toTree (w.map (dir hn)) ≠ Tree.bot ∧
      trace (counterValuation hn A w yVar).toTree (w.map (dir hn)) = Tree.bot := by
  simp only [counterValuation, valuation_xVar, valuation_yVar, trace_pathTree]
  refine ⟨by simp, ?_⟩
  obtain ⟨v, rfl⟩ := huw
  rw [List.map_append, trace_append, trace_trunc_of_not_mem (by simp; omega), trace_bot]
  rintro ⟨u', hu', he⟩
  rw [List.map_injective_iff.mpr (dir_injective hn) he] at hu
  exact hu hu'

/-- If all states are final and `A` accepts the empty word but not the prefix `u` of `w`,
then `w` is right unsafe. -/
theorem unsafe_of_not_accepts (hfin : ∀ q, A.final q = true) (hnil : A.Accepts [])
    {u w : List (Fin 2)} (hu : ¬ A.Accepts u) (huw : u <+: w) :
    Unsafe (fun _ => false) (witnessSystem n A) xVar yVar .r (w.map (dir hn)) := by
  obtain ⟨hx, hy⟩ := trace_counterValuation hn hu huw
  exact ⟨_, (sat_false _ _).mpr (sat_counterValuation hn A hfin hnil w),
    (prefBot_false_iff _ _).mpr hy, fun h => hx ((prefBot_false_iff _ _).mp h)⟩

include hn in
/-- Under the same conditions, the finite countermodel refutes entailment over finite
trees. -/
theorem not_entailsFin_of_not_accepts (hfin : ∀ q, A.final q = true) (hnil : A.Accepts [])
    {u : List (Fin 2)} (hu : ¬ A.Accepts u) :
    ¬ EntailsFin (fun _ => false) (witnessSystem n A) xVar yVar := by
  intro h
  have hle := (treeLe_false_iff_le _ _).mp
    (h _ ((sat_false _ _).mpr (sat_counterValuation hn A hfin hnil u)))
  obtain ⟨hx, hy⟩ := trace_counterValuation hn hu (List.prefix_refl u)
  exact hx ((Tree.le_bot_iff _).mp (hy ▸ trace_mono hle _))

end Countermodel

/-- The system always has a finite solution: `x`, `g` and `b` bottom, `y` and all `Y_q`
top. -/
theorem satisfiableFin_witness (A : BinNFA m) :
    SatisfiableFin (fun _ => false) (witnessSystem n A) := by
  refine ⟨valuation .bot .top .bot .bot fun _ => .top, ?_⟩
  rw [sat_false, covSat_witnessSystem_iff]
  simp

/-- The system always has a solution. -/
theorem satisfiable_witness (A : BinNFA m) :
    Satisfiable (fun _ => false) (witnessSystem n A) :=
  let ⟨_, hσ⟩ := satisfiableFin_witness A
  ⟨_, hσ⟩

section Language

variable (hn : 2 ≤ n) {A : BinNFA m} {W : List (Fin 2)} (hfin : ∀ q, A.final q = true)
  (hW : W ≠ []) (hA : ∀ u, A.Accepts u ↔ ¬ W <+: u)
include hn hfin hW hA

/-- Every binary word that extends `W` is right unsafe. -/
theorem unsafe_append (v : List (Fin 2)) :
    Unsafe (fun _ => false) (witnessSystem n A) xVar yVar .r ((W ++ v).map (dir hn)) :=
  unsafe_of_not_accepts hn hfin ((hA []).mpr fun h => hW (List.prefix_nil.mp h))
    (fun h => (hA W).mp h (List.prefix_refl W)) (List.prefix_append W v)

/-- The word `W` is right unsafe. -/
theorem unsafe_word : Unsafe (fun _ => false) (witnessSystem n A) xVar yVar .r (W.map (dir hn)) :=
  by simpa using unsafe_append hn hfin hW hA []

/-- The unsafe words are exactly the binary words that extend `W`, all on the right
side. -/
theorem unsafe_iff (θ : Side) (w : List (Fin n)) :
    Unsafe (fun _ => false) (witnessSystem n A) xVar yVar θ w ↔
      θ = .r ∧ ∃ v, w = (W ++ v).map (dir hn) := by
  constructor
  · intro h
    obtain ⟨rfl, u, hu, rfl⟩ := exists_of_unsafe hn h
    obtain ⟨v, rfl⟩ : W <+: u := by
      by_contra h
      exact hu ((hA u).mpr h)
    exact ⟨rfl, v, rfl⟩
  · rintro ⟨rfl, v, rfl⟩
    exact unsafe_append hn hfin hW hA v

/-- Entailment fails over finite trees. -/
theorem not_entailsFin_witness :
    ¬ EntailsFin (fun _ => false) (witnessSystem n A) xVar yVar :=
  not_entailsFin_of_not_accepts hn hfin ((hA []).mpr fun h => hW (List.prefix_nil.mp h))
    (fun h => (hA W).mp h (List.prefix_refl W))

/-- Entailment fails over regular trees. -/
theorem not_entailsReg_witness :
    ¬ EntailsReg (fun _ => false) (witnessSystem n A) xVar yVar :=
  fun h => not_entailsFin_witness hn hfin hW hA (Characterisation.entailsReg_toFin _ _ _ _ h)

/-- Entailment fails over arbitrary trees. -/
theorem not_entails_witness :
    ¬ Entails (fun _ => false) (witnessSystem n A) xVar yVar :=
  fun h => not_entailsReg_witness hn hfin hW hA (Characterisation.entails_toReg _ _ _ _ h)

end Language

section Certificates

open Monitor

variable (hn : 2 ≤ n) {A : BinNFA m} {W : List (Fin 2)}

/-- The holes of the side monitors are the unsafe words. -/
theorem hole_iff_unsafe (θ : Side) (w : List (Fin n)) :
    (sideMonitor (fun _ => false) (witnessSystem n A) xVar yVar θ).Hole w ↔
      Unsafe (fun _ => false) (witnessSystem n A) xVar yVar θ w :=
  (sideMonitor _ _ _ _ θ).hole_iff_unsafe (satisfiable_witness A) w

/-- The solver's refutation checker is the Boolean certificate check of its side and
word. -/
theorem checkRefutation_eq_refutesB {k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) (cert : Certificates.Refutation n) :
    Solver.Checked.checkRefutation c ϕ x y cert = refutesB c ϕ x y cert.side cert.word :=
  Solver.Checked.checkRefutation_eq c ϕ x y cert

/-- If `A` accepts every word without the prefix `W`, every hole extends `W`. -/
theorem hole_prefix (hA : ∀ u, ¬ W <+: u → A.Accepts u) {θ : Side} {w : List (Fin n)}
    (h : (sideMonitor (fun _ => false) (witnessSystem n A) xVar yVar θ).Hole w) :
    W.map (dir hn) <+: w :=
  unsafe_prefix hn hA ((hole_iff_unsafe θ w).mp h)

/-- If `A` accepts every word without the prefix `W`, every word passing the Boolean
certificate check extends `W`. -/
theorem refutesB_prefix (hA : ∀ u, ¬ W <+: u → A.Accepts u) {θ : Side} {w : List (Fin n)}
    (h : refutesB (fun _ => false) (witnessSystem n A) xVar yVar θ w = true) :
    W.map (dir hn) <+: w :=
  unsafe_prefix hn hA ((refutesB_iff_unsafe _ _ _ _ θ w).mp h)

/-- If `A` accepts every word without the prefix `W`, the word of every refutation passing
the solver's checker extends `W`. -/
theorem checkRefutation_prefix (hA : ∀ u, ¬ W <+: u → A.Accepts u)
    {cert : Certificates.Refutation n}
    (h : Solver.Checked.checkRefutation (fun _ => false) (witnessSystem n A) xVar yVar cert =
      true) :
    W.map (dir hn) <+: cert.word :=
  refutesB_prefix hn hA ((checkRefutation_eq_refutesB _ _ _ _ cert).symm.trans h)

variable (hfin : ∀ q, A.final q = true) (hW : W ≠ []) (hA : ∀ u, A.Accepts u ↔ ¬ W <+: u)
include hfin hW hA

/-- The left monitor has no hole, and the holes of the right monitor are exactly the binary
words that extend `W`. -/
theorem hole_iff (θ : Side) (w : List (Fin n)) :
    (sideMonitor (fun _ => false) (witnessSystem n A) xVar yVar θ).Hole w ↔
      θ = .r ∧ ∃ v, w = (W ++ v).map (dir hn) :=
  (hole_iff_unsafe θ w).trans (unsafe_iff hn hfin hW hA θ w)

/-- The words passing the Boolean certificate check are exactly the binary words that
extend `W`, on the right side. -/
theorem refutesB_iff (θ : Side) (w : List (Fin n)) :
    refutesB (fun _ => false) (witnessSystem n A) xVar yVar θ w = true ↔
      θ = .r ∧ ∃ v, w = (W ++ v).map (dir hn) :=
  (refutesB_iff_unsafe _ _ _ _ θ w).trans (unsafe_iff hn hfin hW hA θ w)

/-- The refutations passing the solver's checker are exactly the right-side refutations whose
words extend `W`. -/
theorem checkRefutation_iff (cert : Certificates.Refutation n) :
    Solver.Checked.checkRefutation (fun _ => false) (witnessSystem n A) xVar yVar cert =
        true ↔
      cert.side = .r ∧ ∃ v, cert.word = (W ++ v).map (dir hn) := by
  rw [checkRefutation_eq_refutesB]
  exact refutesB_iff hn hfin hW hA cert.side cert.word

end Certificates

section Example

/-- The binary words without the prefix `00`: the initial state `0` reads `0` to `1` and `1`
to `2`, the state `1` reads `1` to `2`, and the state `2` loops; all states are final. -/
def noZeroZero : BinNFA 3 :=
  ⟨fun q => q = 0, fun _ => true, [(0, 0, 1), (0, 1, 2), (1, 1, 2), (2, 0, 2), (2, 1, 2)]⟩

/-- The looping state accepts every word. -/
theorem noZeroZero_acceptsFrom_two (u : List (Fin 2)) : noZeroZero.AcceptsFrom 2 u := by
  refine ⟨2, rfl, ?_⟩
  induction u with
  | nil => rfl
  | cons a u ih => exact ⟨2, by fin_cases a <;> simp [noZeroZero], ih⟩

/-- The automaton accepts exactly the words without the prefix `00`. -/
theorem noZeroZero_accepts_iff (u : List (Fin 2)) :
    noZeroZero.Accepts u ↔ ¬ [0, 0] <+: u := by
  constructor
  · rintro ⟨p, hp, r, -, hpath⟩ ⟨v, rfl⟩
    obtain rfl : p = 0 := by simpa [noZeroZero] using hp
    obtain ⟨p₁, h₁, p₂, h₂, -⟩ := hpath
    obtain rfl : p₁ = 1 := by simpa [noZeroZero] using h₁
    simp [noZeroZero] at h₂
  · intro h
    have two := noZeroZero_acceptsFrom_two
    refine ⟨0, rfl, ?_⟩
    rcases u with _ | ⟨a, _ | ⟨b, v⟩⟩
    · exact ⟨0, rfl, rfl⟩
    · fin_cases a
      · exact ⟨1, rfl, 1, by simp [noZeroZero], rfl⟩
      · exact noZeroZero.acceptsFrom_cons (by simp [noZeroZero]) (two [])
    · fin_cases a
      · fin_cases b
        · exact absurd ⟨v, rfl⟩ h
        · exact noZeroZero.acceptsFrom_cons (q := 1) (by simp [noZeroZero])
            (noZeroZero.acceptsFrom_cons (by simp [noZeroZero]) (two v))
      · exact noZeroZero.acceptsFrom_cons (by simp [noZeroZero]) (two (b :: v))

/-- For `W = 00` at arity three, the unsafe words are the binary words that extend `00`. -/
example (θ : Side) (w : List (Fin 3)) :
    Unsafe (fun _ => false) (witnessSystem 3 noZeroZero) xVar yVar θ w ↔
      θ = .r ∧ ∃ v, w = ([0, 0] ++ v).map (dir (by norm_num)) :=
  unsafe_iff _ (fun _ => rfl) (List.cons_ne_nil _ _) noZeroZero_accepts_iff θ w

/-- For `W = 00`, entailment fails already over finite trees. -/
example : ¬ EntailsFin (fun _ => false) (witnessSystem 2 noZeroZero) xVar yVar :=
  not_entailsFin_witness le_rfl (fun _ => rfl) (List.cons_ne_nil _ _) noZeroZero_accepts_iff

end Example

end DeciNSSE.Complexity.Witness
