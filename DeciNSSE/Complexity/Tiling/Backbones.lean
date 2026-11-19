import DeciNSSE.Complexity.Tiling.Emitter

/-! # Paths along emitted backbones

## Main declarations

- `Emitter.upper_step`, `Emitter.lower_step` characterize all emitted children.
- `Emitter.masks` computes both label sets on a word up to its first target.
-/

namespace DeciNSSE.Complexity.Tiling.Emitter
variable {n : ℕ} (M : StoppingTable (Fin n))
local notation "Z" => system M

/-- The upper backbone variable determines its state. -/
@[simp] theorem u_inj (p q) : u M p = u M q ↔ p = q := by simp [u, Fin.ext_iff]

/-- The lower backbone variable determines its state. -/
@[simp] theorem l_inj (p q) : l M p = l M q ↔ p = q := by simp [l, Fin.ext_iff]

/-- The upper and lower backbone variables occupy disjoint sets of indices. -/
@[simp] theorem l_ne_u (p q) : l M p ≠ u M q := by simp [l,u,Fin.ext_iff]; omega

/-- Every upper backbone variable is distinct from every admission marker. -/
@[simp] theorem u_ne_marker (p q) : u M p ≠ marker M q := by
  unfold marker; split <;> simp [u,l,Fin.ext_iff] <;> omega

/-- The dummy variable is distinct from every upper backbone variable. -/
@[simp] theorem u_ne_dummy (p) : u M p ≠ dummy M := by simp [u,dummy,Fin.ext_iff]; omega

/-- The dummy variable is distinct from every lower backbone variable. -/
@[simp] theorem l_ne_dummy (p) : l M p ≠ dummy M := by simp [l,dummy,Fin.ext_iff]; omega

/-- Every admission marker is distinct from the dummy variable. -/
@[simp] theorem marker_ne_dummy (p) : marker M p ≠ dummy M := by
  unfold marker; split <;> simp [l,dummy,Fin.ext_iff] <;> omega

/-- The variable equated to top is distinct from every lower backbone variable. -/
@[simp] theorem top_ne_l (p) : top M ≠ l M p := by simp [top,l,Fin.ext_iff]; omega

/-- The variable equated to top is distinct from every admission marker. -/
@[simp] theorem top_ne_marker (p) : top M ≠ marker M p := by
  unfold marker; split <;> simp_all [top,Fin.ext_iff,l] <;> omega

/-- The admission marker determines its state, including the marker at the start. -/
@[simp] theorem marker_inj (p q) : marker M p = marker M q ↔ p = q := by
  unfold marker; split_ifs <;> simp_all [l,Fin.ext_iff] <;> omega

/-- A lower backbone variable equals a marker exactly when both correspond to the start state. -/
@[simp] theorem l_eq_marker (p q) : l M p = marker M q ↔ p = M.start ∧ q = M.start := by
  unfold marker; split <;> simp_all [l,Fin.ext_iff]; omega

private theorem vectors_at {k : ℕ} (f : Fin n → List (V k)) (d : V k)
    (hn : ∀ i, f i ≠ []) (i : Fin n) (z : V k) :
    (∃ a ∈ vectors f d, a i = z) ↔ z ∈ f i := by
  simp only [vectors, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨a,⟨j,t,ht,rfl⟩,rfl⟩
    dsimp only
    split <;> rename_i h
    · exact h ▸ ht
    · cases he : f i with
      | nil => exact (hn i he).elim
      | cons x xs => simp
  · intro h
    exact ⟨_,⟨i,z,h,rfl⟩,by simp⟩

/-- Each successor state has at least one upper child choice. -/
theorem upper_nonempty (r) : upper M r ≠ [] := by
  have general (xs : List (V (K M))) : (if xs.isEmpty then [dummy M] else xs) ≠ [] := by
    cases xs <;> simp
  exact general _

/-- Apart from the dummy, the upper children at a state are its own nontarget backbone and the
markers admitted into that state. -/
theorem mem_upper {x} (hd : x ≠ dummy M) (r) :
    x ∈ upper M r ↔ (r ∉ M.target ∧ x = u M r) ∨
      ∃ q, (q,r) ∈ M.pairs ∧ x = marker M q := by
  let xs := (if r ∈ M.target then [] else [u M r]) ++
    ((List.finRange M.size).filter fun a => (a,r) ∈ M.pairs).map (marker M)
  have mem : x ∈ upper M r ↔ x ∈ xs := by
    change x ∈ (if xs.isEmpty then _ else xs) ↔ _
    cases xs <;> simp [hd]
  rw [mem]
  dsimp [xs]; split <;> simp_all [eq_comm]

/-- An upper backbone belongs to the upper child choices exactly at its own nontarget state. -/
theorem u_mem_upper (q r) : u M q ∈ upper M r ↔ q = r ∧ r ∉ M.target := by
  rw [mem_upper M (u_ne_dummy M _)]; simp [and_comm]

/-- A lower backbone belongs to the lower child choices exactly at its own state. -/
theorem l_mem_lower (q r) : l M q ∈ lower M r ↔ q = r := by
  simp [lower]; grind

/-- The lower child choices for an ordinary transition exclude the variable equated to top. -/
theorem top_not_lower (q) : top M ∉ lower M q := by simp [lower]

/-- The lower choices at `q` meet the upper choices at `r` exactly when the table admits the
pair `(q,r)`. -/
theorem meet_iff (q r) :
    (∃ z ∈ lower M q, z ∈ upper M r) ↔ (q,r) ∈ M.pairs := by
  have hm : marker M q ∈ upper M r ↔ (q,r) ∈ M.pairs := by
    rw [mem_upper M (marker_ne_dummy M _)]
    simp [Ne.symm (u_ne_marker M r q)]
  constructor
  · rintro ⟨z,hz,hu⟩
    rcases (show z = l M q ∨ z = marker M q by simpa [lower] using hz) with rfl | rfl
    · rw [mem_upper M (l_ne_dummy M _)] at hu
      rcases hu with ⟨_,he⟩ | ⟨a,ha,he⟩
      · exact (l_ne_u M _ _ he).elim
      · obtain ⟨eq,eq'⟩ := (l_eq_marker M _ _).mp he
        rwa [show q = a from eq.trans eq'.symm]
    · exact hm.mp hu
  · exact fun h => ⟨_,by simp [lower],hm.mpr h⟩

/-- An emitted upper constructor literal is rooted at a nontarget upper backbone and uses one of
its successor child vectors. -/
theorem mem_leF (x a) : Lit.leF x a ∈ Z ↔ ∃ q, x = u M q ∧ q ∉ M.target ∧
    a ∈ vectors (fun i => upper M (M.step q i)) (dummy M) := by
  simp only [system, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro (h | ⟨q,h⟩)
    · cases h
    · unfold row at h; split at h <;> simp_all [eq_comm]
  · rintro ⟨q,rfl,hq,ha⟩
    exact Or.inr ⟨q, by simp [row,hq,ha]⟩

private theorem mem_fLe (x a) : Lit.fLe a x ∈ Z ↔ ∃ q, x = l M q ∧
    (if q ∈ M.target then a = (fun _ => top M)
      else a ∈ vectors (fun i => lower M (M.step q i)) (dummy M)) := by
  simp only [system, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro (h | ⟨q,h⟩)
    · cases h
    · refine ⟨q,?_⟩
      unfold row at h
      split at h <;> simp_all [eq_comm]
  · rintro ⟨q,rfl,h⟩
    exact Or.inr ⟨q, by unfold row; split <;> simp_all⟩

/-- In the emitted system, the roots of upper and lower constructor literals are disjoint. -/
theorem separated : Separated Z := by
  intro x a b hl hu
  obtain ⟨p,rfl,_⟩ := (mem_fLe M _ _).mp hl
  obtain ⟨q,he,_⟩ := (mem_leF M _ _).mp hu
  exact l_ne_u M _ _ he

/-- The only emitted equation to a leaf equates the designated top variable to top. -/
theorem leaf_iff (b : Bool) (x) : leafLit b x ∈ Z ↔ b = true ∧ x = top M := by
  have noLeaf (q) : leafLit b x ∉ row M q := by
    cases b <;> unfold row <;> split <;> simp [leafLit]
  cases b <;> simp [system,leafLit] at noLeaf ⊢ <;> grind

/-- A one-letter upper trace starts at a nontarget upper backbone and reaches exactly an upper
choice of the successor state. -/
theorem upper_step (i : Fin n) (x z) : Trace Z false [i] x z ↔
    ∃ q, x = u M q ∧ q ∉ M.target ∧ z ∈ upper M (M.step q i) := by
  change (∃ a, Lit.leF x a ∈ Z ∧ a i = z) ↔ _
  simp only [mem_leF]
  constructor
  · rintro ⟨a,⟨q,rfl,hq,ha⟩,rfl⟩
    exact ⟨q,rfl,hq,(vectors_at _ _ (fun _ => upper_nonempty M _) ..).mp ⟨a,ha,rfl⟩⟩
  · rintro ⟨q,rfl,hq,hz⟩
    obtain ⟨a,ha,he⟩ := (vectors_at _ _ (fun _ => upper_nonempty M _) ..).mpr hz
    exact ⟨a,⟨q,rfl,hq,ha⟩,he⟩

/-- A one-letter lower trace follows the lower backbone to a successor choice, or reaches the
top variable immediately after a target. -/
theorem lower_step (i : Fin n) (x z) : Trace Z true [i] x z ↔
    ∃ q, x = l M q ∧ (if q ∈ M.target then z = top M else z ∈ lower M (M.step q i)) := by
  change (∃ a, Lit.fLe a x ∈ Z ∧ a i = z) ↔ _
  simp only [mem_fLe]
  constructor
  · rintro ⟨a,⟨q,rfl,ha⟩,rfl⟩
    refine ⟨q,rfl,?_⟩
    by_cases h : q ∈ M.target
    · rw [ite_eq_left h] at ha ⊢; rw [ha]
    · rw [ite_eq_right h] at ha ⊢
      exact (vectors_at (fun j => lower M (M.step q j)) _ (fun _ => by simp [lower]) ..).mp
        ⟨a,ha,rfl⟩
  · rintro ⟨q,rfl,hz⟩
    split at hz <;> rename_i h
    · exact ⟨fun _ => top M,⟨q,rfl,by simp [h]⟩,hz.symm⟩
    · obtain ⟨a,ha,he⟩ :=
        (vectors_at (fun j => lower M (M.step q j)) (dummy M) (fun _ => by simp [lower]) i z).mpr hz
      exact ⟨a,⟨q,rfl,by simp [h,ha]⟩,he⟩

/-- All proper prefixes of the word end outside the target. -/
def ProperFree (w : List (Fin n)) : Prop := ∀ j < w.length, M.dfa.eval (w.take j) ∉ M.target

/-- If every proper prefix of a word avoids targets, the same holds for each prefix of the word. -/
theorem free_take {w} (h : ProperFree M w) (i : ℕ) : ProperFree M (w.take i) := by
  intro j hj
  rw [List.length_take] at hj
  rw [List.take_take, Nat.min_eq_left (by omega)]
  exact h j (by omega)

/-- Every proper prefix of a word reaching a target in a stopping table avoids the target set. -/
theorem free_of_target {w} (ht : M.dfa.eval w ∈ M.target) : ProperFree M w := by
  intro j hj bad
  have hs : M.dfa.evalFrom M.sink (w.drop (j+1)) = M.sink := by
    generalize w.drop (j+1) = v
    induction v with
    | nil => rfl
    | cons a v ih => simpa [DFA.evalFrom_cons, StoppingTable.dfa, M.absorb] using ih
  have split := List.take_append_drop j w
  rw [List.drop_eq_getElem_cons hj] at split
  change M.dfa.evalFrom M.start w ∈ M.target at ht
  rw [← split, DFA.evalFrom_of_append, DFA.evalFrom_cons] at ht
  change M.dfa.evalFrom (M.step (M.dfa.eval (w.take j)) w[j]) (w.drop (j+1)) ∈ M.target at ht
  rw [M.stop _ bad,hs] at ht; exact M.sink_clear ht

/-- If a proper prefix reaches a target, the word has a first such prefix and a letter
immediately after it. -/
theorem first_target {w} (h : ¬ ProperFree M w) :
    ∃ p a, ProperFree M p ∧ M.dfa.eval p ∈ M.target ∧ p ++ [a] <+: w := by
  classical
  have hit : ∃ j, j < w.length ∧ M.dfa.eval (w.take j) ∈ M.target := by
    simpa [ProperFree] using h
  let j := Nat.find hit
  have hj := Nat.find_spec hit
  refine ⟨w.take j,w[j]'hj.1,?_,hj.2,?_⟩
  · intro i hi
    rw [List.length_take] at hi
    rw [List.take_take, Nat.min_eq_left (by omega)]
    exact fun bad => Nat.find_min hit (by omega : i < j) ⟨by omega,bad⟩
  · rw [← List.take_succ_eq_append_getElem hj.1]; exact List.take_prefix ..

/-- The initial upper mask contains the start backbone alone. A nonempty word uses the upper
choices of its endpoint. -/
def upperMask (w : List (Fin n)) :=
  if w = [] then [u M M.start] else upper M (M.dfa.eval w)

/-- The upper mask contains the backbone at `q` exactly when the word ends at `q` and `q` is
outside the target. -/
theorem active_upper (w : List (Fin n)) (q) :
    u M q ∈ upperMask M w ↔ q = M.dfa.eval w ∧ M.dfa.eval w ∉ M.target := by
  cases w with
  | nil => simp [upperMask, StoppingTable.dfa, M.start_clear]
  | cons a w => simp [upperMask,u_mem_upper]

/-- Until a word passes its first target, the upper traces give its upper mask and the lower
traces give the lower choices of its endpoint. -/
theorem masks (w : List (Fin n)) (h : ProperFree M w) :
    (∀ z, Trace Z false w (u M M.start) z ↔ z ∈ upperMask M w) ∧
    (∀ z, Trace Z true w (l M M.start) z ↔ z ∈ lower M (M.dfa.eval w)) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp [Trace, upperMask, lower, marker, StoppingTable.dfa, eq_comm]
  | append_singleton w a ih =>
    have hw : ProperFree M w := by simpa using free_take M h w.length
    have nt : M.dfa.eval w ∉ M.target := by simpa using h w.length (by simp)
    obtain ⟨hu,hl⟩ := ih hw
    constructor
    · intro z
      rw [trace_append, upperMask, ite_eq_right (by simp), DFA.eval_append_singleton]
      simp only [hu, upper_step]
      constructor
      · rintro ⟨_,hu,q,rfl,hq,hz⟩
        rw [((active_upper M w q).mp hu).1] at hz
        exact hz
      · intro hz
        exact ⟨_,(active_upper M w _).mpr ⟨rfl,nt⟩,_,rfl,nt,hz⟩
    · intro z
      rw [trace_append, DFA.eval_append_singleton]
      simp only [hl, lower_step]
      constructor
      · rintro ⟨_,hl,q,rfl,hz⟩
        rw [(l_mem_lower M ..).mp hl, ite_eq_right nt] at hz
        exact hz
      · intro hz
        exact ⟨_,(l_mem_lower M ..).mpr rfl,_,rfl,by rw [ite_eq_right nt]; exact hz⟩

/-- The first letter after a target extends a lower trace from the initial lower backbone to the
top variable. -/
theorem reaches_top {w} (h : ProperFree M w) (ht : M.dfa.eval w ∈ M.target) (a : Fin n) :
    Trace Z true (w ++ [a]) (l M M.start) (top M) := by
  apply (trace_append ..).mpr
  refine ⟨l M (M.dfa.eval w), ((masks M w h).2 _).mpr ((l_mem_lower M ..).mpr rfl), ?_⟩
  exact (lower_step M ..).mpr ⟨_,rfl,by simp [ht]⟩

/-- At positive arity the variables with an upper constructor literal are exactly the nontarget
upper backbones. -/
theorem upper_node (hn : 0 < n) (x) : (∃ a, nodeLit false x a ∈ Z) ↔
    ∃ q, x = u M q ∧ q ∉ M.target := by
  constructor
  · rintro ⟨a,h⟩
    obtain ⟨q,hq,ht,_⟩ := (mem_leF M x a).mp h
    exact ⟨q,hq,ht⟩
  · rintro ⟨q,rfl,ht⟩
    let i : Fin n := ⟨0,hn⟩
    obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _ (upper_nonempty M (M.step q i))
    obtain ⟨a,ha,_⟩ := (upper_step M i _ z).mpr ⟨q,rfl,ht,hz⟩
    exact ⟨a,ha⟩

/-- At positive arity every lower backbone has a lower constructor literal, including at a
target. -/
theorem lower_node (hn : 0 < n) (q) : ∃ a, nodeLit true (l M q) a ∈ Z := by
  let i : Fin n := ⟨0,hn⟩
  by_cases ht : q ∈ M.target
  · exact ⟨_,(mem_fLe M _ _).mpr ⟨q,rfl,by rw [ite_eq_left ht]⟩⟩
  · have ht' := (lower_step M i (l M q) (l M (M.step q i))).mpr ⟨q,rfl,by simp [ht,lower]⟩
    obtain ⟨a,ha,_⟩ := ht'; exact ⟨a,ha⟩

end DeciNSSE.Complexity.Tiling.Emitter
