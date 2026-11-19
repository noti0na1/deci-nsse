import DeciNSSE.Shortening.Blocks
import DeciNSSE.Holes.Depth

/-! # Descent through the canonical hierarchy

## Main declarations

- `descentBound` bounds the length after expanding a shortened unary hole.
- `exists_short_hole` uses the markers and depth of the given word.
-/

namespace DeciNSSE.Shortening
open CoAlignment LetteredHierarchy HierarchyDepth

/-- Length allowance after expanding through `d` levels. -/
def descentBound (N d K : ℕ) := (N + d) * (1 + 2 * K) ^ (d * (d + 1) / 2)

/-- Depth and the action allowance enter monotonically. -/
theorem descentBound_mono {N d d' K K' : ℕ} (hd : d ≤ d') (hK : K ≤ K') :
    descentBound N d K ≤ descentBound N d' K' := by
  unfold descentBound
  gcongr
  omega

section Expansion
variable {Γ : Type*} [DecidableEq Γ] {B : Finset (List Γ)}

private theorem length_le_edges {x : List Γ} (hx : x ∈ B) : x.length ≤ (trieEdges B).card := by
  let suffix (i : Fin x.length) : trieEdges B :=
    ⟨x.drop i, mem_trieEdges.mpr ⟨by simp [i.isLt], x, hx, List.drop_suffix ..⟩⟩
  have inj : Function.Injective suffix := by
    intro i j h
    have hl := congrArg (fun z : trieEdges B => z.val.length) h
    simp [suffix] at hl
    exact Fin.ext (by omega)
  simpa using Fintype.card_le_of_injective suffix inj

/-- A block has one distinct nonempty suffix for each letter position. -/
theorem length_le_card_trieEdges {x : List Γ} (hx : x ∈ B) : x.length ≤ (trieEdges B).card :=
  length_le_edges hx

/-- Each letter in the dictionary is the head of a nonempty suffix. -/
theorem support_le_card_trieEdges (B : Finset (List Γ)) :
    (B.biUnion List.toFinset).card ≤ (trieEdges B).card := by
  classical
  by_cases inhabited : Nonempty Γ
  · obtain ⟨d⟩ := inhabited
    have sub : B.biUnion List.toFinset ⊆ (trieEdges B).image (fun w => w.headD d) := by
      intro a ha
      obtain ⟨x, hx, h⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨p, s, eq⟩ := List.mem_iff_append.mp (List.mem_toFinset.mp h)
      exact Finset.mem_image.mpr
        ⟨a :: s, mem_trieEdges.mpr ⟨by simp, x, hx, p, eq.symm⟩, rfl⟩
    exact (Finset.card_le_card sub).trans Finset.card_image_le
  · have empty : B.biUnion List.toFinset = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun a => (inhabited ⟨a⟩).elim
    simp [empty]

private theorem expand_support (ℓ : Γ) {v : List (List Γ)} (hv : ∀ x ∈ v, x ∈ B) :
    (expand ℓ v).toFinset.card ≤ (trieEdges B).card + 1 := by
  have sub : (expand ℓ v).toFinset ⊆ insert ℓ (B.biUnion List.toFinset) := by
    intro a ha
    obtain ⟨x, hx, h⟩ := mem_expand.mp (List.mem_toFinset.mp ha)
    rcases List.mem_append.mp h with h | h
    · exact Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨x, hv _ hx, List.mem_toFinset.mpr h⟩)
    · rw [List.mem_singleton.mp h]; exact Finset.mem_insert_self ..
  exact (Finset.card_le_card sub).trans
    ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (support_le_card_trieEdges B) _))

private theorem expand_length (ℓ : Γ) (v : List (List Γ)) (hv : ∀ x ∈ v, x ∈ B) :
    (expand ℓ v).length ≤ v.length * ((trieEdges B).card + 1) := by
  induction v with
  | nil => simp
  | cons x v ih =>
    have h := length_le_card_trieEdges (hv _ List.mem_cons_self)
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
    simp only [expand_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

end Expansion

open BoundedDepth

/-- Expand into the original level. Its new support lies in the original
dictionary because each replacement block is a subsequence of an old block. -/
private theorem descend_one {Γ C : Type*} [DecidableEq Γ] [Inhabited Γ]
    (D : Lettered Γ C) {w : List Γ} (hw : w ≠ []) (j : ℕ) (v : List (Alph Γ (j + 1)))
    (hv : (tower D (markOf w) (j + 1)).IsHole v) (sub : ∀ x ∈ v, x ∈ hierOf w (j + 1))
    {K : ℕ} (hK : ActionBound (tower D (markOf w) j) K) :
    ∃ u : List (Alph Γ j), (tower D (markOf w) j).IsHole u ∧
      (∀ a ∈ u, a ∈ hierOf w j) ∧
      u.toFinset.card ≤ (1 + 2 * K) * v.toFinset.card ∧
      u.length ≤ v.length * ((1 + 2 * K) * v.toFinset.card) := by
  classical
  let B : Finset (List (Alph Γ j)) := v.toFinset
  let ℓ := markOf w j
  obtain ⟨f, _, hf, hcost, hh⟩ := exists_shortening (tower D (markOf w) j) ℓ B hK
  have small := hh v (fun _ h => List.mem_toFinset.mpr h) hv
  have pull {X} (hx : X ∈ v.map f) : ∃ Y ∈ v, X = f Y := by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ⟨y, hy, rfl⟩
  have ha : ∀ X ∈ v.map f, ℓ ∉ X := by
    intro X hx
    obtain ⟨Y, hy, rfl⟩ := pull hx
    exact fun h => avoid_hierOf j _ (sub _ hy) ((hf _ (List.mem_toFinset.mpr hy)).subset h)
  have hB : 0 < B.card := by
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ hv.ne_nil
    exact Finset.card_pos.mpr ⟨x, List.mem_toFinset.mpr hx⟩
  have allowance : (trieEdges (B.image f)).card + 1 ≤ (1 + 2 * K) * B.card := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_right_comm 2 K B.card]
    omega
  have memB (X) (hx : X ∈ v.map f) : X ∈ B.image f := by
    obtain ⟨Y, hy, rfl⟩ := pull hx
    exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hy)
  refine ⟨expand ℓ (v.map f), (isHole_der_iff _ _ _ small.ne_nil ha).mp small, ?_,
    (expand_support ℓ memB).trans allowance, ?_⟩
  · intro a ha
    obtain ⟨X, hx, ha⟩ := mem_expand.mp ha
    obtain ⟨Y, hy, rfl⟩ := pull hx
    rcases List.mem_append.mp ha with h | h
    · exact mem_lower_dictionary hw (sub _ hy) ((hf _ (List.mem_toFinset.mpr hy)).subset h)
    · rw [List.mem_singleton.mp h]; exact markOf_mem hw j
  · simpa using (expand_length ℓ _ memB).trans (Nat.mul_le_mul_left _ allowance)

private theorem triangular_succ (r : ℕ) :
    (r + 1) * (r + 1 + 1) / 2 = r * (r + 1) / 2 + (r + 1) := by
  rw [show (r + 1) * (r + 1 + 1) = r * (r + 1) + (r + 1) * 2 by ring]
  exact Nat.add_mul_div_right _ _ (by decide)

/-- Shorten a hole while retaining the final predicate of the same monitor. -/
theorem exists_short_hole {Γ C : Type*} [DecidableEq Γ] [Inhabited Γ] [Fintype C]
    (D : Lettered Γ C) {w : List Γ} (hw : D.IsHole w) {K : ℕ}
    (hK : ∀ j < depth w, ActionBound (tower D (markOf w) j) K) :
    ∃ u, D.IsHole u ∧ u.length ≤ descentBound (Fintype.card C) (depth w) K := by
  classical
  let d := depth w
  let b := 1 + 2 * K
  let N := Fintype.card C
  have go (j r : ℕ) (sum : j + r = d) (v : List (Alph Γ j))
      (hv : (tower D (markOf w) j).IsHole v) (sub : ∀ x ∈ v, x ∈ hierOf w j)
      (hs : v.toFinset.card ≤ b ^ r) (hl : v.length ≤ (N + d) * b ^ (r * (r + 1) / 2)) :
      ∃ u, D.IsHole u ∧ u.length ≤ descentBound N d K := by
    induction j generalizing r with
    | zero =>
      have hr : r = d := by omega
      exact ⟨v, hv, hr ▸ hl⟩
    | succ j ih =>
      obtain ⟨u, hu, hsub, hsize, hlen⟩ := descend_one D hw.ne_nil j v hv sub (hK _ (by omega))
      have hb : b * v.toFinset.card ≤ b ^ (r + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
        exact Nat.mul_le_mul_right _ hs
      refine ih (r + 1) (by omega) u hu hsub (hsize.trans hb) ?_
      rw [triangular_succ, pow_add, ← Nat.mul_assoc]
      exact hlen.trans (Nat.mul_le_mul hl hb)
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hierOf_ne_nil hw.ne_nil d)
  have hr : hierOf w d = List.replicate (hierOf w d).length x :=
    List.eq_replicate_iff.mpr ⟨rfl, fun a ha => isUnary_depth w a ha x hx⟩
  have hh := (isHole_hierOf_iff hw.ne_nil D d).mpr hw
  obtain ⟨m, _, hm, hmH⟩ := (exists_unary_hole_iff (tower D (markOf w) d) x).mp
    ⟨(hierOf w d).length, by rw [← hr]; exact hh⟩
  rw [card_cores d] at hm
  refine go d 0 (by omega) _ hmH (fun a ha => List.eq_of_mem_replicate ha ▸ hx) ?_ (by simpa)
  rw [pow_zero]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact (List.eq_of_mem_replicate (List.mem_toFinset.mp ha)).trans
    (List.eq_of_mem_replicate (List.mem_toFinset.mp hb)).symm

end DeciNSSE.Shortening
