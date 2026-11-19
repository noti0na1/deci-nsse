import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Infix
import DeciNSSE.Holes.Columns

/-! # Erasing loops on a shared path

Each retained letter stores the gap immediately preceding it. Erasure is
valid when that gap fixes the incoming core. Whole prefix actions determine
gaps that are valid for every entry at once.

## Main declarations

- `ActionBound` counts word actions.
- `Path.exists_compression` shortens one segment with its last letter pinned.
- `Path.label_cut` lifts a cut to the end of its last retained letter.
-/

namespace DeciNSSE.Shortening
open CoAlignment LetteredHierarchy BoundedDepth
variable {Γ C : Type*}

/-- At most `K` distinct functions on the cores are induced by words. -/
def ActionBound (D : Lettered Γ C) (K : ℕ) : Prop :=
  ∃ A : Finset (C → C), A.card ≤ K ∧ ∀ w : List Γ, (fun q => kst D q w) ∈ A

/-- Enlarging the allowance preserves an action bound. -/
theorem ActionBound.mono {D : Lettered Γ C} {K K' : ℕ} (h : ActionBound D K) (hle : K ≤ K') :
    ActionBound D K' := by
  obtain ⟨A, ha, hw⟩ := h
  exact ⟨A, ha.trans hle, hw⟩

/-- Counting all functions on the cores bounds every transition monoid. -/
theorem actionBound_card [Fintype C] (D : Lettered Γ C) :
    ActionBound D (Fintype.card C ^ Fintype.card C) := by
  classical
  exact ⟨Finset.univ, by simp, fun _ => Finset.mem_univ _⟩

namespace Path

/-- A gap and the retained letter immediately after it. -/
abbrev Chunk (Γ : Type*) := List Γ × Γ

/-- Reconstruct the original word by inserting each erased gap before its retained letter. -/
def original (p : List (Chunk Γ)) := p.flatMap fun (u, a) => u ++ [a]

/-- Read the retained letter of each chunk in order. -/
def letters (p : List (Chunk Γ)) := p.map Prod.snd

/-- Reconstructing a concatenation of paths concatenates their original words. -/
@[simp] theorem original_append (p r : List (Chunk Γ)) :
    original (p ++ r) = original p ++ original r := List.flatMap_append

/-- The retained letters of two consecutive paths concatenate in the same order. -/
@[simp] theorem letters_append (p r : List (Chunk Γ)) :
    letters (p ++ r) = letters p ++ letters r := List.map_append

/-- Each chunk contributes one retained letter. -/
@[simp] theorem length_letters (p : List (Chunk Γ)) : (letters p).length = p.length :=
  List.length_map _

/-- The retained word is empty exactly when the path has no chunks. -/
@[simp] theorem letters_nil_iff (p : List (Chunk Γ)) : letters p = [] ↔ p = [] :=
  List.map_eq_nil_iff

/-- The retained letters form a subsequence of the original word. -/
theorem sublist (p : List (Chunk Γ)) : (letters p).Sublist (original p) := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    exact (List.sublist_append_right z.1 [z.2]).append ih

/-- The original and retained words have the same last letter, including the empty case. -/
theorem last_eq (p : List (Chunk Γ)) : (letters p).getLast? = (original p).getLast? := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p z _ => simp [letters, original, ← List.append_assoc]

/-- Every erased gap is a loop at the point where it is erased. -/
def Valid (D : Lettered Γ C) (q : C) : List (Chunk Γ) → Prop
  | [] => True
  | (g, a) :: p => kst D q g = q ∧ Valid D (D.κ a q) p

variable {D : Lettered Γ C}

/-- Two consecutive paths are valid when the first is valid at entry and the second is valid at
the first path's exit. -/
theorem valid_append {p r : List (Chunk Γ)} {q : C} :
    Valid D q (p ++ r) ↔ Valid D q p ∧ Valid D (kst D q (letters p)) r := by
  induction p generalizing q with
  | nil => simp [Valid, letters]
  | cons z p ih => simp [Valid, letters, ih, and_assoc]

/-- Erasing the gaps of a valid path preserves the exit core. -/
theorem eval_eq {p : List (Chunk Γ)} {q : C} (h : Valid D q p) :
    kst D q (original p) = kst D q (letters p) := by
  induction p generalizing q with
  | nil => rfl
  | cons z p ih =>
    simp only [original, List.flatMap_cons, List.append_assoc, List.singleton_append,
      kst_append, h.1, kst_cons, letters, List.map_cons]
    exact ih h.2

/-- Remove the longest initial loop on the current action. The remaining
proper prefix actions avoid that action, so recursion spends one fewer state. -/
private theorem compress_to_last (D : Lettered Γ C) (A : Finset (C → C))
    (F : C → C) (u : List Γ) (z : Γ)
    (visit : ∀ v, v <+: u → (fun q => kst D (F q) v) ∈ A) :
    ∃ p : List (Chunk Γ), original p = u ++ [z] ∧
      p.length ≤ A.card ∧ ∀ q, Valid D (F q) p := by
  classical
  let loops := u.inits.toFinset.filter fun v => ∀ q, kst D (F q) v = F q
  have he : [] ∈ loops := by simp [loops]
  obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image loops List.length ⟨_, he⟩
  obtain ⟨hgu, hgF⟩ : g <+: u ∧ ∀ q, kst D (F q) g = F q := by
    simpa [loops] using hg
  have hF : F ∈ A := by simpa using visit [] (List.nil_prefix)
  obtain ⟨r, hr⟩ := hgu
  cases r with
  | nil =>
    refine ⟨[(g,z)], by simpa [original] using congrArg (· ++ [z]) hr, ?_,
      fun q => ⟨hgF q, trivial⟩⟩
    simpa using Finset.card_pos.mpr ⟨_, hF⟩
  | cons a r =>
    have hvis (v) (hv : v <+: r) :
        (fun q => kst D (D.κ a (F q)) v) ∈ A.erase F := by
      have hp : g ++ a :: v <+: u := by
        obtain ⟨s, hs⟩ := hv
        exact ⟨s, by simp [List.append_assoc, hs, hr]⟩
      have hact : (fun q => kst D (F q) (g ++ a :: v)) =
          (fun q => kst D (D.κ a (F q)) v) := by funext q; rw [kst_append, hgF, kst_cons]
      rw [← hact, Finset.mem_erase]
      refine ⟨fun h => ?_, visit _ hp⟩
      have hm : g ++ a :: v ∈ loops := by
        simpa [loops, funext_iff] using And.intro hp (congrFun h)
      have := hmax _ hm
      simp at this
    obtain ⟨p, htext, hlen, hvalid⟩ :=
      compress_to_last D (A.erase F) (fun q => D.κ a (F q)) r z hvis
    refine ⟨(g,a) :: p, ?_, ?_, fun q => ⟨hgF q, hvalid q⟩⟩
    · change (g ++ [a]) ++ original p = _
      simp [htext, ← hr, List.append_assoc]
    · rw [Finset.card_erase_of_mem hF] at hlen
      have := Finset.card_pos.mpr ⟨_, hF⟩
      simp; omega
termination_by A.card
decreasing_by
  classical
  exact Finset.card_erase_lt_of_mem hF

/-- Every segment has a representation by at most `K` chunks valid at every entering core, where
`K` bounds word actions. -/
theorem exists_compression (D : Lettered Γ C) {K : ℕ} (hK : ActionBound D K) (s : List Γ) :
    ∃ p : List (Chunk Γ), original p = s ∧ p.length ≤ K ∧ ∀ q, Valid D q p := by
  rcases List.eq_nil_or_concat s with rfl | ⟨u, z, rfl⟩
  · exact ⟨[], rfl, Nat.zero_le _, fun _ => trivial⟩
  obtain ⟨A, hcard, ha⟩ := hK
  obtain ⟨p, hp, hl, hv⟩ := compress_to_last D A id u z (fun v _ => ha v)
  exact ⟨p, by simpa [List.concat_eq_append] using hp, hl.trans hcard, hv⟩

private def entry (D : Lettered Γ C) (ℓ : Γ) : Option C → C
  | none => D.start
  | some q => D.κ ℓ q

private theorem fcore_eq (D : Lettered Γ C) (ℓ : Γ) (q : Option C) (s : List Γ) :
    fcore D ℓ q s = kst D (entry D ℓ q) s := by cases q <;> rfl

/-- A path valid at every entry gives the same shifted-block exit before and after erasure. -/
theorem exit_eq (ℓ : Γ) (q : Option C) {p : List (Chunk Γ)} (h : ∀ c, Valid D c p) :
    fcore D ℓ q (letters p) = fcore D ℓ q (original p) := by
  rw [fcore_eq, fcore_eq, eval_eq (h _)]

private theorem zlab_prefix (D : Lettered Γ C) (ℓ : Γ) (q : Option C) (p r : List Γ) :
    zlab D ℓ q (p ++ r) p.length = zlab D ℓ q p p.length := by
  cases q with
  | none => exact labFrom_append_le D _ _ _ le_rfl
  | some q => exact labFrom_append_le D _ (ℓ :: p) r (p := p.length + 1) (by simp)

/-- At a cut between chunks the retained block and the original block carry the same shifted
label, including at the initial cut. -/
theorem label_cut (ℓ : Γ) (q : Option C) (p r : List (Chunk Γ))
    (h : ∀ c, Valid D c (p ++ r)) :
    zlab D ℓ q (letters (p ++ r)) (letters p).length =
      zlab D ℓ q (original (p ++ r)) (original p).length := by
  rw [letters_append, original_append, zlab_prefix, zlab_prefix]
  obtain rfl | ⟨p, ⟨g,a⟩, rfl⟩ := List.eq_nil_or_concat p
  · rfl
  · have hv := (valid_append.mp (h (entry D ℓ q))).1
    rw [List.concat_eq_append] at hv
    obtain ⟨hv, hg, _⟩ := valid_append.mp hv
    simp only [List.concat_eq_append, letters_append, original_append]
    change zlab D ℓ q (letters p ++ [a]) (letters p ++ [a]).length =
      zlab D ℓ q (original p ++ (g ++ [a] ++ [])) (original p ++ (g ++ [a] ++ [])).length
    simp only [List.append_nil, ← List.append_assoc]
    rw [List.length_append (as := letters p), List.length_append (as := original p ++ g)]
    simp only [List.length_singleton]
    rw [zlab_snoc_last, zlab_snoc_last, fcore_eq, fcore_eq, kst_append, eval_eq hv, hg]

end Path
end DeciNSSE.Shortening
