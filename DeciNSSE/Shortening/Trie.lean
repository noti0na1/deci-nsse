import DeciNSSE.Shortening.Paths

/-! # Dictionaries of shared suffixes

At a fork, split the dictionary into two groups with different last letters.
The common suffix above the fork is one segment, even when many blocks use
it. An endpoint at a fork has the empty remaining path.

## Main declarations

- `trieEdges` counts the distinct nonempty suffixes.
- `Path.Coherent` says that a retained suffix determines its decorated path.
- `Path.exists_dictionary` constructs simultaneously valid paths for a dictionary.
-/

namespace DeciNSSE.Shortening
open CoAlignment LetteredHierarchy
open scoped List
variable {Γ C : Type*}

/-- Each nonroot trie vertex names the edge from its parent. -/
def trieEdges [DecidableEq Γ] (B : Finset (List Γ)) : Finset (List Γ) :=
  B.biUnion fun w => w.tails.toFinset.erase []

/-- A trie edge is named by a nonempty suffix of some block in the dictionary. -/
theorem mem_trieEdges [DecidableEq Γ] {B : Finset (List Γ)} {s : List Γ} :
    s ∈ trieEdges B ↔ s ≠ [] ∧ ∃ w ∈ B, s <:+ w := by
  simp [trieEdges, List.mem_tails]
  grind

private theorem suffix_split {α : Type*} {p x z : List α} (h : p <:+ x ++ z) :
    p <:+ z ∨ ∃ a, a ≠ [] ∧ a <:+ x ∧ p = a ++ z := by
  by_cases hl : p.length ≤ z.length
  · exact Or.inl (List.suffix_of_suffix_length_le h (List.suffix_append x z) hl)
  · obtain ⟨a, ha⟩ := List.suffix_of_suffix_length_le (List.suffix_append x z) h (by omega)
    subst p
    exact Or.inr ⟨a, by rintro rfl; simp at hl, List.suffix_append_self_iff.mp h, rfl⟩

private theorem card_edges_append [DecidableEq Γ] (B : Finset (List Γ)) (z : List Γ) :
    (trieEdges (B.image (· ++ z))).card ≤ (trieEdges B).card + z.length := by
  let E := z.tails.toFinset.erase []
  have he : E.card ≤ z.length := by
    have hn : [] ∈ z.tails.toFinset := by simp [List.mem_tails]
    have hb := z.tails.toFinset_card_le
    rw [List.length_tails] at hb
    dsimp [E]
    rw [Finset.card_erase_of_mem hn]
    omega
  have hsub : trieEdges (B.image (· ++ z)) ⊆ (trieEdges B).image (· ++ z) ∪ E := by
    intro p hp
    obtain ⟨hn, w, hw, hs⟩ := mem_trieEdges.mp hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    rcases suffix_split hs with short | ⟨a, ha, inside, rfl⟩
    · exact Finset.mem_union_right _ (by simpa [E, List.mem_tails] using And.intro hn short)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨a, mem_trieEdges.mpr ⟨ha, x, hx, inside⟩, rfl⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le he))

private theorem suffix_induction [DecidableEq Γ] (P : Finset (List Γ) → Prop)
    (single : ∀ x, P {x})
    (fork : ∀ A B : Finset (List Γ), ∀ s : List Γ, A.Nonempty → B.Nonempty →
      (∀ x ∈ A, ∀ y ∈ B, x.getLast? ≠ y.getLast?) →
        P A → P B → P ((A ∪ B).image (· ++ s)))
    (F : Finset (List Γ)) (hne : F.Nonempty) : P F := by
  classical
  obtain ⟨x, hx⟩ := hne
  by_cases heq : F = {x}
  · rw [heq]; exact single x
  let suffixes := x.tails.toFinset.filter fun s => ∀ y ∈ F, s <:+ y
  have hnil : [] ∈ suffixes := by simp [suffixes, List.mem_tails]
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image suffixes List.length ⟨_, hnil⟩
  have hcommon := (Finset.mem_filter.mp hs).2
  let strip (y : List Γ) := y.take (y.length - s.length)
  have restore (y) (hy : y ∈ F) : strip y ++ s = y := by
    obtain ⟨a, rfl⟩ := hcommon y hy
    simp [strip]
  let G := F.image strip
  have hG (a) : a ∈ G ↔ a ++ s ∈ F := by
    constructor
    · rintro ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      rwa [restore _ hy]
    · intro ha
      exact Finset.mem_image.mpr ⟨_, ha, by simp [strip]⟩
  have hF : G.image (· ++ s) = F := by
    ext y
    constructor
    · rintro hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      exact (hG _).mp ha
    · intro hy
      exact Finset.mem_image.mpr ⟨strip y, Finset.mem_image_of_mem _ hy, restore y hy⟩
  have diff : ∃ a ∈ G, ∃ b ∈ G, a.getLast? ≠ b.getLast? := by
    by_contra! same
    have hxg : strip x ∈ G := Finset.mem_image_of_mem _ hx
    cases hlast : (strip x).getLast? with
    | none =>
      have hx0 : strip x = [] := List.getLast?_eq_none_iff.mp hlast
      apply heq
      ext y
      simp only [Finset.mem_singleton]
      refine ⟨fun hy => ?_, fun h => h ▸ hx⟩
      have hz := same (strip y) (Finset.mem_image_of_mem _ hy) _ hxg
      rw [hlast, List.getLast?_eq_none_iff] at hz
      rw [← restore y hy, ← restore x hx, hx0, hz]
    | some c =>
      have hall (y) (hy : y ∈ F) : c :: s <:+ y := by
        have hz := (same (strip y) (Finset.mem_image_of_mem _ hy) _ hxg).trans hlast
        obtain ⟨a, ha⟩ := List.getLast?_eq_some_iff.mp hz
        exact ⟨a, by conv_rhs => rw [← restore y hy, ha]; simp [List.append_assoc]⟩
      have hm : c :: s ∈ suffixes := by
        simp only [suffixes, Finset.mem_filter, List.mem_toFinset, List.mem_tails]
        exact ⟨hall x hx, hall⟩
      have := hmax _ hm
      simp at this
  obtain ⟨a, ha, b, hb, hab⟩ := diff
  let A := G.filter fun y => y.getLast? = a.getLast?
  let B := G.filter fun y => ¬ y.getLast? = a.getLast?
  have hA : A.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  have hB : B.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, Ne.symm hab⟩⟩
  have hun : A ∪ B = G := Finset.filter_union_filter_not_eq ..
  have hc : A.card + B.card = G.card := Finset.card_filter_add_card_filter_not ..
  have hl : G.card ≤ F.card := Finset.card_image_le
  have hsep : ∀ x ∈ A, ∀ y ∈ B, x.getLast? ≠ y.getLast? :=
    fun _ hx _ hy h => (Finset.mem_filter.mp hy).2 (h.symm.trans (Finset.mem_filter.mp hx).2)
  have ltA : A.card < F.card := by have := hB.card_pos; omega
  have ltB : B.card < F.card := by have := hA.card_pos; omega
  rw [← hF, ← hun]
  exact fork A B s hA hB hsep (suffix_induction P single fork A hA)
    (suffix_induction P single fork B hB)
termination_by F.card
decreasing_by all_goals first | exact ltA | exact ltB

namespace Path

/-- Equal visible suffixes lift to identical lists of gaps and retained letters. -/
def Coherent (F : Finset (List (Chunk Γ))) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, ∀ p q, p <:+ x → q <:+ y → letters p = letters q → p = q

private theorem suffix_unique {α : Type*} {p q z : List α}
    (hp : p <:+ z) (hq : q <:+ z) (hl : p.length = q.length) : p = q :=
  (List.suffix_of_suffix_length_le hp hq hl.le).eq_of_length hl

private theorem coherent_append [DecidableEq Γ] {F : Finset (List (Chunk Γ))} (hc : Coherent F)
    (z : List (Chunk Γ)) : Coherent (F.image (· ++ z)) := by
  intro x hx y hy p q hp hq he
  obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hy
  have hl : p.length = q.length := by simpa using congrArg List.length he
  by_cases hle : p.length ≤ z.length
  · exact suffix_unique (List.suffix_of_suffix_length_le hp (List.suffix_append x z) hle)
      (List.suffix_of_suffix_length_le hq (List.suffix_append y z) (by omega)) hl
  · obtain ⟨a, rfl⟩ := List.suffix_of_suffix_length_le (List.suffix_append x z) hp (by omega)
    obtain ⟨b, rfl⟩ := List.suffix_of_suffix_length_le (List.suffix_append y z) hq (by omega)
    simp only [letters_append, List.append_cancel_right_eq] at he
    rw [hc _ hxF _ hyF _ _ (List.suffix_append_self_iff.mp hp)
      (List.suffix_append_self_iff.mp hq) he]

private theorem coherent_union [DecidableEq Γ] {F G : Finset (List (Chunk Γ))}
    (hf : Coherent F) (hg : Coherent G)
    (sep : ∀ x ∈ F, ∀ y ∈ G, (letters x).getLast? ≠ (letters y).getLast?) :
    Coherent (F ∪ G) := by
  have cross {x y p q : List (Chunk Γ)} (hx : x ∈ F) (hy : y ∈ G)
      (hp : p <:+ x) (hq : q <:+ y) (he : letters p = letters q) : p = q := by
    by_cases hn : letters p = []
    · rw [(letters_nil_iff _).mp hn, (letters_nil_iff _).mp (he.symm.trans hn)]
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact False.elim (sep _ hx _ hy (by
      rw [letters_append, letters_append, List.getLast?_append_of_ne_nil _ hn,
        List.getLast?_append_of_ne_nil _ (he ▸ hn), he]))
  intro x hx y hy p q hp hq he
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact hf _ hx _ hy _ _ hp hq he
  · exact cross hx hy hp hq he
  · exact (cross hy hx hq hp he.symm).symm
  · exact hg _ hx _ hy _ _ hp hq he

/-- A dictionary of decorated paths with coherent suffixes. The extra `K` on
the left reserves the single segment above a binary fork. -/
theorem exists_dictionary [DecidableEq Γ] (D : Lettered Γ C) {K : ℕ} (hK : ActionBound D K)
    (B : Finset (List Γ)) (hne : B.Nonempty) :
    ∃ F : Finset (List (Chunk Γ)), F.image original = B ∧ Coherent F ∧
      (∀ p ∈ F, ∀ q, Valid D q p) ∧
      (trieEdges (F.image letters)).card + K ≤ 2 * B.card * K := by
  classical
  refine suffix_induction (fun B =>
    ∃ F : Finset (List (Chunk Γ)), F.image original = B ∧ Coherent F ∧
      (∀ p ∈ F, ∀ q, Valid D q p) ∧
        (trieEdges (F.image letters)).card + K ≤ 2 * B.card * K) ?_ ?_ B hne
  · intro x
    obtain ⟨p, hp, hl, hv⟩ := exists_compression D hK x
    refine ⟨{p}, by simp [hp], ?_, by simpa using hv, ?_⟩
    · intro x hx y hy a b ha hb he
      simp only [Finset.mem_singleton] at hx hy
      subst x; subst y
      exact suffix_unique ha hb (by simpa using congrArg List.length he)
    · have bound := card_edges_append ({[]} : Finset (List Γ)) (letters p)
      simp [trieEdges] at bound ⊢
      omega
  · intro A B s hA hB sep ihA ihB
    obtain ⟨F, hF, hf, vf, bf⟩ := ihA
    obtain ⟨G, hG, hg, vg, bg⟩ := ihB
    obtain ⟨z, hz, hl, vz⟩ := exists_compression D hK s
    refine ⟨(F ∪ G).image (· ++ z), ?_, coherent_append (coherent_union hf hg ?_) z, ?_, ?_⟩
    · simp only [Finset.image_image, Function.comp_def, original_append, hz, ← hF,
        ← hG, ← Finset.image_union]
    · intro x hx y hy
      rw [last_eq, last_eq]
      apply sep
      · rw [← hF]; exact Finset.mem_image_of_mem _ hx
      · rw [← hG]; exact Finset.mem_image_of_mem _ hy
    · intro p hp q
      obtain ⟨p, hpF, rfl⟩ := Finset.mem_image.mp hp
      exact valid_append.mpr ⟨(Finset.mem_union.mp hpF).elim
        (fun h => vf _ h _) (fun h => vg _ h _),
        vz _⟩
    · have hd : Disjoint A B := Finset.disjoint_left.mpr (fun _ h₁ h₂ => sep _ h₁ _ h₂ rfl)
      have hadd : ((A ∪ B).image (· ++ s)).card = A.card + B.card := by
        rw [Finset.card_image_of_injective _ (fun _ _ h => List.append_cancel_right h),
          Finset.card_union_of_disjoint hd]
      have hmap : (((F ∪ G).image (· ++ z)).image letters) =
          ((F.image letters ∪ G.image letters).image (· ++ letters z)) := by
        simp only [← Finset.image_union, Finset.image_image, Function.comp_def, letters_append]
      have hu : trieEdges (F.image letters ∪ G.image letters) =
          trieEdges (F.image letters) ∪ trieEdges (G.image letters) := by
        ext p; simp [mem_trieEdges]; grind
      rw [hadd, hmap, Nat.mul_add, Nat.add_mul]
      have h := card_edges_append (F.image letters ∪ G.image letters) (letters z)
      rw [hu, length_letters] at h
      have hu' := Finset.card_union_le (s := trieEdges (F.image letters))
        (t := trieEdges (G.image letters))
      omega

end Path
end DeciNSSE.Shortening
