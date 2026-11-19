import DeciNSSE.Shortening.Trie

/-! # Shortening a dictionary of blocks

A nonempty suffix names one edge of the trie of reversed blocks. Counting
these suffixes charges shared material just once.

## Main declarations

- `exists_shortening` renames a finite dictionary simultaneously for every
  derived hole over that dictionary.
-/

namespace DeciNSSE.Shortening
open CoAlignment LetteredHierarchy
variable {Γ C : Type*}

open Path BoundedDepth

private theorem lift_ladder (D : Lettered Γ C) (ℓ : Γ) {F : Finset (List (Chunk Γ))}
    (hc : Coherent F) (hv : ∀ p ∈ F, ∀ q, Valid D q p) {x y} (hx : x ∈ F) (hy : y ∈ F)
    (c d : Option C) :
    derΛ D ℓ (some (c, letters x)) (some (d, letters y)) →
    derΛ D ℓ (some (c, original x)) (some (d, original y)) := by
  rintro ⟨a, b, s, ha, hb, hadm⟩
  obtain ⟨u, p, rfl, hau, hsp⟩ := List.map_eq_append_iff.mp ha
  obtain ⟨v, r, rfl, hbv, hsr⟩ := List.map_eq_append_iff.mp hb
  have hpr := hc _ hx _ hy p r (List.suffix_append ..) (List.suffix_append ..) (hsp.trans hsr.symm)
  subst r
  refine ⟨original u, original v, original p, original_append .., original_append .., ?_⟩
  rw [← label_cut ℓ c u p (hv _ hx), ← label_cut ℓ d v p (hv _ hy)]
  simpa only [letters, hau, hbv] using hadm

private theorem lift_position (D : Lettered Γ C) (ℓ : Γ) {x : List (Chunk Γ)}
    (hv : ∀ q, Valid D q x) (c : Option C) {i : ℕ} (hi : i ≤ (letters x).length) :
    ∃ j ≤ (original x).length, zlab D ℓ c (letters x) i = zlab D ℓ c (original x) j := by
  let p := x.take i
  let r := x.drop i
  have hsplit : p ++ r = x := List.take_append_drop ..
  have hlen : (letters p).length = i := by simp [p, Nat.min_eq_left (length_letters x ▸ hi)]
  refine ⟨(original p).length, ?_, ?_⟩
  · rw [← hsplit, original_append]; simp
  · simpa only [hsplit, hlen] using label_cut ℓ c p r (hsplit.symm ▸ hv)

/-- An injective letter map preserves holes if it preserves transitions,
preserves true targets and reflects both kinds of admission on the support. -/
private theorem map_hole {α Q : Type*} (D : Lettered α Q) (f : α → α) (E : List α)
    (inj : ∀ a ∈ E, ∀ b ∈ E, f a = f b → a = b)
    (step : ∀ a ∈ E, ∀ c, D.κ (f a) c = D.κ a c)
    (target : ∀ a ∈ E, ∀ c, D.Tf c a → D.Tf c (f a))
    (adm : ∀ l r, LabIn E l → LabIn E r → D.Λ (mapLab f id l) (mapLab f id r) → D.Λ l r)
    (final : ∀ l r, LabIn E l → LabIn E r →
      D.Λf (mapLab f id l) (mapLab f id r) → D.Λf l r)
    (v : List α) (sub : ∀ a ∈ v, a ∈ E) (h : D.IsHole v) : D.IsHole (v.map f) := by
  have run (w : List α) (hw : ∀ a ∈ w, a ∈ E) (q : Q) : kst D q (w.map f) = kst D q w := by
    induction w generalizing q with
    | nil => rfl
    | cons a w ih =>
      rw [List.map_cons, kst_cons, kst_cons, step a (hw _ List.mem_cons_self)]
      exact ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)) _
  have lab (i) : D.label (v.map f) i = mapLab f id (D.label v i) := by
    cases i with
    | zero => rfl
    | succ i =>
      simp only [Lettered.label, List.getElem?_map, core_eq_kst, ← List.map_take,
        run _ (fun a ha => sub a (List.mem_of_mem_take ha))]
      cases v[i]? <;> rfl
  have inside := labIn_label D sub
  obtain ⟨⟨q, a, hlabel, hT⟩, hF, hI⟩ := h
  have ha := inside v.length
  rw [hlabel] at ha
  unfold Lettered.IsHole
  simp only [List.length_map, lab]
  refine ⟨⟨q, f a, by rw [hlabel]; rfl, target a ha q hT⟩, ?_, ?_⟩
  · exact fun s hs h => hF s hs (final _ _ (inside s) (inside _) h)
  · intro s e hc he hadm
    have refl := isComp_map_iff f v (fun _ _ _ _ _ _ eq =>
      inj _ (sub _ (List.getElem_mem _)) _ (sub _ (List.getElem_mem _)) eq) s e
    exact hI s e (refl.mp hc) he (adm _ _ (inside s) (inside e) hadm)

/-- A single injective renaming to subsequences preserves every hole over the
dictionary. The total length of its compressed trie edges is at most `2 |B| K`. -/
theorem exists_shortening [DecidableEq Γ] (D : Lettered Γ C) (ℓ : Γ)
    (B : Finset (List Γ)) {K : ℕ} (hK : ActionBound D K) :
    ∃ f : List Γ → List Γ, Set.InjOn f (↑B) ∧
      (∀ X ∈ B, (f X).Sublist X) ∧
      (trieEdges (B.image f)).card ≤ 2 * B.card * K ∧
      ∀ v : List (List Γ), (∀ X ∈ v, X ∈ B) →
        (der D ℓ).IsHole v → (der D ℓ).IsHole (v.map f) := by
  classical
  by_cases hne : B.Nonempty
  · obtain ⟨F, hF, hc, hv, bound⟩ := exists_dictionary D hK B hne
    have rep (X : List Γ) (hx : X ∈ B) : ∃ p ∈ F, original p = X := by
      rw [← hF] at hx
      exact Finset.mem_image.mp hx
    let path (X : List Γ) := if hx : X ∈ B then (rep X hx).choose else []
    have spec (X : List Γ) (hx : X ∈ B) : path X ∈ F ∧ original (path X) = X := by
      simpa [path, hx] using (rep X hx).choose_spec
    let f (X : List Γ) := letters (path X)
    have inj : Set.InjOn f (↑B) := by
      intro x hx y hy he
      have hp := hc _ (spec _ hx).1 _ (spec _ hy).1 _ _ (List.suffix_refl _) (List.suffix_refl _) he
      rw [← (spec _ hx).2, ← (spec _ hy).2, hp]
    have ex (x) (hx : x ∈ B) (q) : fcore D ℓ q (f x) = fcore D ℓ q x := by
      exact (exit_eq ℓ q (hv _ (spec x hx).1)).trans (congrArg _ (spec x hx).2)
    have pos (x) (hx : x ∈ B) (q) (i) (hi : i ≤ (f x).length) :
        ∃ j ≤ x.length, zlab D ℓ q (f x) i = zlab D ℓ q x j := by
      have h := lift_position D ℓ (hv _ (spec x hx).1) q hi
      rwa [(spec x hx).2] at h
    have ladder (x) (hx : x ∈ B) (y) (hy : y ∈ B) (c d) :
        derΛ D ℓ (some (c, f x)) (some (d, f y)) →
          derΛ D ℓ (some (c, x)) (some (d, y)) := by
      have h := lift_ladder D ℓ hc hv (spec x hx).1 (spec y hy).1 c d
      rwa [(spec x hx).2, (spec y hy).2] at h
    refine ⟨f, inj, fun x hx => by simpa only [(spec x hx).2] using sublist (path x), ?_, ?_⟩
    · apply (Finset.card_le_card (t := trieEdges (F.image letters)) ?_).trans (by omega)
      intro s hs
      obtain ⟨hn, y, hy, hs⟩ := mem_trieEdges.mp hs
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact mem_trieEdges.mpr ⟨hn, f x, Finset.mem_image_of_mem _ (spec x hx).1, hs⟩
    · intro v hsub hh
      apply map_hole (der D ℓ) f B.toList
        (fun _ hx _ hy => inj (by simpa using hx) (by simpa using hy))
        _ _ _ _ v (by simpa using hsub) hh
      · exact fun x hx q => congrArg some (ex x (by simpa using hx) q)
      · intro x hx c ht
        have hxB : x ∈ B := by simpa using hx
        refine ⟨(ex x hxB c).symm ▸ ht.1, ?_⟩
        rintro ⟨i, hi, hr⟩
        obtain ⟨j, hj, he⟩ := pos x hxB c i hi
        rw [he, ex x hxB c] at hr
        exact ht.2 ⟨j, hj, hr⟩
      · rintro (_ | ⟨c,x⟩) (_ | ⟨d,y⟩) hx hy hr
        all_goals try exact hr
        exact ladder x (by simpa [LabIn] using hx) y (by simpa [LabIn] using hy) c d hr
      · rintro (_ | ⟨c,x⟩) (_ | ⟨d,y⟩) hx hy hr
        all_goals try exact hr
        have hxB : x ∈ B := by simpa [LabIn] using hx
        have hyB : y ∈ B := by simpa [LabIn] using hy
        rcases hr with hr | ⟨i, hi, hr⟩
        · exact Or.inl (ladder x hxB y hyB c d hr)
        · obtain ⟨j, hj, he⟩ := pos x hxB c i hi
          simp only [id_eq] at hr
          rw [he, ex y hyB d] at hr
          exact Or.inr ⟨j, hj, hr⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact ⟨id, Function.injective_id.injOn, by simp, by simp [trieEdges], by simp⟩

end DeciNSSE.Shortening
