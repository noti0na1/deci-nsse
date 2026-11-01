import DeciNSSE.Holes.Hierarchy.Derived

/-! # Agreement of lettered monitors on a support

An agreement `Agree D D' φ E` says that the letter map `φ` carries the atomic
type of the letters of `E` in `D` to that of their images in `D'`: the same
start core, the same transitions, targets and admissions on labels over `E`.
Agreement transfers holes over `E`, composes, and passes through derived
monitors.

## Main declarations

- `LabIn`, `Agree`: labels over a support, and agreement on a support.
- `Agree.refl`, `Agree.comp`: identity and composition.
- `Agree.isHole_iff`: agreement transfers holes over the support.
- `Agree.derive`: agreement passes through `Der(·, ℓ)`.

The declarations are in the namespace `DeciNSSE.BoundedDepth`.
-/

namespace DeciNSSE.BoundedDepth
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy
open scoped List

section Agree
variable {Γ Γ' Γ'' C : Type*}

/-- Labels whose letter lies in `E` (and the start label `S`). -/
def LabIn (E : List Γ) : Lab Γ C → Prop
  | none => True
  | some (_, a) => a ∈ E

/-- Agreement on a support. `φ` carries the atomic type of the letters of `E` in `D` to
that of their images in `D'`, possibly over another alphabet: the start core is the same,
`φ` is injective on `E`, and `κ`, `Tf`, `Λ`, `Λ^f` (the `S`-rows included) are preserved on
all labels whose letters lie in `E`, for all cores. -/
structure Agree (D : Lettered Γ C) (D' : Lettered Γ' C) (φ : Γ → Γ') (E : List Γ) : Prop where
  /-- The same start core. -/
  start : D'.start = D.start
  /-- `φ` is injective on `E`. -/
  inj : ∀ a ∈ E, ∀ b ∈ E, φ a = φ b → a = b
  /-- The same transitions on the letters of `E`. -/
  κ : ∀ a ∈ E, ∀ c, D'.κ (φ a) c = D.κ a c
  /-- The same target condition on the letters of `E`. -/
  tf : ∀ a ∈ E, ∀ c, (D'.Tf c (φ a) ↔ D.Tf c a)
  /-- The same interior admissions on labels over `E`. -/
  Λ : ∀ L L', LabIn E L → LabIn E L' → (D'.Λ (mapLab φ id L) (mapLab φ id L') ↔ D.Λ L L')
  /-- The same terminal admissions on labels over `E`. -/
  Λf : ∀ L L', LabIn E L → LabIn E L' → (D'.Λf (mapLab φ id L) (mapLab φ id L') ↔ D.Λf L L')

/-- Renaming fixes the start label. -/
@[simp] theorem mapLab_none (φ : Γ → Γ') : mapLab φ (id : C → C) none = none := rfl

/-- Renaming a letter label renames its letter. -/
@[simp] theorem mapLab_some (φ : Γ → Γ') (c : C) (a : Γ) :
    mapLab φ id (some (c, a)) = some (c, φ a) := rfl

/-- Renaming by identities is the identity. -/
theorem mapLab_id (L : Lab Γ C) : mapLab (id : Γ → Γ) (id : C → C) L = L := by
  rcases L with _ | ⟨c, a⟩ <;> rfl

/-- Renamings compose. -/
theorem mapLab_comp (φ : Γ' → Γ'') (ψ : Γ → Γ') (L : Lab Γ C) :
    mapLab (φ ∘ ψ) (id : C → C) L = mapLab φ id (mapLab ψ id L) := by
  rcases L with _ | ⟨c, a⟩ <;> rfl

/-- Every monitor agrees with itself under the identity. -/
theorem Agree.refl (D : Lettered Γ C) (E : List Γ) : Agree D D id E where
  start := rfl
  inj _ _ _ _ h := h
  κ _ _ _ := rfl
  tf _ _ _ := Iff.rfl
  Λ L L' _ _ := by rw [mapLab_id, mapLab_id]
  Λf L L' _ _ := by rw [mapLab_id, mapLab_id]

/-- Labels over `E` are renamed to labels over `φ(E)`. -/
theorem LabIn.map {E : List Γ} (φ : Γ → Γ') {L : Lab Γ C} (h : LabIn E L) :
    LabIn (E.map φ) (mapLab φ id L) := by
  rcases L with _ | ⟨c, a⟩
  · trivial
  · exact List.mem_map_of_mem h

/-- Composition of agreements. -/
theorem Agree.comp {D : Lettered Γ C} {D' : Lettered Γ' C} {D'' : Lettered Γ'' C}
    {ψ : Γ → Γ'} {φ : Γ' → Γ''} {E : List Γ}
    (h₁ : Agree D D' ψ E) (h₂ : Agree D' D'' φ (E.map ψ)) : Agree D D'' (φ ∘ ψ) E where
  start := h₂.start.trans h₁.start
  inj a ha b hb h := h₁.inj a ha b hb
    (h₂.inj _ (List.mem_map_of_mem ha) _ (List.mem_map_of_mem hb) h)
  κ a ha c := (h₂.κ _ (List.mem_map_of_mem ha) c).trans (h₁.κ a ha c)
  tf a ha c := (h₂.tf _ (List.mem_map_of_mem ha) c).trans (h₁.tf a ha c)
  Λ L L' hL hL' := by
    rw [mapLab_comp, mapLab_comp]
    exact (h₂.Λ _ _ (hL.map ψ) (hL'.map ψ)).trans (h₁.Λ L L' hL hL')
  Λf L L' hL hL' := by
    rw [mapLab_comp, mapLab_comp]
    exact (h₂.Λf _ _ (hL.map ψ) (hL'.map ψ)).trans (h₁.Λf L L' hL hL')

variable {D : Lettered Γ C} {D' : Lettered Γ' C} {φ : Γ → Γ'} {E : List Γ}

/-- Agreement preserves `κ*` along words over the support. -/
theorem Agree.kst_map (h : Agree D D' φ E) :
    ∀ (w : List Γ), (∀ a ∈ w, a ∈ E) → ∀ c, kst D' c (w.map φ) = kst D c w
  | [], _, _ => rfl
  | a :: w, hw, c => by
      rw [List.map_cons, kst_cons, kst_cons, h.κ a (hw a List.mem_cons_self)]
      exact h.kst_map w (fun b hb => hw b (List.mem_cons_of_mem _ hb)) _

/-- The labels of a word over `E` are labels over `E`. -/
theorem labIn_labFrom (D : Lettered Γ C) {w : List Γ} (hw : ∀ a ∈ w, a ∈ E) (c : C) :
    ∀ p, LabIn E (labFrom D c w p)
  | 0 => trivial
  | x + 1 => by
      simp only [labFrom]
      rcases hx : w[x]? with _ | a
      · trivial
      · exact hw a (List.mem_of_getElem? hx)

/-- Agreement commutes with the labels read from a core. -/
theorem Agree.labFrom_map (h : Agree D D' φ E) {w : List Γ} (hw : ∀ a ∈ w, a ∈ E) (c : C) :
    ∀ p, labFrom D' c (w.map φ) p = mapLab φ id (labFrom D c w p)
  | 0 => rfl
  | x + 1 => by
      simp only [DeciNSSE.LetteredHierarchy.labFrom, List.getElem?_map, ← List.map_take,
        h.kst_map _ (fun a ha => hw a (List.mem_of_mem_take ha))]
      rcases w[x]? with _ | a <;> rfl

/-- The labels of a word over `E` are labels over `E`. -/
theorem labIn_label (D : Lettered Γ C) {v : List Γ} (hv : ∀ a ∈ v, a ∈ E) (x : ℕ) :
    LabIn E (D.label v x) := by
  rw [label_eq_labFrom]; exact labIn_labFrom D hv _ x

/-- Agreement commutes with labels. -/
theorem Agree.label_map (h : Agree D D' φ E) {v : List Γ} (hv : ∀ a ∈ v, a ∈ E) (x : ℕ) :
    D'.label (v.map φ) x = mapLab φ id (D.label v x) := by
  rw [label_eq_labFrom, label_eq_labFrom, h.start]
  exact h.labFrom_map hv _ x

/-- Agreement preserves and reflects comparisons, since `φ` is injective on the support. -/
theorem Agree.isComp_iff (h : Agree D D' φ E) {v : List Γ} (hv : ∀ a ∈ v, a ∈ E) (s e : ℕ) :
    IsComp (v.map φ) s e ↔ IsComp v s e :=
  isComp_map_iff φ v (fun _ _ _ _ _ _ he => h.inj _ (hv _ (List.getElem_mem _)) _
    (hv _ (List.getElem_mem _)) he) s e

/-- Transfer. Under an agreement on a support containing the letters of
`v`, `φ(v)` is a hole of `D'` iff `v` is a hole of `D`. -/
theorem Agree.isHole_iff (h : Agree D D' φ E) {v : List Γ} (hv : ∀ a ∈ v, a ∈ E) :
    D'.IsHole (v.map φ) ↔ D.IsHole v := by
  have hl := h.label_map hv
  have hu := labIn_label (E := E) D hv
  unfold Lettered.IsHole
  rw [List.length_map, hl]
  refine and_congr ?_ (and_congr ?_ ?_)
  · have hU := hu v.length
    rcases hL : D.label v v.length with _ | ⟨c, a⟩
    · simp
    · rw [hL] at hU
      rw [mapLab_some, exists_some_eq_iff, exists_some_eq_iff]
      exact h.tf a hU c
  · refine forall_congr' fun s => imp_congr_right fun _ => not_congr ?_
    rw [hl]
    exact h.Λf _ _ (hu s) (hu _)
  · refine forall_congr' fun s => forall_congr' fun e => ?_
    rw [h.isComp_iff hv]
    refine imp_congr_right fun _ => imp_congr_right fun _ => not_congr ?_
    rw [hl, hl]
    exact h.Λ _ _ (hu s) (hu e)

section DerAgree
variable (h : Agree D D' φ E) {ℓ : Γ} (hℓ : ℓ ∈ E)
include h hℓ

/-- Agreement preserves the exit cores of shifted blocks. -/
theorem Agree.fcore_map {X : List Γ} (hX : ∀ a ∈ X, a ∈ E) (c : Option C) :
    fcore D' (φ ℓ) c (X.map φ) = fcore D ℓ c X := by
  rcases c with _ | c
  · simp only [DeciNSSE.LetteredHierarchy.fcore, h.start]; exact h.kst_map X hX _
  · simp only [DeciNSSE.LetteredHierarchy.fcore]
    rw [show φ ℓ :: X.map φ = (ℓ :: X).map φ from rfl]
    exact h.kst_map (ℓ :: X) (fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hℓ
      · exact hX a ha) c

/-- Agreement commutes with the labels of shifted blocks. -/
theorem Agree.zlab_map {X : List Γ} (hX : ∀ a ∈ X, a ∈ E) (c : Option C) (p : ℕ) :
    zlab D' (φ ℓ) c (X.map φ) p = mapLab φ id (zlab D ℓ c X p) := by
  rcases c with _ | c
  · simp only [DeciNSSE.LetteredHierarchy.zlab, h.start]; exact h.labFrom_map hX _ p
  · simp only [DeciNSSE.LetteredHierarchy.zlab]
    rw [show φ ℓ :: X.map φ = (ℓ :: X).map φ from rfl]
    exact h.labFrom_map (fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hℓ
      · exact hX a ha) c (p + 1)

omit h in
/-- The labels of a shifted block over `E ∋ ℓ` are labels over `E`. -/
theorem labIn_zlab (D : Lettered Γ C) {X : List Γ} (hX : ∀ a ∈ X, a ∈ E) (c : Option C)
    (p : ℕ) : LabIn E (zlab D ℓ c X p) := by
  rcases c with _ | c
  · exact labIn_labFrom D hX _ p
  · exact labIn_labFrom D (fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hℓ
      · exact hX a ha) c (p + 1)

/-- Agreement preserves the ladder `Λ'`. -/
theorem Agree.derΛ_map {X Y : List Γ} (hX : ∀ a ∈ X, a ∈ E) (hY : ∀ a ∈ Y, a ∈ E)
    (c c' : Option C) :
    derΛ D' (φ ℓ) (some (c, X.map φ)) (some (c', Y.map φ)) ↔
      derΛ D ℓ (some (c, X)) (some (c', Y)) := by
  simp only [DeciNSSE.LetteredHierarchy.derΛ]
  constructor
  · rintro ⟨x, x', y, hx, hy, hΛ⟩
    obtain ⟨X1, X2, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hx
    obtain ⟨Y1, Y2, rfl, rfl, h2⟩ := List.map_eq_append_iff.mp hy
    have hX2 : ∀ a ∈ X2, a ∈ E := fun a ha => hX a (List.mem_append_right _ ha)
    have hY2 : ∀ a ∈ Y2, a ∈ E := fun a ha => hY a (List.mem_append_right _ ha)
    obtain rfl := map_inj_on h.inj hY2 hX2 h2
    rw [h.zlab_map hℓ hX, h.zlab_map hℓ hY, List.length_map, List.length_map] at hΛ
    exact ⟨X1, Y1, Y2, rfl, rfl,
      (h.Λ _ _ (labIn_zlab hℓ D hX c _) (labIn_zlab hℓ D hY c' _)).mp hΛ⟩
  · rintro ⟨x, x', y, rfl, rfl, hΛ⟩
    refine ⟨x.map φ, x'.map φ, y.map φ, by simp, by simp, ?_⟩
    rw [h.zlab_map hℓ hX, h.zlab_map hℓ hY, List.length_map, List.length_map]
    exact (h.Λ _ _ (labIn_zlab hℓ D hX c _) (labIn_zlab hℓ D hY c' _)).mpr hΛ

/-- Agreement preserves the terminal admissions of a shifted block. -/
theorem Agree.blockΛf_map {X : List Γ} (hX : ∀ a ∈ X, a ∈ E) (c : Option C) (d : C) :
    (∃ p ≤ (X.map φ).length, D'.Λf (zlab D' (φ ℓ) c (X.map φ) p) (some (d, φ ℓ))) ↔
      ∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) (some (d, ℓ)) := by
  rw [List.length_map]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  rw [h.zlab_map hℓ hX, show (some (d, φ ℓ) : Lab Γ' C) = mapLab φ id (some (d, ℓ)) from rfl]
  exact h.Λf _ _ (labIn_zlab hℓ D hX c p) hℓ

/-- Agreement passes through `Der(·, ℓ)`. If `φ` agrees on a support `E ∋ ℓ`, then the
letterwise map agrees on every list of level-`(j+1)` letters over `E`, between `Der(D, ℓ)` and
`Der(D', φ ℓ)`. -/
theorem Agree.derive (F : List (List Γ)) (hF : ∀ X ∈ F, ∀ a ∈ X, a ∈ E) :
    Agree (der D ℓ) (der D' (φ ℓ)) (List.map φ) F where
  start := rfl
  inj X hX Y hY hXY := map_inj_on h.inj (hF X hX) (hF Y hY) hXY
  κ X hX c := by rw [der_κ, der_κ, h.fcore_map hℓ (hF X hX)]
  tf X hX c := by
    simp only [der_Tf, derTf]
    rw [h.fcore_map hℓ (hF X hX), h.tf ℓ hℓ, h.blockΛf_map hℓ (hF X hX)]
  Λ L L' hL hL' := by
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · simp [derΛ]
    · simp [derΛ]
    · simp [derΛ]
    · exact h.derΛ_map hℓ (hF X hL) (hF Y hL') c c'
  Λf L L' hL hL' := by
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · simp [derΛf]
    · simp [derΛf]
    · simp [derΛf]
    · simp only [mapLab_some, der_Λf, derΛf]
      rw [h.derΛ_map hℓ (hF X hL) (hF Y hL') c c', h.fcore_map hℓ (hF Y hL'),
        h.blockΛf_map hℓ (hF X hL)]

end DerAgree

end Agree

end DeciNSSE.BoundedDepth
