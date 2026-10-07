import DeciNSSE.Holes.Hierarchy
import DeciNSSE.Holes.Packets

/-! # Finite search at bounded hierarchy depth

Finite summaries record transitions, admissions and block equalities.
Short representatives preserve the derived monitor on its support. At a unary
level a short power of one letter is a hole; iterating the compression below
it bounds the length of a witness at bounded depth. This does not bound every
hole at that depth.
-/

set_option autoImplicit false

namespace DeciNSSE.BoundedDepth
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy
open scoped List

section Agree
variable {Γ C : Type*}

/-- Labels whose letter lies in `E` (and the start label `S`). -/
def LabIn (E : List Γ) : Lab Γ C → Prop
  | none => True
  | some (_, a) => a ∈ E

/-- Agreement on a support. `φ` carries the atomic type of the letters of `E` in `D` to
that of their images in `D'`: the start core is the same, `φ` is injective on
`E`, and `κ`, `Tf`, `Λ`, `Λ^f` (the `S`-rows included) are preserved on all labels whose
letters lie in `E`, for all cores. -/
structure Agree (D D' : Lettered Γ C) (φ : Γ → Γ) (E : List Γ) : Prop where
  start : D'.start = D.start
  inj : ∀ a ∈ E, ∀ b ∈ E, φ a = φ b → a = b
  κ : ∀ a ∈ E, ∀ c, D'.κ (φ a) c = D.κ a c
  tf : ∀ a ∈ E, ∀ c, (D'.Tf c (φ a) ↔ D.Tf c a)
  Λ : ∀ L L', LabIn E L → LabIn E L' → (D'.Λ (mapLab φ id L) (mapLab φ id L') ↔ D.Λ L L')
  Λf : ∀ L L', LabIn E L → LabIn E L' → (D'.Λf (mapLab φ id L) (mapLab φ id L') ↔ D.Λf L L')

@[simp] theorem mapLab_none (φ : Γ → Γ) : mapLab φ (id : C → C) none = none := rfl

@[simp] theorem mapLab_some (φ : Γ → Γ) (c : C) (a : Γ) :
    mapLab φ id (some (c, a)) = some (c, φ a) := rfl

theorem mapLab_id (L : Lab Γ C) : mapLab (id : Γ → Γ) (id : C → C) L = L := by
  rcases L with _ | ⟨c, a⟩ <;> rfl

theorem mapLab_comp (φ ψ : Γ → Γ) (L : Lab Γ C) :
    mapLab (φ ∘ ψ) (id : C → C) L = mapLab φ id (mapLab ψ id L) := by
  rcases L with _ | ⟨c, a⟩ <;> rfl

theorem Agree.refl (D : Lettered Γ C) (E : List Γ) : Agree D D id E where
  start := rfl
  inj _ _ _ _ h := h
  κ _ _ _ := rfl
  tf _ _ _ := Iff.rfl
  Λ L L' _ _ := by rw [mapLab_id, mapLab_id]
  Λf L L' _ _ := by rw [mapLab_id, mapLab_id]

theorem LabIn.map {E : List Γ} (φ : Γ → Γ) {L : Lab Γ C} (h : LabIn E L) :
    LabIn (E.map φ) (mapLab φ id L) := by
  rcases L with _ | ⟨c, a⟩
  · trivial
  · exact List.mem_map_of_mem h

/-- Composition of agreements. -/
theorem Agree.comp {D D' D'' : Lettered Γ C} {ψ φ : Γ → Γ} {E : List Γ}
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

variable {D D' : Lettered Γ C} {φ : Γ → Γ} {E : List Γ}

theorem Agree.kst_map (h : Agree D D' φ E) :
    ∀ (w : List Γ), (∀ a ∈ w, a ∈ E) → ∀ c, kst D' c (w.map φ) = kst D c w
  | [], _, _ => rfl
  | a :: w, hw, c => by
      rw [List.map_cons, kst_cons, kst_cons, h.κ a (hw a List.mem_cons_self)]
      exact h.kst_map w (fun b hb => hw b (List.mem_cons_of_mem _ hb)) _

theorem labIn_labFrom (D : Lettered Γ C) {w : List Γ} (hw : ∀ a ∈ w, a ∈ E) (c : C) :
    ∀ p, LabIn E (labFrom D c w p)
  | 0 => trivial
  | x + 1 => by
      simp only [labFrom]
      rcases hx : w[x]? with _ | a
      · trivial
      · exact hw a (List.mem_of_getElem? hx)

theorem Agree.labFrom_map (h : Agree D D' φ E) {w : List Γ} (hw : ∀ a ∈ w, a ∈ E) (c : C) :
    ∀ p, labFrom D' c (w.map φ) p = mapLab φ id (labFrom D c w p)
  | 0 => rfl
  | x + 1 => by
      simp only [DeciNSSE.LetteredHierarchy.labFrom, List.getElem?_map, ← List.map_take,
        h.kst_map _ (fun a ha => hw a (List.mem_of_mem_take ha))]
      rcases w[x]? with _ | a <;> rfl

theorem labIn_label (D : Lettered Γ C) {v : List Γ} (hv : ∀ a ∈ v, a ∈ E) (x : ℕ) :
    LabIn E (D.label v x) := by
  rw [label_eq_labFrom]; exact labIn_labFrom D hv _ x

theorem Agree.label_map (h : Agree D D' φ E) {v : List Γ} (hv : ∀ a ∈ v, a ∈ E) (x : ℕ) :
    D'.label (v.map φ) x = mapLab φ id (D.label v x) := by
  rw [label_eq_labFrom, label_eq_labFrom, h.start]
  exact h.labFrom_map hv _ x

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
theorem labIn_zlab (D : Lettered Γ C) {X : List Γ} (hX : ∀ a ∈ X, a ∈ E) (c : Option C)
    (p : ℕ) : LabIn E (zlab D ℓ c X p) := by
  rcases c with _ | c
  · exact labIn_labFrom D hX _ p
  · exact labIn_labFrom D (fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hℓ
      · exact hX a ha) c (p + 1)

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

theorem Agree.blockΛf_map {X : List Γ} (hX : ∀ a ∈ X, a ∈ E) (c : Option C) (d : C) :
    (∃ p ≤ (X.map φ).length, D'.Λf (zlab D' (φ ℓ) c (X.map φ) p) (some (d, φ ℓ))) ↔
      ∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) (some (d, ℓ)) := by
  rw [List.length_map]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  rw [h.zlab_map hℓ hX, show (some (d, φ ℓ) : Lab Γ C) = mapLab φ id (some (d, ℓ)) from rfl]
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

section Column
variable {Γ C : Type*} (D : Lettered Γ C) (ℓ : Γ)

/-- The label of position `0` of a shifted block: `(c, ℓ)`, or `S` for the new start core. -/
def lab0 (c : Option C) : Lab Γ C := c.map fun c => (c, ℓ)

theorem zlab_zero (c : Option C) (X : List Γ) : zlab D ℓ c X 0 = lab0 ℓ c := by
  rcases c with _ | c
  · rfl
  · simp [zlab, labFrom, lab0]

theorem fcore_snoc (c : Option C) (X : List Γ) (z : Γ) :
    fcore D ℓ c (X ++ [z]) = D.κ z (fcore D ℓ c X) := by
  rcases c with _ | c
  · simp only [fcore, kst_append]; rfl
  · simp only [fcore]; rw [← List.cons_append, kst_append]; rfl

theorem zlab_snoc_le (c : Option C) (X : List Γ) (z : Γ) {p : ℕ} (hp : p ≤ X.length) :
    zlab D ℓ c (X ++ [z]) p = zlab D ℓ c X p := by
  rcases c with _ | c
  · exact labFrom_append_le D _ X [z] hp
  · simp only [zlab]
    rw [← List.cons_append]
    exact labFrom_append_le D _ (ℓ :: X) [z] (by simp; omega)

theorem zlab_snoc_last (c : Option C) (X : List Γ) (z : Γ) :
    zlab D ℓ c (X ++ [z]) (X.length + 1) = some (fcore D ℓ c X, z) := by
  rcases c with _ | c
  · simp [zlab, labFrom, fcore]
  · simp [zlab, labFrom, fcore]

theorem blockΛf_snoc (c : Option C) (X : List Γ) (z : Γ) (L : Lab Γ C) :
    (∃ p ≤ (X ++ [z]).length, D.Λf (zlab D ℓ c (X ++ [z]) p) L) ↔
      (∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) L) ∨ D.Λf (some (fcore D ℓ c X, z)) L := by
  constructor
  · rintro ⟨p, hp, hΛ⟩
    rw [List.length_append, List.length_singleton] at hp
    rcases Nat.lt_or_ge X.length p with h | h
    · obtain rfl : p = X.length + 1 := by omega
      rw [zlab_snoc_last] at hΛ; exact Or.inr hΛ
    · rw [zlab_snoc_le D ℓ c X z h] at hΛ; exact Or.inl ⟨p, h, hΛ⟩
  · rintro (⟨p, hp, hΛ⟩ | hΛ)
    · exact ⟨p, by simp; omega, by rw [zlab_snoc_le D ℓ c X z hp]; exact hΛ⟩
    · exact ⟨X.length + 1, by simp, by rw [zlab_snoc_last]; exact hΛ⟩

theorem blockΛf_nil (c : Option C) (L : Lab Γ C) :
    (∃ p ≤ ([] : List Γ).length, D.Λf (zlab D ℓ c [] p) L) ↔ D.Λf (lab0 ℓ c) L := by
  constructor
  · rintro ⟨p, hp, hΛ⟩
    obtain rfl : p = 0 := by simpa using hp
    rwa [zlab_zero] at hΛ
  · intro hΛ; exact ⟨0, le_rfl, by rwa [zlab_zero]⟩

theorem derΛ_nil_nil (c c' : Option C) :
    derΛ D ℓ (some (c, [])) (some (c', [])) ↔ D.Λ (lab0 ℓ c) (lab0 ℓ c') := by
  simp only [derΛ]
  constructor
  · rintro ⟨x, x', y, hx, hx', hΛ⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
    obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hx'.symm
    simpa [zlab_zero] using hΛ
  · intro hΛ; exact ⟨[], [], [], rfl, rfl, by simpa [zlab_zero] using hΛ⟩

theorem derΛ_nil_snoc (c c' : Option C) (Y : List Γ) (z' : Γ) :
    derΛ D ℓ (some (c, [])) (some (c', Y ++ [z'])) ↔
      D.Λ (lab0 ℓ c) (some (fcore D ℓ c' Y, z')) := by
  simp only [derΛ]
  constructor
  · rintro ⟨x, x', y, hx, hx', hΛ⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
    rw [List.append_nil] at hx'
    subst hx'
    rwa [List.length_nil, zlab_zero, List.length_append, List.length_singleton,
      zlab_snoc_last] at hΛ
  · intro hΛ
    refine ⟨[], Y ++ [z'], [], rfl, (List.append_nil _).symm, ?_⟩
    rwa [List.length_nil, zlab_zero, List.length_append, List.length_singleton, zlab_snoc_last]

theorem derΛ_snoc_nil (c c' : Option C) (X : List Γ) (z : Γ) :
    derΛ D ℓ (some (c, X ++ [z])) (some (c', [])) ↔
      D.Λ (some (fcore D ℓ c X, z)) (lab0 ℓ c') := by
  simp only [derΛ]
  constructor
  · rintro ⟨x, x', y, hx, hx', hΛ⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx'.symm
    rw [List.append_nil] at hx
    subst hx
    rwa [List.length_nil, zlab_zero, List.length_append, List.length_singleton,
      zlab_snoc_last] at hΛ
  · intro hΛ
    refine ⟨X ++ [z], [], [], (List.append_nil _).symm, rfl, ?_⟩
    rwa [List.length_nil, zlab_zero, List.length_append, List.length_singleton, zlab_snoc_last]

theorem derΛ_snoc_snoc (c c' : Option C) (X Y : List Γ) (z z' : Γ) :
    derΛ D ℓ (some (c, X ++ [z])) (some (c', Y ++ [z'])) ↔
      D.Λ (some (fcore D ℓ c X, z)) (some (fcore D ℓ c' Y, z')) ∨
        (z = z' ∧ derΛ D ℓ (some (c, X)) (some (c', Y))) := by
  simp only [derΛ]
  constructor
  · rintro ⟨x, x', y, hx, hy, hΛ⟩
    rcases List.eq_nil_or_concat y with rfl | ⟨y0, u, rfl⟩
    · rw [List.append_nil] at hx hy
      subst hx; subst hy
      left
      rwa [List.length_append, List.length_singleton, zlab_snoc_last,
        List.length_append, List.length_singleton, zlab_snoc_last] at hΛ
    · rw [List.concat_eq_append, ← List.append_assoc] at hx hy
      obtain ⟨hX, hz⟩ := List.append_inj' hx rfl
      obtain ⟨hY, hz'⟩ := List.append_inj' hy rfl
      simp only [List.cons.injEq, and_true] at hz hz'
      right
      refine ⟨hz.trans hz'.symm, x, x', y0, hX, hY, ?_⟩
      rwa [zlab_snoc_le D ℓ c X z (p := x.length) (by rw [hX]; simp),
        zlab_snoc_le D ℓ c' Y z' (p := x'.length) (by rw [hY]; simp)] at hΛ
  · rintro (hΛ | ⟨hzz, x, x', y, hX, hY, hΛ⟩)
    · refine ⟨X ++ [z], Y ++ [z'], [], (List.append_nil _).symm, (List.append_nil _).symm, ?_⟩
      rwa [List.length_append, List.length_singleton, zlab_snoc_last,
        List.length_append, List.length_singleton, zlab_snoc_last]
    · refine ⟨x, x', y ++ [z], by rw [hX, List.append_assoc], by
        rw [hY, List.append_assoc, hzz], ?_⟩
      rwa [zlab_snoc_le D ℓ c X z (p := x.length) (by rw [hX]; simp),
        zlab_snoc_le D ℓ c' Y z' (p := x'.length) (by rw [hY]; simp)]

/-- States of the column automaton for `k` tracks over cores `C`: the exits `fc(c, X_a)`, the
sets `B_a(c) ∋ d` (some label of the shifted block `Ẑ_a(c)` is `Λ^f`-related to `(d, ℓ)`),
the equality relation of the tracks, and the ladders `Λ'` for all pairs of tracks and start
cores. -/
abbrev CS (C : Type*) (k : ℕ) :=
  (Fin k → Option C → C) × (Fin k → Option C → C → Prop) × (Fin k → Fin k → Prop) ×
    (Fin k → Fin k → Option C → Option C → Prop)

variable (k : ℕ)

/-- The transition of the column automaton on a column (`none` = padding; columns are
right-aligned, so a padded track is still empty). -/
def colStep (x : CS C k) (col : Fin k → Option Γ) : CS C k :=
  (fun a c => match col a with
      | none => x.1 a c
      | some z => D.κ z (x.1 a c),
   fun a c d => match col a with
      | none => x.2.1 a c d
      | some z => x.2.1 a c d ∨ D.Λf (some (x.1 a c, z)) (some (d, ℓ)),
   fun a b => x.2.2.1 a b ∧ col a = col b,
   fun a b c c' => match col a, col b with
      | none, none => x.2.2.2 a b c c'
      | none, some z' => D.Λ (lab0 ℓ c) (some (x.1 b c', z'))
      | some z, none => D.Λ (some (x.1 a c, z)) (lab0 ℓ c')
      | some z, some z' =>
          D.Λ (some (x.1 a c, z)) (some (x.1 b c', z')) ∨ (z = z' ∧ x.2.2.2 a b c c'))

/-- The initial state (all tracks empty). -/
def colStart : CS C k :=
  (fun _ c => fcore D ℓ c [], fun _ c d => D.Λf (lab0 ℓ c) (some (d, ℓ)), fun _ _ => True,
    fun _ _ c c' => D.Λ (lab0 ℓ c) (lab0 ℓ c'))

/-- The finite reader that accumulates a summary of padded word columns. -/
def colDFA : DFA (Fin k → Option Γ) (CS C k) where
  step := colStep D ℓ k
  start := colStart D ℓ k
  accept := ∅

/-- The intended value of the column automaton on a tuple of level-`(j+1)` letters. -/
def summ (Ws : Fin k → List Γ) : CS C k :=
  (fun a c => fcore D ℓ c (Ws a),
   fun a c d => ∃ p ≤ (Ws a).length, D.Λf (zlab D ℓ c (Ws a) p) (some (d, ℓ)),
   fun a b => Ws a = Ws b,
   fun a b c c' => derΛ D ℓ (some (c, Ws a)) (some (c', Ws b)))

open DeciNSSE.Packets in

theorem colEval (w : List (Fin k → Option Γ)) (hw : Valid w) :
    (colDFA D ℓ k).eval w = summ D ℓ k (dec w) := by
  induction w using List.reverseRecOn with
  | nil =>
    have hd : ∀ a, dec ([] : List (Fin k → Option Γ)) a = [] := fun _ => rfl
    show colStart D ℓ k = summ D ℓ k (dec [])
    simp only [colStart, summ, hd]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext a c d; exact propext (blockΛf_nil D ℓ c _).symm
    · funext a b; simp
    · funext a b c c'; exact propext (derΛ_nil_nil D ℓ c c').symm
  | append_singleton w col ih =>
    rw [DFA.eval_append_singleton, ih (hw.sublist (List.sublist_append_left _ _))]
    have hpad : ∀ a, col a = none → dec w a = [] := dec_eq_nil_of_pad hw
    show colStep D ℓ k (summ D ℓ k (dec w)) col = summ D ℓ k (dec (w ++ [col]))
    simp only [colStep, summ, dec_snoc]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext a c
      dsimp only
      rcases col a with _ | z
      · simp
      · simp [fcore_snoc]
    · funext a c d
      dsimp only
      rcases col a with _ | z
      · simp
      · simp only [Option.toList_some]
        exact propext (blockΛf_snoc D ℓ c _ z _).symm
    · funext a b
      dsimp only
      apply propext
      rcases hca : col a with _ | z <;> rcases hcb : col b with _ | z'
      · rw [hpad a hca, hpad b hcb]; simp
      · rw [hpad a hca]; simp
      · rw [hpad b hcb]; simp
      · simp only [Option.toList_some, Option.some.injEq]
        constructor
        · rintro ⟨h1, rfl⟩; rw [h1]
        · intro h
          obtain ⟨e1, e2⟩ := List.append_inj' h rfl
          simp only [List.cons.injEq, and_true] at e2
          exact ⟨e1, e2⟩
    · funext a b c c'
      dsimp only
      apply propext
      rcases hca : col a with _ | z <;> rcases hcb : col b with _ | z'
      · simp
      · rw [hpad a hca]
        simp only [Option.toList_none, Option.toList_some, List.append_nil]
        exact (derΛ_nil_snoc D ℓ c c' _ z').symm
      · rw [hpad b hcb]
        simp only [Option.toList_none, Option.toList_some, List.append_nil]
        exact (derΛ_snoc_nil D ℓ c c' _ z).symm
      · simp only [Option.toList_some]
        exact (derΛ_snoc_snoc D ℓ c c' _ _ z z').symm

instance instFintypeCS [Fintype C] [DecidableEq C] : Fintype (CS C k) :=
  @instFintypeProd _ _ inferInstance
    (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance inferInstance))

/-- The number of column-automaton states for `N` cores and `k` tracks. -/
def colBound (N k : ℕ) : ℕ :=
  (N ^ (N + 1)) ^ k * ((2 ^ N) ^ (N + 1)) ^ k * (2 ^ k) ^ k *
    (((2 ^ (N + 1)) ^ (N + 1)) ^ k) ^ k

theorem card_CS [Fintype C] [DecidableEq C] :
    Fintype.card (CS C k) = colBound (Fintype.card C) k := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  simp [Fintype.card_option, colBound, mul_assoc]

/-- The summary determines the atomic type at level `j + 1`:
two `k`-tuples with the same column summary have the same equality pattern and the same
`κ'`, `Tf'`, `Λ'`, `Λ'^f` in `Der(D, ℓ)` (all start cores). -/
theorem der_type_of_summ {Ws Ws' : Fin k → List Γ} (hs : summ D ℓ k Ws' = summ D ℓ k Ws)
    (a b : Fin k) :
    (Ws' a = Ws' b ↔ Ws a = Ws b) ∧
    (∀ c, (der D ℓ).κ (Ws' a) c = (der D ℓ).κ (Ws a) c) ∧
    (∀ c, (der D ℓ).Tf c (Ws' a) ↔ (der D ℓ).Tf c (Ws a)) ∧
    (∀ c c', (der D ℓ).Λ (some (c, Ws' a)) (some (c', Ws' b)) ↔
      (der D ℓ).Λ (some (c, Ws a)) (some (c', Ws b))) ∧
    (∀ c c', (der D ℓ).Λf (some (c, Ws' a)) (some (c', Ws' b)) ↔
      (der D ℓ).Λf (some (c, Ws a)) (some (c', Ws b))) := by
  have h1 : ∀ a c, fcore D ℓ c (Ws' a) = fcore D ℓ c (Ws a) := fun a c =>
    congrFun (congrFun (congrArg Prod.fst hs) a) c
  have h2 : ∀ a c d, (∃ p ≤ (Ws' a).length, D.Λf (zlab D ℓ c (Ws' a) p) (some (d, ℓ))) ↔
      ∃ p ≤ (Ws a).length, D.Λf (zlab D ℓ c (Ws a) p) (some (d, ℓ)) := fun a c d =>
    Iff.of_eq (congrFun (congrFun (congrFun (congrArg (fun s => s.2.1) hs) a) c) d)
  have h3 : ∀ a b, Ws' a = Ws' b ↔ Ws a = Ws b := fun a b =>
    Iff.of_eq (congrFun (congrFun (congrArg (fun s => s.2.2.1) hs) a) b)
  have h4 : ∀ a b c c', derΛ D ℓ (some (c, Ws' a)) (some (c', Ws' b)) ↔
      derΛ D ℓ (some (c, Ws a)) (some (c', Ws b)) := fun a b c c' =>
    Iff.of_eq (congrFun (congrFun (congrFun (congrFun
      (congrArg (fun s => s.2.2.2) hs) a) b) c) c')
  refine ⟨h3 a b, fun c => ?_, fun c => ?_, fun c c' => h4 a b c c', fun c c' => ?_⟩
  · rw [der_κ, der_κ, h1]
  · simp only [der_Tf, derTf]
    rw [h1, h2]
  · simp only [der_Λf, derΛf]
    rw [h4, h1, h2]

open DeciNSSE.Packets in

/-- Short realisers of a summary. Every `k`-tuple of level-`(j+1)` letters has a tuple of
sub-words, each shorter than `colBound |C| k`, with the same column summary. -/
theorem exists_short_tuple [Fintype C] [DecidableEq C] (Ws : Fin k → List Γ) :
    ∃ Ws' : Fin k → List Γ, (∀ a, (Ws' a).Sublist (Ws a)) ∧
      (∀ a, (Ws' a).length < colBound (Fintype.card C) k) ∧ summ D ℓ k Ws' = summ D ℓ k Ws := by
  obtain ⟨Ws', h1, h2, h3⟩ := exists_short_conv (fun x => (colDFA D ℓ k).eval x)
    (fun x y a h => by simp only [DFA.eval_append_singleton]; rw [h]) Ws
  refine ⟨Ws', h1, fun a => (h2 a).trans_eq (card_CS k), ?_⟩
  have e1 := colEval D ℓ k _ (valid_conv Ws')
  have e2 := colEval D ℓ k _ (valid_conv Ws)
  rw [dec_conv] at e1 e2
  rw [← e1, ← e2]
  exact h3

/-- For every list `E` of at most `k`
level-`(j+1)` letters (words over the level-`j` alphabet) there is a map `ψ` sending each
`X ∈ E` to a sub-word of `X` of length `< colBound |C| k` and preserving the atomic type of `E`
in `Der(D, ℓ)`. -/
theorem exists_short_letters [Fintype C] [DecidableEq C] (E : List (List Γ))
    (hk : E.length ≤ k) :
    ∃ ψ : List Γ → List Γ, Agree (der D ℓ) (der D ℓ) ψ E ∧
      ∀ X ∈ E, (ψ X).Sublist X ∧ (ψ X).length < colBound (Fintype.card C) k := by
  classical
  set Ws : Fin k → List Γ := fun a => E.getD a.1 [] with hWs
  obtain ⟨Ws', hsub, hlen, hsumm⟩ := exists_short_tuple D ℓ k Ws
  have hT := der_type_of_summ D ℓ k hsumm
  have hidx : ∀ X ∈ E, E.idxOf X < k := fun X hX =>
    (List.idxOf_lt_length_of_mem hX).trans_le hk
  let idx : ∀ X ∈ E, Fin k := fun X hX => ⟨E.idxOf X, hidx X hX⟩
  have hWsidx : ∀ X (hX : X ∈ E), Ws (idx X hX) = X := fun X hX => by
    simp only [hWs, idx]
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hX), List.getElem_idxOf]
  let ψ : List Γ → List Γ := fun X => if hX : X ∈ E then Ws' (idx X hX) else X
  have hψ : ∀ X (hX : X ∈ E), ψ X = Ws' (idx X hX) := fun X hX => dite_eq_left hX
  refine ⟨ψ, ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, fun X hX => ?_⟩
  · intro X hX Y hY hXY
    rw [hψ X hX, hψ Y hY, (hT (idx X hX) (idx Y hY)).1, hWsidx X hX, hWsidx Y hY] at hXY
    exact hXY
  · intro X hX c
    rw [hψ X hX, (hT (idx X hX) (idx X hX)).2.1, hWsidx X hX]
  · intro X hX c
    rw [hψ X hX, (hT (idx X hX) (idx X hX)).2.2.1, hWsidx X hX]
  · intro L L' hL hL'
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · simp [derΛ]
    · simp [derΛ]
    · simp [derΛ]
    · simp only [mapLab_some]
      rw [hψ X hL, hψ Y hL', (hT (idx X hL) (idx Y hL')).2.2.2.1, hWsidx X hL, hWsidx Y hL']
  · intro L L' hL hL'
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · simp [derΛf]
    · simp [derΛf]
    · simp [derΛf]
    · simp only [mapLab_some]
      rw [hψ X hL, hψ Y hL', (hT (idx X hL) (idx Y hL')).2.2.2.2, hWsidx X hL, hWsidx Y hL']
  · rw [hψ X hX]
    refine ⟨?_, hlen _⟩
    have := hsub (idx X hX)
    rwa [hWsidx X hX] at this

end Column

section Cores
universe v
variable {Q : Type v}

instance instFintypeCores [Fintype Q] : ∀ i, Fintype (Cores Q i)
  | 0 => (inferInstance : Fintype Q)
  | i + 1 => by haveI := instFintypeCores i; exact (inferInstance : Fintype (Option (Cores Q i)))

/-- Size of the derived instances. The level-`i` instance has
`|C_i| = N + i` cores (the reader's states and one start core per level). -/
theorem card_cores [Fintype Q] : ∀ i, Fintype.card (Cores Q i) = Fintype.card Q + i
  | 0 => rfl
  | i + 1 => by
      have e : @Fintype.card (Cores Q (i + 1)) (instFintypeCores (i + 1)) =
          Fintype.card (Cores Q i) + 1 := @Fintype.card_option (Cores Q i) (instFintypeCores i)
      rw [e, card_cores i]
      omega

end Cores

section Levels
universe u v
variable {α : Type u} {Q : Type v}

theorem admissible_congr {ℓ ℓ' : (i : ℕ) → Alph α i} : ∀ (j : ℕ), (∀ t < j, ℓ t = ℓ' t) →
    ∀ v : List (Alph α j), Admissible ℓ j v ↔ Admissible ℓ' j v
  | 0, _, _ => Iff.rfl
  | j + 1, h, v => by
      show ((∀ X ∈ v, ℓ j ∉ X) ∧ Admissible ℓ j (expand (ℓ j) v)) ↔
        ((∀ X ∈ v, ℓ' j ∉ X) ∧ Admissible ℓ' j (expand (ℓ' j) v))
      rw [h j (by omega), admissible_congr j (fun t ht => h t (by omega))]

theorem expandTo_congr {ℓ ℓ' : (i : ℕ) → Alph α i} : ∀ (j : ℕ), (∀ t < j, ℓ t = ℓ' t) →
    ∀ v : List (Alph α j), expandTo ℓ j v = expandTo ℓ' j v
  | 0, _, _ => rfl
  | j + 1, h, v => by
      show expandTo ℓ j (expand (ℓ j) v) = expandTo ℓ' j (expand (ℓ' j) v)
      rw [h j (by omega), expandTo_congr j (fun t ht => h t (by omega))]

theorem expandTo_append (ℓ : (i : ℕ) → Alph α i) : ∀ (j : ℕ) (u u' : List (Alph α j)),
    expandTo ℓ j (u ++ u') = expandTo ℓ j u ++ expandTo ℓ j u'
  | 0, _, _ => rfl
  | j + 1, u, u' => by
      show expandTo ℓ j (expand (ℓ j) (u ++ u')) =
        expandTo ℓ j (expand (ℓ j) u) ++ expandTo ℓ j (expand (ℓ j) u')
      rw [expand_append, expandTo_append ℓ j]

theorem expandTo_nil (ℓ : (i : ℕ) → Alph α i) : ∀ j, expandTo ℓ j [] = []
  | 0 => rfl
  | j + 1 => expandTo_nil ℓ j

/-- The level-`0` length of a level-`j` word is the sum of the lengths of its letters. -/
theorem length_expandTo_le (ℓ : (i : ℕ) → Alph α i) (j : ℕ) {B : ℕ} :
    ∀ u : List (Alph α j), (∀ z ∈ u, (expandTo ℓ j [z]).length ≤ B) →
      (expandTo ℓ j u).length ≤ u.length * B
  | [], _ => by simp [expandTo_nil]
  | z :: u, h => by
      rw [show z :: u = [z] ++ u from rfl, expandTo_append, List.length_append,
        List.length_append, List.length_singleton, Nat.add_mul, one_mul]
      have h1 := length_expandTo_le ℓ j u (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have h2 := h z List.mem_cons_self
      omega

theorem length_flatten_le {β : Type*} {B : ℕ} :
    ∀ L : List (List β), (∀ l ∈ L, l.length ≤ B) → L.flatten.length ≤ L.length * B
  | [], _ => by simp
  | l :: L, h => by
      rw [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, one_mul]
      have h1 := length_flatten_le L (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
      have h2 := h l List.mem_cons_self
      omega

/-- The size bound: `sizeB N 0 k = 1`; a level-`(j+1)` letter of a `k`-tuple is shortened to at
most `colBound (N + j) k` level-`j` letters (its body and the marker), each of size at most
`sizeB N j (1 + k · colBound (N + j) k)`. -/
def sizeB (N : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | j + 1, k => colBound (N + j) k * sizeB N j (1 + k * colBound (N + j) k)

theorem shorten_level (D0 : Lettered α Q) [Fintype Q] :
    ∀ (j k : ℕ) (ℓ : (i : ℕ) → Alph α i) (E : List (Alph α j)), E.length ≤ k →
      Admissible ℓ j E →
      ∃ (ℓ' : (i : ℕ) → Alph α i) (φ : Alph α j → Alph α j),
        Agree (tower D0 ℓ j) (tower D0 ℓ' j) φ E ∧ Admissible ℓ' j (E.map φ) ∧
        ∀ x ∈ E, (expandTo ℓ' j [φ x]).length ≤ sizeB (Fintype.card Q) j k
  | 0, k, ℓ, E, _, _ => ⟨ℓ, id, Agree.refl _ _, trivial, fun x _ => by simp [expandTo, sizeB]⟩
  | j + 1, k, ℓ, E, hk, hadm => by
      classical
      by_cases hE : E = []
      · subst hE
        exact ⟨ℓ, id, Agree.refl _ _, hadm, by simp⟩
      set N := Fintype.card Q with hN
      set D := tower D0 ℓ j with hD
      obtain ⟨ψ, hψA, hψ⟩ := exists_short_letters D (ℓ j) k E hk
      rw [card_cores j] at hψ
      set Ebig : List (Alph α j) := ℓ j :: (E.map ψ).flatten with hEbig
      have hmemBig : ∀ X ∈ E, ∀ a ∈ ψ X, a ∈ Ebig := fun X hX a ha =>
        List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨ψ X, List.mem_map_of_mem hX, ha⟩)
      have hℓBig : ℓ j ∈ Ebig := List.mem_cons_self
      have hlenBig : Ebig.length ≤ 1 + k * colBound (N + j) k := by
        have h1 := length_flatten_le (B := colBound (N + j) k) (E.map ψ) (by
          intro l hl
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hl
          exact (hψ X hX).2.le)
        rw [List.length_map] at h1
        have h2 := Nat.mul_le_mul_right (colBound (N + j) k) hk
        simp only [hEbig, List.length_cons]
        omega
      have hadmBig : Admissible ℓ j Ebig := by
        refine admissible_of_subset ℓ j Ebig (expand (ℓ j) E) hadm.2
          (by simpa [expand_eq_nil] using hE) ?_
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · obtain ⟨X, hX⟩ := List.exists_mem_of_ne_nil E hE
          exact mem_expand.mpr ⟨X, hX, by simp⟩
        · obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp ha
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hl
          exact mem_expand.mpr ⟨X, hX, List.mem_append_left _ ((hψ X hX).1.subset hal)⟩
      obtain ⟨ℓ'', φ₀, hA, hadm'', hsize⟩ :=
        shorten_level D0 j (1 + k * colBound (N + j) k) ℓ Ebig hlenBig hadmBig
      set ℓ' : (i : ℕ) → Alph α i := Function.update ℓ'' j (φ₀ (ℓ j)) with hℓ'
      have hℓ'j : ℓ' j = φ₀ (ℓ j) := Function.update_self _ _ _
      have hℓ'lt : ∀ t < j, ℓ' t = ℓ'' t := fun t ht =>
        Function.update_of_ne (by omega) _ _
      have htw : tower D0 ℓ' j = tower D0 ℓ'' j := tower_congr D0 j hℓ'lt
      have htw1 : tower D0 ℓ' (j + 1) = der (tower D0 ℓ'' j) (φ₀ (ℓ j)) := by
        show der (tower D0 ℓ' j) (ℓ' j) = _
        rw [htw, hℓ'j]
      refine ⟨ℓ', fun X => (ψ X).map φ₀, ?_, ?_, ?_⟩
      · rw [htw1]
        exact hψA.comp (hA.derive hℓBig (E.map ψ) (by
          intro Y hY a ha
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
          exact hmemBig X hX a ha))
      · refine ⟨?_, ?_⟩
        · intro Y hY hmem
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
          rw [hℓ'j] at hmem
          obtain ⟨z, hz, hzeq⟩ := List.mem_map.mp hmem
          have hzℓ := hA.inj z (hmemBig X hX z hz) (ℓ j) hℓBig hzeq
          rw [hzℓ] at hz
          exact hadm.1 X hX ((hψ X hX).1.subset hz)
        · rw [hℓ'j, admissible_congr j hℓ'lt]
          refine admissible_of_subset ℓ'' j _ (Ebig.map φ₀) hadm'' (by simp) ?_
          intro a ha
          obtain ⟨Y, hY, haY⟩ := mem_expand.mp ha
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
          rcases List.mem_append.mp haY with h1 | h1
          · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h1
            exact List.mem_map_of_mem (hmemBig X hX z hz)
          · rw [List.mem_singleton] at h1
            rw [h1]
            exact List.mem_map_of_mem hℓBig
      · intro X hX
        have e1 : expandTo ℓ' (j + 1) [(ψ X).map φ₀] =
            expandTo ℓ'' j ((ψ X ++ [ℓ j]).map φ₀) := by
          show expandTo ℓ' j (expand (ℓ' j) [(ψ X).map φ₀]) = _
          rw [expandTo_congr j hℓ'lt, hℓ'j]
          simp [expand]
        rw [e1]
        refine (length_expandTo_le ℓ'' j _ (B := sizeB N j (1 + k * colBound (N + j) k))
          ?_).trans ?_
        · intro z hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
          refine hsize y ?_
          rcases List.mem_append.mp hy with h1 | h1
          · exact hmemBig X hX y h1
          · rw [List.mem_singleton] at h1
            rw [h1]
            exact hℓBig
        · show _ ≤ colBound (N + j) k * sizeB N j (1 + k * colBound (N + j) k)
          rw [List.length_map, List.length_append, List.length_singleton]
          exact Nat.mul_le_mul_right _ (hψ X hX).2

end Levels

section Final
universe u v
variable {α : Type u} {Q : Type v}

/-- The computable length bound for a hole in `𝓛(d)` of an instance with `N` cores: at a
unary level `i` the top word `x^m` has `m ≤ N + i`, and the letter `x` expands to at most
`sizeB N i 1` letters. -/
def holeBound (N d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d + 1), (N + i) * sizeB N i 1

variable [DecidableEq α] [Inhabited α]

/-- If a lettered instance with `N` cores (over any alphabet) has a hole in `𝓛(d)`, it has
one of length `≤ holeBound N d`. At the unary level `i` a short power `x^m` is a hole of the
derived instance; shortening the single letter `x` and expanding gives the witness. Nothing is
assumed about the variety, degeneracy or run lengths of the levels below the top. -/
theorem exists_short_hole_InL (D0 : Lettered α Q) [Fintype Q] (d : ℕ) {w : List α}
    (hw : D0.IsHole w) (hL : InL d w) :
    ∃ w', D0.IsHole w' ∧ InL d w' ∧ w'.length ≤ holeBound (Fintype.card Q) d := by
  classical
  obtain ⟨i, hi, hu⟩ := hL
  have hw0 : w ≠ [] := hw.ne_nil
  set N := Fintype.card Q with hN
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hierOf_ne_nil hw0 i)
  have hrep : hierOf w i = List.replicate (hierOf w i).length x :=
    List.eq_replicate_iff.mpr ⟨rfl, fun b hb => hu b hb x hx⟩
  have hv : (tower D0 (markOf w) i).IsHole (hierOf w i) := (isHole_hierOf_iff hw0 D0 i).mpr hw
  obtain ⟨m, -, hmN, hm⟩ := (exists_unary_hole_iff (tower D0 (markOf w) i) x).mp
    ⟨(hierOf w i).length, by rw [← hrep]; exact hv⟩
  rw [card_cores i] at hmN
  have hadm : Admissible (markOf w) i [x] :=
    admissible_of_subset _ i [x] _ (admissible_hierOf hw0 i) (hierOf_ne_nil hw0 i)
      fun a ha => by rw [List.mem_singleton.mp ha]; exact hx
  obtain ⟨ℓ', φ, hA, hadm', hsize⟩ := shorten_level D0 i 1 (markOf w) [x] le_rfl hadm
  have hv' : (tower D0 ℓ' i).IsHole (List.replicate m (φ x)) := by
    rw [← List.map_replicate]
    exact (hA.isHole_iff fun a ha => List.mem_singleton.mpr (List.eq_of_mem_replicate ha)).mpr hm
  have hadm₂ : Admissible ℓ' i (List.replicate m (φ x)) :=
    admissible_of_subset ℓ' i _ _ hadm' (by simp) fun a ha => by
      rw [List.eq_of_mem_replicate ha]; exact List.mem_map_of_mem (List.mem_singleton_self x)
  refine ⟨expandTo ℓ' i (List.replicate m (φ x)),
    (isHole_tower_iff D0 ℓ' i _ hadm₂ hv'.ne_nil).mp hv', ⟨i, hi, ?_⟩, ?_⟩
  · rw [(hierOf_expandTo ℓ' i _ hadm₂ hv'.ne_nil).1]
    intro a ha b hb
    rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  · calc (expandTo ℓ' i (List.replicate m (φ x))).length
          ≤ (List.replicate m (φ x)).length * sizeB N i 1 :=
          length_expandTo_le ℓ' i _ fun z hz => by
            rw [List.eq_of_mem_replicate hz]; exact hsize x (List.mem_singleton_self x)
      _ ≤ (N + i) * sizeB N i 1 := by
          rw [List.length_replicate]; exact Nat.mul_le_mul_right _ hmN
      _ ≤ holeBound N d :=
          Finset.single_le_sum (f := fun i => (N + i) * sizeB N i 1)
            (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

theorem exists_hole_InL_iff_bounded (D0 : Lettered α Q) [Fintype Q] (d : ℕ) :
    (∃ w, D0.IsHole w ∧ InL d w) ↔
      ∃ w, D0.IsHole w ∧ InL d w ∧ w.length ≤ holeBound (Fintype.card Q) d :=
  ⟨fun ⟨_, hw, hL⟩ => exists_short_hole_InL D0 d hw hL, fun ⟨w, hw, hL, _⟩ => ⟨w, hw, hL⟩⟩

end Final

section Monitor
universe u v
open DeciNSSE.Holes

instance decIsUnary {β : Type*} [DecidableEq β] (u : List β) : Decidable (IsUnary u) :=
  inferInstanceAs (Decidable (∀ a ∈ u, ∀ b ∈ u, a = b))

variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

omit [DecidableEq α] [Inhabited α] in
theorem isHole_ofReader_iff' (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) :
    (ofReader M R T).IsHole w ↔ w ≠ [] ∧ IsReaderHole M R T w :=
  ⟨fun h => ⟨h.ne_nil, (isHole_ofReader_iff M R T h.ne_nil).mp h⟩,
    fun ⟨h0, h⟩ => (isHole_ofReader_iff M R T h0).mpr h⟩

/-- A reader `(M, R, T)` with `N` states having a
hole in `𝓛(d)` has one of length `≤ holeBound N d`. -/
theorem exists_reader_hole_InL_iff_bounded (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [Fintype Q] (d : ℕ) :
    (∃ w, w ≠ [] ∧ IsReaderHole M R T w ∧ InL d w) ↔
      ∃ w, w ≠ [] ∧ IsReaderHole M R T w ∧ InL d w ∧
        w.length ≤ holeBound (Fintype.card Q) d := by
  have := exists_hole_InL_iff_bounded (ofReader M R T) d
  simp only [isHole_ofReader_iff', and_assoc] at this
  exact this

end Monitor

end DeciNSSE.BoundedDepth
