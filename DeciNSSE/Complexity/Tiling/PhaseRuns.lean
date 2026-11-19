import DeciNSSE.Complexity.Tiling.CutGeometry

/-! # Independent regular checks of a repeated packet

## Main declarations

- `copies_final` expresses a target run on repeated packets as one probe
  traversal and one master traversal for each physical checker.
-/

namespace DeciNSSE.Complexity.Tiling.Controller
open scoped List
variable {D : Type*} [DecidableEq D] (I : Square D)

/-- Render the selected packet field together with the delimiter that ends its traversal. -/
def regionText (P : Packet (CellLetter D)) (m : Bool) :=
  P.field m ++ [if m then Token.stop else .bang]

/-- A completed probe traversal starts the master of the same copy. Completing the master
advances to the next copy or the final control. -/
def finishes (j : ℕ) (m : Bool) := if m then afterMaster I j else beginPhase D j true

/-- Every successful run through a complete field ends at the prescribed control for that
traversal. -/
theorem region_finish {P : Packet (CellLetter D)} {m : Bool} {j r}
    (success : run I (beginPhase D j m) (regionText P m) = some r) : r = finishes I j m := by
  obtain ⟨q,hq,he⟩ := (run_split I).mp success
  have ok : WellPhased I (beginPhase D j m) := by simp [WellPhased,beginPhase]
  have label := paint_run I ok hq
  change paint q = (P.field m).foldl _ (some (fresh j m)) at label
  rw [fold_field _ j m _ (plain_field P m)] at label
  cases q with
  | none => cases label
  | some s =>
    have copy := congrArg Paint.copy (Option.some.inj label)
    have master := congrArg Paint.master (Option.some.inj label)
    change s.copy = j at copy; change s.master = m at master
    cases m with
    | false =>
      have st : tokenStep I (some s) .bang = some r := by simpa [run] using he
      exact (step_shape I (phased_run I ok hq) st).2.2.trans (by rw [copy]; rfl)
    | true =>
      have st : tokenStep I (some s) .stop = some r := by simpa [run] using he
      rcases step_shape I (phased_run I ok hq) st with ⟨h,_⟩ | ⟨_,h⟩
      · simp_all
      · exact h.trans (by rw [copy]; rfl)

/-- Repeating a packet reaches the final control exactly when its probe and master traversals
succeed in every copy. -/
theorem copies_final (P : Packet (CellLetter D)) :
    run I (beginPhase D 0 false) (copies I P) = some none ↔
      ∀ j ≤ 2*I.p, ∀ m,
        run I (beginPhase D j m) (regionText P m) = some (finishes I j m) := by
  let ok (j : ℕ) := ∀ m, run I (beginPhase D j m) (regionText P m) = some (finishes I j m)
  have packet (j) (r) :
      run I (beginPhase D j false) P.render = some r ↔ ok j ∧ r = afterMaster I j := by
    have eq : P.render = regionText P false ++ regionText P true := by
      simp [Packet.render,regionText,Packet.field,List.append_assoc]
    rw [eq,run_split]
    constructor
    · rintro ⟨q,hq,hr⟩
      have e₁ := region_finish I hq
      subst q
      have e₂ := region_finish (P := P) (m := true) I hr
      exact ⟨fun m => by cases m <;> [exact hq; exact e₂ ▸ hr],e₂⟩
    · rintro ⟨h,rfl⟩; exact ⟨_,h false,h true⟩
  have repeat_ok (l : ℕ) (j : ℕ) (len : j+l=2*I.p) :
      run I (beginPhase D j false) (List.replicate (l+1) P.render).flatten = some none ↔
        ∀ i, j ≤ i → i ≤ 2*I.p → ok i := by
    induction l generalizing j with
    | zero =>
      simp only [List.replicate_succ,List.replicate_zero,
        List.flatten_cons,List.flatten_nil,List.append_nil]
      rw [packet]
      have he : j = 2*I.p := by omega
      simp only [afterMaster,he,ite_true,and_true]
      exact ⟨fun h i lo hi => (le_antisymm hi lo).symm ▸ h,fun h => h _ le_rfl le_rfl⟩
    | succ l ih =>
      rw [List.replicate_succ,List.flatten_cons,run_split]
      simp only [packet,afterMaster,ite_eq_right (by omega : j ≠ 2*I.p)]
      constructor
      · rintro ⟨_,⟨h,rfl⟩,ht⟩ i lo hi
        rcases Nat.eq_or_lt_of_le lo with rfl | lt
        · exact h
        · exact (ih (j+1) (by omega)).mp ht i lt hi
      · intro h
        exact ⟨_,⟨h j le_rfl (by omega),rfl⟩,
          (ih (j+1) (by omega)).mpr (fun i hi => h i (by omega))⟩
  simpa only [copies, Nat.zero_le, forall_const] using repeat_ok (2*I.p) 0 (by omega)

end DeciNSSE.Complexity.Tiling.Controller
