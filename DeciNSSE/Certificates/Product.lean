import DeciNSSE.Holes.Packets
import DeciNSSE.Words

/-! # Finite covering products

Terminal comparisons and admitted periodic rays give finite-state sufficient
conditions for a word not to be a reader hole. Access words describe a finite
closed set of product states.
-/

set_option autoImplicit false
namespace DeciNSSE.Certificates
open Holes Words
open scoped List

variable {α Q : Type*} [DecidableEq α] [DecidableEq Q]

/-- A ray is specified by an access word and a nonempty period. -/
structure Ray (α : Type*) where
  access : List α
  period : List α
  deriving DecidableEq

/-- A position in a ray records the unread part of the current period. -/
structure Position (α : Type*) where
  ray : Ray α
  rest : List α
  mature : Bool
  deriving DecidableEq

/-- The finite memory used to cover words. -/
structure ProductState (α Q : Type*) where
  reader : Q
  roots : Finset (Q × List α)
  residuals : Finset (List α)
  active : Finset (Position α)
  deriving DecidableEq

variable (M : DFA α Q) (R : Q → Q → Prop) [DecidableRel R]

omit [DecidableEq α] [DecidableEq Q] in
theorem eval_append (u v : List α) : M.eval (u ++ v) = M.evalFrom (M.eval u) v :=
  M.evalFrom_of_append M.start u v

/-- Rays beginning at the current reader state. -/
def starts (rays : List (Ray α)) (q : Q) : Finset (Position α) :=
  (rays.filter fun r => M.eval r.access = q).toFinset.image fun r => ⟨r, r.period, false⟩

/-- Consume one letter at a ray position, cycling after a full period. -/
def advance (a : α) (p : Position α) : Finset (Position α) :=
  match p.rest with
  | [] => ∅
  | c :: t => if c = a then
      {⟨p.ray, if t = [] then p.ray.period else t, p.mature || decide (t = [])⟩}
    else ∅

/-- Initial product state. -/
def initial (rays : List (Ray α)) : ProductState α Q :=
  ⟨M.start, ∅, ∅, starts M rays M.start⟩

/-- Extend pending roots, retaining at most the window length. -/
def nextRoots (b : ℕ) (s : ProductState α Q) (a : α) : Finset (Q × List α) :=
  insert (s.reader, [a].take b)
    (s.roots.image fun p => (p.1, (p.2 ++ [a]).take b))

/-- Deterministic covering-product transition. -/
def step (b : ℕ) (rays : List (Ray α)) (s : ProductState α Q) (a : α) :
    ProductState α Q :=
  let q := M.step s.reader a
  let roots := nextRoots b s a
  let tails := s.residuals.biUnion fun t => match t with
    | [] => ∅
    | c :: t => if c = a then {t} else ∅
  let fresh := (roots.filter fun p => R p.1 q).image fun p => (pow p.2 b).take b
  ⟨q, roots, tails ∪ fresh,
    s.active.biUnion (advance a) ∪ starts M rays q⟩

/-- Product state reached by a word. -/
def run (b : ℕ) (rays : List (Ray α)) (w : List α) : ProductState α Q :=
  w.foldl (step M R b rays) (initial M rays)

@[simp] theorem run_nil (b : ℕ) (rays : List (Ray α)) :
    run M R b rays [] = initial M rays := rfl

@[simp] theorem run_append (b : ℕ) (rays : List (Ray α)) (w : List α) (a : α) :
    run M R b rays (w ++ [a]) = step M R b rays (run M R b rays w) a := by
  simp [run, List.foldl_append]

/-- A ray's period witnesses admission at its starting state. -/
def ValidRay (r : Ray α) : Prop :=
  r.period ≠ [] ∧ R (M.eval r.access) (M.eval (r.access ++ r.period))

instance (r : Ray α) : Decidable (ValidRay M R r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A comparison with a finite continuation still to be read. -/
def Pending (w t : List α) : Prop :=
  ∃ u v z, w = u ++ v ++ z ∧ v ≠ [] ∧
    R (M.eval u) (M.eval (u ++ v)) ∧ z ++ t <+: v ++ z ++ t

/-- The semantic meaning of an active ray position. -/
def Tracks (w : List α) (p : Position α) : Prop :=
  ValidRay M R p.ray ∧ ∃ u z j, w = u ++ z ∧ M.eval u = M.eval p.ray.access ∧
    z ++ p.rest = pow p.ray.period (j + 1) ∧
    (p.mature = true → p.ray.period.length ≤ z.length)

/-- Every stored item has a witness along the input word. -/
def Invariant (b : ℕ) (w : List α) (s : ProductState α Q) : Prop :=
  s.reader = M.eval w ∧
  (∀ p ∈ s.roots, ∃ u v, w = u ++ v ∧ v ≠ [] ∧ p.1 = M.eval u ∧ p.2 = v.take b) ∧
  (∀ t ∈ s.residuals, Pending M R w t) ∧
  (∀ p ∈ s.active, Tracks M R w p)

omit [DecidableEq α] in
private theorem pow_append (v : List α) (j : ℕ) : pow v j ++ v = pow v (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih => simpa only [Words.pow_succ, List.append_assoc] using congrArg (v ++ ·) ih

omit [DecidableEq α] in
private theorem prefix_short {t v : List α} {b : ℕ} (ht : t.length ≤ b)
    (h : t <+: v.take b ++ t) : t <+: v ++ t := by
  by_cases hv : v.length ≤ b
  · simpa [List.take_of_length_le hv] using h
  · have ht' : t.length ≤ (v.take b).length := by simp; omega
    exact ((List.isPrefix_append_of_length ht').mp h).trans
      ((List.take_prefix b v).trans (List.prefix_append v t))

omit [DecidableEq α] in
private theorem prefix_cancel_future {z v t : List α}
    (h : z ++ t <+: v ++ z ++ t) : z <+: v ++ z := by
  exact (List.isPrefix_append_of_length (by simp)).mp ((List.prefix_append z t).trans h)

omit [DecidableEq α] [DecidableEq Q] [DecidableRel R] in
/-- A pending comparison already prevents a hole before its continuation. -/
theorem pending_not_hole (T : Set Q) {w t : List α} (h : Pending M R w t) :
    ¬ IsReaderHole M R T w := by
  obtain ⟨u, v, z, rfl, hv, hr, hp⟩ := h
  intro hh
  have hn := (isReaderHole_iff M R T _).mp hh |>.2
  apply hn u.length (u ++ v).length
  · have := List.length_pos_iff.mpr hv
    simp only [List.length_append]; omega
  · simp
  · rw [List.drop_left, List.append_assoc, List.drop_left]
    exact prefix_cancel_future hp
  · rw [List.take_left, List.append_assoc, List.take_left]
    exact hr

omit [DecidableRel R] in
private theorem starts_tracks (rays : List (Ray α)) (hv : ∀ r ∈ rays, ValidRay M R r)
    (w : List α) (p : Position α) (hp : p ∈ starts M rays (M.eval w)) : Tracks M R w p := by
  simp only [starts, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq] at hp
  obtain ⟨r, ⟨hr, hq⟩, rfl⟩ := hp
  exact ⟨hv r hr, w, [], 0, by simp, hq.symm, by simp, by simp⟩

omit [DecidableEq Q] [DecidableRel R] in
private theorem advance_tracks {w : List α} {p p' : Position α} {a : α}
    (h : Tracks M R w p) (hp : p' ∈ advance a p) : Tracks M R (w ++ [a]) p' := by
  obtain ⟨hv, u, z, j, hw, hq, hz, hm⟩ := h
  cases ht : p.rest with
  | nil => simp [advance, ht] at hp
  | cons c t =>
    simp only [advance, ht] at hp
    split at hp <;> rename_i ha
    · subst c
      simp only [Finset.mem_singleton] at hp
      subst p'
      refine ⟨hv, u, z ++ [a], if t = [] then j + 1 else j, ?_, hq, ?_, ?_⟩
      · simp [hw, List.append_assoc]
      · by_cases he : t = []
        · subst t
          change (z ++ [a]) ++ p.ray.period = pow p.ray.period (j + 1 + 1)
          rw [← pow_append]
          congr 1
          simpa [ht] using hz
        · simpa [he, ht, List.append_assoc] using hz
      · simp only [Bool.or_eq_true, decide_eq_true_eq]
        rintro (hm' | he)
        · have := hm hm'; simp only [List.length_append, List.length_singleton]; omega
        · subst t
          have hl := congrArg List.length hz
          simp only [ht, List.length_append, List.length_cons, List.length_nil, length_pow] at hl
          have := Nat.le_mul_of_pos_left p.ray.period.length (show 0 < j + 1 by omega)
          simp only [List.length_append, List.length_singleton]; omega
    · simp at hp

omit [DecidableEq α] [DecidableEq Q] [DecidableRel R] in
/-- A mature admitted ray supplies a suffix comparison. -/
theorem tracks_not_hole (T : Set Q) {w : List α} {p : Position α}
    (h : Tracks M R w p) (hm : p.mature = true) : ¬ IsReaderHole M R T w := by
  obtain ⟨⟨hv, hr⟩, u, z, j, rfl, hq, hz, hlen⟩ := h
  have hp : z <+: pow p.ray.period (j + 1) := ⟨p.rest, hz⟩
  have hvz : p.ray.period <+: z :=
    List.prefix_of_prefix_length_le (by simp only [Words.pow_succ]; exact List.prefix_append _ _) hp (hlen hm)
  obtain ⟨t, rfl⟩ := hvz
  have ht : t <+: pow p.ray.period j := by
    simpa only [Words.pow_succ, List.prefix_append_right_inj] using hp
  apply pending_not_hole M R T (t := [])
  refine ⟨u, p.ray.period, t, by simp [List.append_assoc], hv, ?_, ?_⟩
  · simpa only [eval_append, hq] using hr
  · simpa using prefix_append_of_prefix_pow j ht

omit [DecidableEq α] in
private theorem take_extend (v : List α) (b : ℕ) (a : α) :
    (v.take b ++ [a]).take b = (v ++ [a]).take b := by
  by_cases h : v.length ≤ b
  · rw [List.take_of_length_le h]
  · rw [List.take_append_of_le_length (by simp; omega), List.take_take,
      min_self, List.take_append_of_le_length (by omega)]

omit [DecidableRel R] in
private theorem roots_witness (b : ℕ) {w : List α} {s : ProductState α Q}
    (h : Invariant M R b w s) (a : α) {p : Q × List α} (hp : p ∈ nextRoots b s a) :
    ∃ u v, w ++ [a] = u ++ v ∧ v ≠ [] ∧ p.1 = M.eval u ∧ p.2 = v.take b := by
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact ⟨w, [a], rfl, by simp, h.1, rfl⟩
  · obtain ⟨p₀, hp₀, he⟩ := Finset.mem_image.mp hp
    subst p
    obtain ⟨u, v, hw, hv, hq, ht⟩ := h.2.1 p₀ hp₀
    exact ⟨u, v ++ [a], by simp [hw, List.append_assoc], by simp,
      hq, by simp only [ht, take_extend]⟩

/-- The semantic witnesses are preserved by each product transition. -/
theorem invariant_step (b : ℕ) (rays : List (Ray α))
    (hv : ∀ r ∈ rays, ValidRay M R r) {w : List α} {s : ProductState α Q}
    (h : Invariant M R b w s) (a : α) :
    Invariant M R b (w ++ [a]) (step M R b rays s a) := by
  refine ⟨by simpa only [step, DFA.eval_append_singleton] using congrArg (M.step · a) h.1,
    (fun _ hp => roots_witness M R b h a hp), ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨r, hr, ht⟩ := Finset.mem_biUnion.mp ht
      cases r with
      | nil => simp at ht
      | cons c r =>
        change t ∈ (if c = a then {r} else ∅) at ht
        split at ht <;> rename_i ha
        · subst c
          obtain rfl := Finset.mem_singleton.mp ht
          obtain ⟨u, v, z, hw, hn, hadm, hp⟩ := h.2.2.1 _ hr
          refine ⟨u, v, z ++ [a], by simp [hw, List.append_assoc], hn, hadm, ?_⟩
          simpa only [List.append_assoc, List.singleton_append] using hp
        · simp at ht
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hp, hadm⟩ := Finset.mem_filter.mp hp
      obtain ⟨u, v, hw, hn, hq, ht⟩ := roots_witness M R b h a hp
      refine ⟨u, v, [], by simpa using hw, hn, ?_, ?_⟩
      · rw [hq, h.1, ← DFA.eval_append_singleton, hw] at hadm
        exact hadm
      · simp only [List.nil_append, List.append_nil]
        apply prefix_short (b := b) (by simp)
        rw [ht]
        exact prefix_append_of_prefix_pow b (List.take_prefix b _)
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨p', hp', ha⟩ := Finset.mem_biUnion.mp hp
      exact advance_tracks M R (h.2.2.2 p' hp') ha
    · rw [h.1, ← DFA.eval_append_singleton] at hp
      exact starts_tracks M R rays hv _ _ hp

/-- All reachable product states carry valid comparison witnesses. -/
theorem run_invariant (b : ℕ) (rays : List (Ray α))
    (hv : ∀ r ∈ rays, ValidRay M R r) (w : List α) :
    Invariant M R b w (run M R b rays w) := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, by simp [initial], by simp [initial], ?_⟩
    exact starts_tracks M R rays hv []
  | append_singleton w a ih =>
    rw [run_append]
    exact invariant_step M R b rays hv ih a

variable (T : Set Q) [DecidablePred (· ∈ T)]

/-- Acceptance, a terminal residual, or a mature ray covers the current word. -/
def Covered (s : ProductState α Q) : Prop :=
  s.reader ∉ T ∨ s.residuals.Nonempty ∨ ∃ p ∈ s.active, p.mature = true

instance (s : ProductState α Q) : Decidable (Covered T s) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

omit [DecidablePred (· ∈ T)] in
/-- Coverage of a reachable product state rules out a reader hole. -/
theorem covered_not_hole (b : ℕ) (rays : List (Ray α))
    (hv : ∀ r ∈ rays, ValidRay M R r) (w : List α)
    (hc : Covered T (run M R b rays w)) : ¬ IsReaderHole M R T w := by
  have h := run_invariant M R b rays hv w
  rcases hc with hc | ⟨t, ht⟩ | ⟨p, hp, hm⟩
  · intro hh
    exact hc (h.1 ▸ (isReaderHole_iff M R T w).mp hh |>.1)
  · exact pending_not_hole M R T (h.2.2.1 t ht)
  · exact tracks_not_hole M R T (h.2.2.2 p hp) hm

/-- A side certificate supplies a window, rays, and access words for a closed cover. -/
structure Cover (α : Type*) where
  window : ℕ
  rays : List (Ray α)
  access : List (List α)

variable [Fintype α]

/-- Check ray admissions, initial membership, coverage, and closure under letters. -/
def checkCover (cert : Cover α) : Bool :=
  let states := (cert.access.map (run M R cert.window cert.rays)).toFinset
  decide ((∀ r ∈ cert.rays, ValidRay M R r) ∧ initial M cert.rays ∈ states ∧
    ∀ s ∈ states, Covered T s ∧ ∀ a, step M R cert.window cert.rays s a ∈ states)

/-- A closed cover contains the product state of every word. -/
theorem checkCover_sound (cert : Cover α) (hc : checkCover M R T cert = true) :
    ∀ w, ¬ IsReaderHole M R T w := by
  simp only [checkCover, decide_eq_true_eq] at hc
  obtain ⟨hr, hi, hs⟩ := hc
  have reach (w : List α) : run M R cert.window cert.rays w ∈
      (cert.access.map (run M R cert.window cert.rays)).toFinset := by
    induction w using List.reverseRecOn with
    | nil => exact hi
    | append_singleton w a ih =>
      rw [run_append]
      exact (hs _ ih).2 a
  intro w
  exact covered_not_hole M R T cert.window cert.rays hr w (hs _ (reach w)).1

end DeciNSSE.Certificates
