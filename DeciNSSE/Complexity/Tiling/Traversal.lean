import DeciNSSE.Complexity.Tiling.CellStep

/-! # Finite-state verification of an ordered traversal

## Main declarations

- `Tape` represents the master text or the list of probes in a packet.
- `read_traversal` equates simultaneous success of the individual checkers
  with an ordered list of records satisfying the local tests.
-/

namespace DeciNSSE.Complexity.Tiling.Controller
open scoped List
variable {D : Type*} [DecidableEq D] (I : Square D)

/-- A master traversal reads one data word. A probe traversal reads a list of probe words, each
of which has an exposed record. -/
inductive Tape (D : Type*) : Bool → Type _
  /-- The data to scan in the master field. -/
  | master (data : List (CellLetter D)) : Tape D true
  /-- The individual data words to scan in the probe field. -/
  | probes (xs : List (List (CellLetter D))) : Tape D false

namespace Tape
section
omit [DecidableEq D]

/-- The empty traversal contains no records in the selected region. -/
def empty : (m : Bool) → Tape D m
  | true => .master []
  | false => .probes []

/-- Render a traversal as a token word including its closing delimiter. -/
def text {m} : Tape D m → List (Letter D)
  | .master x => x.map Token.data ++ [.stop]
  | .probes xs => probeText xs ++ [.bang]

/-- Prepend one cell record to the traversal, retaining its payload in the probe case. -/
def put {m} (a : Addr I.p) (d : D) (payload : List (CellLetter D)) : Tape D m → Tape D m
  | .master xs => .master (record I.p a.1 a.2 d ++ xs)
  | .probes xs => .probes ((record I.p a.1 a.2 d ++ payload) :: xs)

/-- Prepending a cell to a traversal prefixes its rendered word by the corresponding cell text. -/
@[simp] theorem put_text {m} (a : Addr I.p) (d payload) (t : Tape D m) :
    (put I a d payload t).text = cellText I m a d payload ++ t.text := by
  cases t <;> simp [put,text,cellText,probeText,List.append_assoc]

private theorem data_prefix {x xs : List (CellLetter D)} {a : Token (CellLetter D)}
    (ha : ∀ z, a ≠ .data z) (t : List (Letter D))
    (hp : x.map Token.data <+: xs.map Token.data ++ a :: t) : x <+: xs := by
  induction x generalizing xs with
  | nil => simp
  | cons d x ih =>
    cases xs with
    | nil => simp_all [List.cons_prefix_cons]; exact ha d hp.1.symm
    | cons d' xs =>
      simp only [List.map_cons,List.cons_append,List.cons_prefix_cons,Token.data.injEq] at hp ⊢
      exact ⟨hp.1,ih hp.2⟩

/-- A traversal whose text starts with a complete record splits into that cell, its possible
payload and the remaining traversal. -/
theorem parse_front {m} (t : Tape D m) (a : Addr I.p) (d)
    (h : (record I.p a.1 a.2 d).map Token.data <+: t.text) :
    ∃ payload rest, t = put I a d payload rest := by
  cases t with
  | master xs =>
    obtain ⟨rest,hr⟩ := data_prefix (a := Token.stop) (by simp) [] h
    exact ⟨[],.master rest,congrArg Tape.master hr.symm⟩
  | probes xs =>
    cases xs with
    | nil => simp [record,text,probeText] at h
    | cons x xs =>
      change _ <+: (x.map Token.data ++ [Token.stop] ++ _) ++ [.bang] at h
      simp only [List.append_assoc,List.cons_append] at h
      obtain ⟨payload,hr⟩ := data_prefix (a := Token.stop) (by simp) _ h
      exact ⟨payload,.probes xs,by rw [← hr]; rfl⟩

end

/-- A successful nonempty traversal starting at a record boundary begins with the record marker. -/
theorem nonempty_marker {m} {r : Registers D} {j : Guard I.p} {i prev} (fr : Frame I r j m i prev)
    (t : Tape D m) (nonempty : t ≠ empty m) {endState}
    (h : run I (some r) t.text = some endState) : [Token.data CellLetter.record] <+: t.text := by
  have zero := fr.2.2.1
  have mode := fr.2.1
  have must {x : CellLetter D} {rest : List (Letter D)}
      (eq : t.text = .data x :: rest) : x = .record := by
    rw [eq] at h
    obtain ⟨q, step, _⟩ := Option.bind_eq_some_iff.mp h
    cases x <;> simp_all [tokenStep]
  cases t with
  | master xs =>
    cases xs with
    | nil => exact (nonempty rfl).elim
    | cons x xs =>
      rw [must (x := x) rfl]; exact ⟨_,rfl⟩
  | probes xs =>
    cases xs with
    | nil => exact (nonempty rfl).elim
    | cons x xs =>
      cases x with
      | nil =>
        obtain ⟨q,step,_⟩ := Option.bind_eq_some_iff.mp h
        change tokenStep I (some r) Token.stop = some q at step
        simp [tokenStep,zero,mode] at step
      | cons a x => rw [must (x := a) rfl]; exact ⟨_,rfl⟩

end Tape

omit [DecidableEq D] in
private theorem cannot_finish {m} (j : Guard I.p) (r : Registers D) (mode : r.master=m) :
    some r ≠ finishes I j m := by
  cases m with
  | false => intro h; cases Option.some.inj h; cases mode
  | true =>
    unfold finishes afterMaster
    by_cases last : j.val = 2*I.p
    · simp [last]
    · simp only [ite_true,ite_eq_right last]; intro h; cases Option.some.inj h; cases mode

/-- At a nonempty traversal the checker for slot `i` forces precisely that
physical bit. Every successful copy must also reach the tile slot. -/
private theorem first_record {m i prev} (rs : Guard I.p → Registers D)
    (frame : ∀ j, Frame I (rs j) j m i prev)
    (T : Tape D m) (hn : T ≠ Tape.empty m) (a : Addr I.p) (index : Addr.index m a=i)
    (accept : ∀ j, run I (some (rs j)) T.text = some (finishes I j m)) :
    ∃ d, (record I.p a.1 a.2 d).map Token.data <+: T.text := by
  let last : Guard I.p := ⟨2*I.p,by omega⟩
  have next (n : ℕ) (k : Guard I.p) (small : n ≤ 2*I.p) (hp : slotText I a n <+: T.text) :
      ∃ x rest q, T.text = slotText I a n ++ x :: rest ∧
        tokenStep I (some (slots I (rs k) a n)) x = some q := by
    obtain ⟨rest,hr⟩ := hp
    obtain ⟨q,hq,after⟩ := (run_split I).mp (hr.symm ▸ accept k)
    rw [slot_success I (frame k) a index small] at hq
    cases hq
    cases rest with
    | nil =>
      exact (cannot_finish I k (slots I (rs k) a n) (frame k).2.1 (Option.some.inj after)).elim
    | cons x rest =>
      obtain ⟨s,hs,_⟩ := Option.bind_eq_some_iff.mp after
      exact ⟨x,rest,s,hr.symm,hs⟩
  have pref (n : ℕ) (h : n ≤ 2*I.p) : slotText I a n <+: T.text := by
    induction n with
    | zero => exact T.nonempty_marker I (frame last) hn (accept last)
    | succ n ih =>
      let j : Guard I.p := ⟨n,by omega⟩
      obtain ⟨x,v,q,eq,hs⟩ := next n j (by omega) (ih (by omega))
      have expect : (rs j).expected = a.bits n := by
        rw [(frame j).2.2.2.2.2.1 (by dsimp [j]; omega),←index,
          Addr.index_bit a m _ (by dsimp [j]; omega)]
      obtain rfl := at_bit_forced I _ a (by omega : n<2*I.p) (frame j).1 expect hs
      exact ⟨v,by simpa [slotText,List.range_succ,List.append_assoc] using eq.symm⟩
  obtain ⟨x,v,q,eq,hs⟩ := next (2*I.p) last le_rfl (pref _ le_rfl)
  obtain ⟨d,rfl⟩ := at_tile_forced I _ _ hs
  exact ⟨d,v,by simpa [encoded_record,List.append_assoc] using eq.symm⟩

private theorem end_region {m i prev} (hi : i ≤ total I.p) (rs : Guard I.p → Registers D)
    (frame : ∀ j, Frame I (rs j) j m i prev) :
    (∀ j, run I (some (rs j)) (Tape.empty (D := D) m).text = some (finishes I j m)) ↔
      i = total I.p := by
  have test (j : Guard I.p) :
      run I (some (rs j)) (Tape.empty (D := D) m).text =
        if i ≠ 0 ∧ (j.val ≠ 2*I.p ∨ i = total I.p)
          then some (finishes I j m) else none := by
    obtain ⟨copy,master,zero,seen,last,_⟩ := frame j
    by_cases hz : i=0
    · cases m <;> simp [Tape.empty,Tape.text,probeText,run,tokenStep,zero,master,seen,hz]
    · have e : (rs j).colLast = true ∧ (rs j).rowLast = true ↔ i = total I.p := by
        simpa only [Bool.and_eq_true,decide_eq_true_eq]
          using (congrArg (· = true) (last hz)).to_iff
      cases m <;> simp [Tape.empty,Tape.text,probeText,run,
        tokenStep,zero,master,copy,seen,hz,e,finishes,afterMaster]
      split_ifs <;> simp
  constructor
  · intro h
    let j : Guard I.p := ⟨2*I.p,by omega⟩
    have eq := h j
    rw [test] at eq
    split at eq <;> simp_all [j]
  · rintro rfl j
    rw [test,ite_eq_left ⟨(Nat.two_pow_pos _).ne',Or.inr rfl⟩]

/-- A visit records the address, tile and possible probe payload of one cell in a traversal. -/
structure Visit (p : ℕ) (D : Type*) where
  /-- The grid cell being visited. -/
  addr : Addr p
  /-- The tile exposed at this address. -/
  tile : D
  /-- The data after the exposed record in a probe. -/
  payload : List (CellLetter D)

/-- Render a list of visits as master data or as the corresponding list of probes. -/
def tapeOf (m : Bool) : List (Visit I.p D) → Tape D m
  | [] => Tape.empty m
  | v :: vs => Tape.put I v.addr v.tile v.payload (tapeOf m vs)

/-- Each visit checks its tile against the previous one when required, as well as the applicable
master boundary conditions. -/
def localChecks (m : Bool) : Option D → List (Visit I.p D) → Prop
  | _, [] => True
  | prev, v::vs => CellOK I m prev v.addr v.tile ∧ localChecks m (some v.tile) vs

private theorem consume_iff {m i prev} (rs : Guard I.p → Registers D)
    (frames : ∀ j, Frame I (rs j) j m i prev) (a : Addr I.p) (index : Addr.index m a=i)
    (d : D) (payload : List (CellLetter D)) (tail : Tape D m) :
    (∀ j, run I (some (rs j)) (Tape.put I a d payload tail).text = some (finishes I j m)) ↔
      CellOK I m prev a d ∧
      ∀ j, run I (some (nextState I (rs j) a d)) tail.text = some (finishes I j m) := by
  classical
  simp only [Tape.put_text,run_append,read_cell I (frames _) a index]
  constructor
  · intro h
    have check (j : Guard I.p) :
        (m=true → Boundary I a d) ∧ (j.val=2*I.p → Neighbor I m prev a d) := by
      by_contra bad
      have impossible := h j
      rw [ite_eq_right bad] at impossible
      cases impossible
    let last : Guard I.p := ⟨2*I.p, by omega⟩
    exact ⟨⟨(check last).1,(check last).2 rfl⟩,
        fun j => by simpa only [ite_eq_left (check j),Option.bind_some] using h j⟩
  · rintro ⟨ok,h⟩ j
    rw [ite_eq_left ⟨ok.1,fun _ => ok.2⟩]
    exact h j

/-- All checkers finish a traversal exactly when its visits follow the required address order
and satisfy the local cell tests. -/
theorem read_traversal (m : Bool) (T : Tape D m) :
    (∀ j : Guard I.p, run I (beginPhase D j m) T.text = some (finishes I j m)) ↔
      ∃ vs, vs.map Visit.addr = order I.side m ∧
        T = tapeOf I m vs ∧ localChecks I m none vs := by
  classical
  have go (xs : List (Addr I.p)) (i : ℕ) (len : i+xs.length=total I.p)
      (number : ∀ j (hj : j < xs.length), Addr.index m xs[j] = i+j)
      (prev : Option D) (rs : Guard I.p → Registers D)
      (frames : ∀ k, Frame I (rs k) k m i prev) (T : Tape D m) :
      (∀ j, run I (some (rs j)) T.text = some (finishes I j m)) ↔
        ∃ vs, vs.map Visit.addr = xs ∧ T = tapeOf I m vs ∧ localChecks I m prev vs := by
    induction xs generalizing i prev rs T with
    | nil =>
      have eq : i=total I.p := by simpa using len
      constructor
      · intro accepts
        have empty : T = Tape.empty m := by
          by_contra nonempty
          let j : Guard I.p := ⟨2*I.p,by omega⟩
          obtain ⟨v,hv⟩ := T.nonempty_marker I (frames j) nonempty (accepts j)
          have hrun := accepts j
          rw [← hv, List.singleton_append] at hrun
          obtain ⟨q,hs,_⟩ := Option.bind_eq_some_iff.mp hrun
          have f := frames j
          have pos : i ≠ 0 := eq ▸ (Nat.two_pow_pos _).ne'
          have full := f.2.2.2.2.1 pos
          rw [slot_record I _ f.2.2.1
            ((⟨0,Nat.two_pow_pos _⟩,⟨0,Nat.two_pow_pos _⟩) : Addr I.p)] at hs
          simp [canStart,f.1,f.2.2.2.1,j,full,eq] at hs
        exact ⟨[],rfl,empty,trivial⟩
      · rintro ⟨vs,he,tape,_⟩
        obtain rfl : vs = [] := List.map_eq_nil_iff.mp he
        rw [tape]; exact (end_region I (by omega) rs frames).mpr eq
    | cons a xs ih =>
      have ix : Addr.index m a=i := by
        have he := number 0 (by simp)
        change Addr.index m a = i+0 at he
        exact he
      have lt : i < total I.p := by simp at len; omega
      have hl : i+1+xs.length=total I.p := by simp at len; omega
      have hn (j) (hj : j < xs.length) : Addr.index m xs[j] = i+1+j := by
        have he := number (j+1) (by simp [hj])
        change Addr.index m xs[j] = i+(j+1) at he
        omega
      constructor
      · intro accepts
        have ne : T ≠ Tape.empty m := by
          rintro rfl; exact lt.ne ((end_region I lt.le rs frames).mp accepts)
        obtain ⟨d,pref⟩ := first_record I rs frames T ne a ix accepts
        obtain ⟨payload,tail,rfl⟩ := Tape.parse_front I T a d pref
        obtain ⟨ok,cont⟩ := (consume_iff I rs frames a ix d payload tail).mp accepts
        obtain ⟨vs,order,tape,checks⟩ := (ih (i+1) hl hn (some d) _
          (fun j => next_frame I (frames j) a ix d) tail).mp cont
        exact ⟨⟨a,d,payload⟩::vs,by simp [order],by rw [tape]; rfl,ok,checks⟩
      · rintro ⟨vs,order,tape,checks⟩
        cases vs with
        | nil => cases order
        | cons v vs =>
          obtain ⟨eq,tailOrder⟩ := List.cons.inj order
          subst a
          rw [tape]; apply (consume_iff I rs frames _ ix _ _ _).mpr
          exact ⟨checks.1,(ih (i+1) hl hn (some v.tile) _
            (fun j => next_frame I (frames j) _ ix _) _).mpr ⟨vs,tailOrder,rfl,checks.2⟩⟩
  have len := congrArg List.length (map_index_order I.p m)
  simp only [List.length_map,List.length_range] at len
  exact go (order I.side m) 0 (by simpa using len)
    (fun j hj => by simpa using index_order_get I.p m j hj)
    none (fun j => {copy := j,master := m}) (fun j => initial_frame I j m) T

end DeciNSSE.Complexity.Tiling.Controller
