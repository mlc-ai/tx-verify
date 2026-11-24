-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
public import Kernels.TmlFa4Fwd.Proof.MmaReadyCursor
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- The four decoded ready observations consume the logical K/V ring. -/
def readyHead : Fin 4 → Nat
  | 0 => 2145
  | 1 => 2294
  | 2 => 2352
  | 3 => 2545

/-- Project a successful K/V-ready observation, leaving the other pipeline waits out. -/
def readyEvent (e : Event) : Option (Loc × Nat) :=
  match e.kind with
  | .wait loc parity true _ _ =>
    if (List.finRange 4).any (fun i => readyHead i == e.pc) then some (loc, parity) else none
  | _ => none

/-- The ranges between polling and cursor updates use an unchanged live register frame. -/
structure ReadyInterval where
  lo : Nat
  hi : Nat
  exits : List Nat
  keep : List Nat

def readyInterval : Fin 9 → ReadyInterval
  | 0 => ⟨1908, 2140, [2140, 2763], [2535, 1178]⟩
  | 1 => ⟨2141, 2144, [2144], [2535, 2536]⟩
  | 2 => ⟨2148, 2280, [2280], [2535]⟩
  | 3 => ⟨2284, 2287, [2287, 2534], [2535, 7207, 7208]⟩
  | 4 => ⟨2297, 2344, [2344], [2535, 7207, 7208]⟩
  | 5 => ⟨2355, 2524, [2524], [2535, 1192, 2572]⟩
  | 6 => ⟨2529, 2534, [2291, 2534], [2535, 7207, 7208]⟩
  | 7 => ⟨2534, 2542, [2542], [2535, 7207, 7208]⟩
  | 8 => ⟨2548, 2768, [3099], []⟩

def ReadyInterval.inside (interval : ReadyInterval) (pc : Nat) : Prop :=
  interval.lo ≤ pc ∧ pc < interval.hi

instance (interval : ReadyInterval) (pc : Nat) : Decidable (interval.inside pc) :=
  inferInstanceAs (Decidable (interval.lo ≤ pc ∧ pc < interval.hi))

def ReadyInterval.next (interval : ReadyInterval) (pc : Nat) : Bool :=
  decide (interval.inside pc) || interval.exits.contains pc

def ReadyInterval.code (interval : ReadyInterval) (pc : Nat) (ins : Instr) : Bool :=
  interval.keep.all (fun r => !(mmaWrites ins.op).contains r) &&
    (ins.op.isLocal || linearEventOp ins.op) &&
    (match ins.op with
      | .bra target _ => interval.next target
      | .brx .. => false
      | _ => true) &&
    (interval.next (pc + 1) || (ins.guard.isNone && match ins.op with
      | .bra .. => true
      | _ => false))

private theorem decodedInterval (i : Fin 9) {pc : Nat} {ins : Instr}
    (hPc : (readyInterval i).inside pc) (hc : kernel.code[pc]? = some ins) :
    (readyInterval i).code pc ins = true := by
  let interval := readyInterval i
  let code := ((kernel.code.drop interval.lo).take (interval.hi - interval.lo)).zipIdx interval.lo
  have hCode : code.all (fun pair => interval.code pair.2 pair.1) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  apply List.all_eq_true.mp hCode (ins, pc)
  apply List.mem_of_getElem? (i := pc - interval.lo)
  dsimp only [code]
  have hLo : interval.lo ≤ pc := hPc.1
  have hHi : pc < interval.hi := hPc.2
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega),
    List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
  rfl

private theorem intervalBounds (i : Fin 9) :
    1907 ≤ (readyInterval i).lo ∧ (readyInterval i).hi ≤ 2768 := by
  fin_cases i <;> decide

theorem readyIntervalNoHead (i : Fin 9) {pc : Nat}
    (hPc : (readyInterval i).inside pc) : (List.finRange 4).any (fun j => readyHead j == pc) =
      false := by
  have h : ∀ j : Fin 4, ¬ (readyInterval i).inside (readyHead j) := by
    fin_cases i <;> intro j <;> fin_cases j <;> decide
  apply Bool.eq_false_iff.mpr
  intro hb
  obtain ⟨j, _, hj⟩ := List.any_eq_true.mp hb
  exact h j ((beq_iff_eq.mp hj).symm ▸ hPc)

/-- The checked interval contains no successful ready observation station. -/
theorem readyEventOutside (i : Fin 9) {e : Event}
    (hPc : (readyInterval i).lo ≤ e.pc ∧ e.pc < (readyInterval i).hi) : readyEvent e = none := by
  simp [readyEvent, readyIntervalNoHead i hPc]
  split <;> rfl

private theorem intervalStep (interval : ReadyInterval)
    (hBounds : 1907 ≤ interval.lo ∧ interval.hi ≤ 2768)
    (hDecoded : ∀ {pc ins}, interval.inside pc → kernel.code[pc]? = some ins →
      interval.code pc ins = true) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} {F : List (Nat × Value)} (hPc : interval.inside s.pc)
    (hs : RoleShape s ∧ s.regs 1062 = some (b32 12)) (hF : Holds s.regs F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ interval.keep)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    (interval.inside u.pc ∨ u.pc ∈ interval.exits ∧ u.fault = none) ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F := by
  have hLo := hBounds.1.trans hPc.1
  have hHi := hPc.2.trans_le hBounds.2
  have hShape := (mmaCutStep hLo hHi hStep hs).2
  have hRegs := Epilogue.holdsSchedulerFrame hF (fun r hr => by
    rcases hKeep r hr with rfl | hr
    · exact hShape.2.trans hs.2.symm
    apply mmaStepReg (by omega) hHi _ hStep
    intro ins hc
    have h := hDecoded hPc hc
    simp only [ReadyInterval.code, Bool.and_eq_true] at h
    simpa using List.all_eq_true.mp h.1.1.1 r hr)
    (fun _ h => List.mem_map_of_mem h)
  have hNext : interval.inside u.pc ∨ u.pc ∈ interval.exits ∧ u.fault = none := by
    have toExit {pc : Nat} (h : interval.next pc = true) (hf : u.fault = none)
        (hu : u.pc = pc) :
        interval.inside u.pc ∨ u.pc ∈ interval.exits ∧ u.fault = none := by
      rw [hu]
      simp only [ReadyInterval.next, Bool.or_eq_true, decide_eq_true_eq, List.contains_eq_mem,
        hf, and_true] at h ⊢
      exact h
    rcases hStep with ⟨_, ht⟩ | ⟨ev, _, he⟩
    · have ht' : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← out_eq_core (by omega) hHi]
      obtain ⟨ins, hc, hf, hSrc⟩ := Softmax.tauScoreSource ht
      have hCode := hDecoded hPc hc
      simp only [ReadyInterval.code, Bool.and_eq_true] at hCode
      rcases hSrc with ⟨rfl, hg⟩ | ⟨_, hl, hx⟩
      · apply toExit (pc := s.pc + 1) _ hf rfl
        have hNext := hCode.2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hNext
        rcases hNext with h | h
        · exact h
        · have hGuard := Option.isNone_iff_eq_none.mp h.1
          simp [hGuard, guardHolds, pure, Except.pure] at hg
      · have hRun : LocalFrame ins.op s u := by
          rcases Softmax.scoreExecLocal hx with h | ⟨_, hSites, _, _⟩
          · exact h
          · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSites
            omega
        have hF := hRun.fault.trans hf
        have hNoBrx : ¬ BrxTarget ins.op u.pc := by
          cases ho : ins.op <;> simp [ho, BrxTarget] at hCode ⊢
        apply toExit (pc := nextPc ins.op s.pc) _ hF (hRun.pc.resolve_right hNoBrx)
        cases ho : ins.op <;> simp only [nextPc]
        case bra target uni =>
          simpa only [ho] using hCode.1.2
        case brx => simp [ho] at hCode
        all_goals
          simpa only [ho, Bool.and_false, Bool.or_false] using hCode.2
    · obtain ⟨ins, hc, hl, _⟩ := estep_event_source he
      have hCode := hDecoded hPc hc
      simp only [ReadyInterval.code, Bool.and_eq_true] at hCode
      have hFall : interval.next (s.pc + 1) = true := by
        cases ho : ins.op <;> simp only [ho, Op.isLocal] at hl hCode
        case bra => cases hl
        case brx => cases hl
        all_goals simpa using hCode.2
      have hNonFault : s.fault = none := by
        cases h : s.fault
        · rfl
        · obtain ⟨tmpl, hOut, hFire⟩ := he
          simp only [out, h, Out.ev.injEq] at hOut
          subst tmpl
          cases hFire.2
      have hEvent : linearEventOp ins.op = true := by simpa [hl] using hCode.1.1.2
      rcases (linearEventProgressWithSub hc hEvent hs.1.1 hs.1.2.1 he).2.2 with h | h | h
      · exact toExit hFall (h.2.1.trans hNonFault) h.1
      · exact .inl (h.1.symm ▸ hPc)
      · exact .inl (h.1.symm ▸ hPc)
  exact ⟨hNext, hShape, hRegs⟩

/-- An actual interval either stops before its next boundary, or leaves through one of the
decoded exits with the cursor registers intact. The cut erases events outside the projection. -/
theorem certifiedIntervalCut {α : Type} (mark : Event → Option α) (interval : ReadyInterval)
    (hBounds : 1907 ≤ interval.lo ∧ interval.hi ≤ 2768)
    (hDecoded : ∀ {pc ins}, interval.inside pc → kernel.code[pc]? = some ins →
      interval.code pc ins = true)
    (hErase : ∀ e : Event,
      interval.lo ≤ e.pc ∧ e.pc < interval.hi → mark e = none)
    {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {F : List (Nat × Value)}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : interval.lo ≤ s.pc ∧ s.pc < interval.hi)
    (hs : RoleShape s ∧ s.regs 1062 = some (b32 12)) (hF : Holds s.regs F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ interval.keep) :
    es.filterMap mark = [] ∨
      ∃ u pre tail post, es = pre ++ tail ∧ pre.filterMap mark = [] ∧
        post.length < vs.length ∧ u.pc ∈ interval.exits ∧ u.fault = none ∧
        (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F ∧
        Walk kernel Assumptions.all l g u tail post := by
  induction hw with
  | stop => exact .inl rfl
  | tau ht hw ih =>
    obtain ⟨hInner | ⟨hExit, hf⟩, hu, hRegs⟩ :=
      intervalStep interval hBounds hDecoded hPc hs hF hKeep (.inl ⟨rfl, ht⟩)
    · rcases ih hInner hu hRegs with h | ⟨v, pre, tail, post, hE, hP, hL, hX, hF, hS, hH, hW⟩
      · exact .inl h
      · exact .inr ⟨v, pre, tail, post, hE, hP, by simp; omega, hX, hF, hS, hH, hW⟩
    · exact .inr ⟨_, [], _, _, rfl, rfl, by simp, hExit, hf, hu, hRegs, hw⟩
  | @ev t u ev events visits he hw ih =>
    have hNo : mark ev = none := hErase ev ((estep_source_pc he).symm ▸ hPc)
    obtain ⟨hInner | ⟨hExit, hf⟩, hu, hRegs⟩ :=
      intervalStep interval hBounds hDecoded hPc hs hF hKeep (.inr ⟨_, rfl, he⟩)
    · rcases ih hInner hu hRegs with h | ⟨v, pre, tail, post, hE, hP, hL, hX, hF, hS, hH, hW⟩
      · exact .inl (by simp [hNo, h])
      · exact .inr ⟨v, ev :: pre, tail, post, congrArg (ev :: ·) hE,
          by simp only [List.filterMap_cons, hNo, hP],
          by simp; omega, hX, hF, hS, hH, hW⟩
    · exact .inr ⟨_, [ev], _, _, rfl, by simp [hNo], by simp, hExit, hf, hu, hRegs, hw⟩
  | last he =>
    exact .inl (by simp [hErase _ ((estep_source_pc he).symm ▸ hPc)])

/-- An actual interval either stops before its next boundary, or leaves through one of the
decoded exits with the cursor registers intact. The cut erases events outside the projection. -/
theorem readyIntervalCutWith {α : Type} (mark : Event → Option α) (i : Fin 9)
    (hErase : ∀ e : Event,
      (readyInterval i).lo ≤ e.pc ∧ e.pc < (readyInterval i).hi → mark e = none)
    {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {F : List (Nat × Value)}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : (readyInterval i).lo ≤ s.pc ∧ s.pc < (readyInterval i).hi)
    (hs : RoleShape s ∧ s.regs 1062 = some (b32 12)) (hF : Holds s.regs F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ (readyInterval i).keep) :
    es.filterMap mark = [] ∨
      ∃ u pre tail post, es = pre ++ tail ∧ pre.filterMap mark = [] ∧
        post.length < vs.length ∧ u.pc ∈ (readyInterval i).exits ∧ u.fault = none ∧
        (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F ∧
        Walk kernel Assumptions.all l g u tail post :=
  certifiedIntervalCut mark (readyInterval i) (intervalBounds i) (decodedInterval i) hErase
    hw hPc hs hF hKeep

end
end PTX.Kernels.TmlFa4Fwd.Mma
