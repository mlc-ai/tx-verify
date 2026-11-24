-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Mma Softmax

noncomputable section

private theorem correctionLdAccumulator {l : Launch} {g ta : Nat} {s u : TState}
    {ds : List Nat} {sh : TcShape} {e : Event}
    (he : Fires s.pc (eventTmpl Assumptions.all l g s (.tcLd ds ta sh none)) e (some u)) :
    u.acc = s.acc := by
  let P := fun v : TState => v.acc = s.acc
  have hFrame : CallbackFrame P (tcTmpl l g s (.tcLd ds ta sh none)) := by
    cases sh <;> simp only [tcTmpl, ldResult] <;> apply ofExec_frame
    all_goals repeat' first | trivial | (apply allOk_bind; intro v) | split
    all_goals intro vals; exact (setRegs_skel (next s) _ _).2.2.1
  by_cases hWait : Assumptions.all.any (·.tcLdWait s.pc) = true
  · by_cases hSub : s.sub = 0
    · have hDelayed : CallbackFrame P ((tcTmpl l g s (.tcLd ds ta sh none)).thenWaitLd s.pc) := by
        have lift {m : Exec Tmpl}
            (hm : AllOk (fun t => CallbackFrame P (t.thenWaitLd s.pc)) m) :
            CallbackFrame P ((ofExec m).thenWaitLd s.pc) := by
          cases m <;> exact hm
        cases sh <;> simp only [tcTmpl, ldResult] <;> apply lift
        all_goals repeat' first | trivial | (apply allOk_bind; intro v) | split
        all_goals intro vals; exact (setRegs_skel (next s) _ _).2.2.1
      exact callbackFrame_fires hDelayed (by
        simpa only [eventTmpl, tcLdTmpl, hWait, hSub, ite_true] using he)
    · obtain ⟨_, rfl⟩ := fires_tcLd_wait hWait hSub he
      rfl
  · have hOff : Assumptions.all.any (·.tcLdWait s.pc) = false := by simpa using hWait
    exact callbackFrame_fires hFrame (by
      simpa only [eventTmpl, tcLdTmpl, hOff, Bool.false_eq_true, ite_false] using he)

private theorem correctionStAccumulator {l : Launch} {g ta : Nat} {s u : TState}
    {ss : List Opnd} {sh : TcShape} {e : Event}
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.tcSt ta ss sh)) e (some u)) :
    u.acc = s.acc := by
  have frame (v : TState) : CallbackFrame (· = next v) (tcTmpl l g v (.tcSt ta ss sh)) := by
    cases sh <;> simp only [tcTmpl] <;> apply ofExec_frame
    all_goals repeat' first | rfl | trivial | (apply allOk_bind; intro v) | split
  simp only [eventTmpl, tcStTmpl] at hf
  split at hf
  · split at hf
    · split at hf
      · obtain rfl := Option.some.inj hf.2
        rfl
      · cases hf.2
    · obtain rfl := callbackFrame_fires (frame _) hf
      rfl
  · obtain rfl := callbackFrame_fires (frame _) hf
    rfl


/-- The decoded weak memory store only changes the element sub-step. -/
theorem correctionStoreState {l : Launch} {g : Nat} {s u : TState}
    {a : MemAccess} {e : Event} (hop : scoreStoreOp a = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.mem a)) e (some u)) :
    u = afterStore s a.srcs := by
  simp only [scoreStoreOp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hop
  obtain ⟨⟨⟨⟨⟨hKind, hSem⟩, _⟩, hRule⟩, hSpace⟩, hAddr⟩ := hop
  cases hLoc : a.locSpace? with
  | none => simp [hLoc] at hSpace
  | some sp =>
    cases hBase : a.addr.base <;> simp [hBase] at hAddr
    simp only [eventTmpl, memTmpl_direct_weakStore hRule hLoc hBase hKind hSem, storeTmpl] at hf
    repeat' split at hf
    all_goals simp only [Fires, reduceCtorEq, and_false] at hf
    exact Option.some.inj hf.2

private theorem correctionMemAccumulator {l : Launch} {g : Nat} {s u : TState}
    {a : MemAccess} {e : Event} (hOp : scoreEventOp (.mem a) = true)
    (hScalar : a.kind = .load → a.regs.length ≤ 1) (hAcc : s.acc = [])
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.mem a)) e (some u)) :
    u.acc = [] := by
  simp only [scoreEventOp, Bool.or_eq_true] at hOp
  rcases hOp with h | h
  · have hs : a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs.length ≤ 4 := by
      simpa [and_assoc] using h
    obtain ⟨_, bs, _, rfl⟩ := fires_load hs.1 hs.2.1 hf hs.2.2.1
    cases hb : rebuild 3 bs with
    | error f => simpa only [afterLoad, hb] using hAcc
    | ok v =>
      rw [afterLoad_last hb (by have := hScalar hs.1; omega)]
  · rw [correctionStoreState h hf]
    unfold afterStore
    split <;> exact hAcc

/-- Only multi-element loads can append to the partial scalar load accumulator.
Correction loads one scalar at a time, so its memory and TMEM events keep it empty. -/
theorem correctionEventAccumulator {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
    (hOp : correctionReturningOp ins.op = true)
    (hScalar : match ins.op with | .mem a => a.kind = .load → a.regs.length ≤ 1 | _ => True)
    (hS : s.acc = []) (he : EStep kernel Assumptions.all l g s e (some u)) : u.acc = [] := by
  obtain ⟨j, hj, _, hf⟩ := estep_event_source he
  rw [hc] at hj
  obtain rfl := Option.some.inj hj
  have hAdv {op : Op} (h : AdvancesOp op)
      (hf : Fires s.pc (eventTmpl Assumptions.all l g s op) e (some u)) : u.acc = [] := by
    obtain rfl := fires_next h hf
    exact hS
  cases hop : ins.op <;> simp only [hop, correctionReturningOp, scoreEventOp,
    Bool.or_false, Bool.or_true, Bool.false_eq_true] at hOp
  case tcLd ds ta sh red =>
    have hR := Option.isNone_iff_eq_none.mp hOp
    subst red
    rw [hop] at hf
    exact (correctionLdAccumulator hf).trans hS
  case tcSt ta ss sh =>
    rw [hop] at hf
    exact (correctionStAccumulator hf).trans hS
  case mem a =>
    rw [hop] at hf hScalar
    exact correctionMemAccumulator hOp hScalar hS hf
  case tcWaitLd =>
    rw [hop, eventTmpl, tcTmpl] at hf
    split at hf
    · obtain rfl := Option.some.inj hf.2
      exact hS
    · cases hf.2
  case tcWaitSt =>
    rw [hop] at hf
    have h : CallbackFrame (· = next s) (eventTmpl Assumptions.all l g s .tcWaitSt) := by
      simp only [eventTmpl, tcTmpl]
      apply ofExec_frame
      repeat' first | rfl | trivial | split
    obtain rfl := callbackFrame_fires h hf
    exact hS
  case mbarArrive base off tx count cl rel sc d =>
    rw [hop] at hf
    obtain ⟨rfl, _⟩ := fires_arrive_state hf
    cases d <;> exact hS
  case mbarWait d base off phase acq sc =>
    rw [hop] at hf
    obtain ⟨_, _, _, _, _, rfl⟩ := fires_wait hf
    exact hS
  case warp w =>
    rw [hop] at hf
    simp only [Bool.or_eq_true] at hOp
    rcases hOp with h | h
    · exact (linearWarpAccumulator h hf).trans hS
    · apply hAdv _ hf
      cases w with
      | mk k ty dsts srcs mask =>
        cases k <;> first | exact True.intro | cases h
  case barArrive id n aligned =>
    rw [hop] at hf
    have h : CallbackFrame (· = next s) (eventTmpl Assumptions.all l g s
        (.barArrive id n aligned)) := by
      simp only [eventTmpl, barTmpl]
      repeat' split
      all_goals first | rfl | trivial
    obtain rfl := callbackFrame_fires h hf
    exact hS
  case barSync id aligned =>
    rw [hop] at hf
    have h : CallbackFrame (· = next s) (eventTmpl Assumptions.all l g s
        (.barSync id aligned)) := by
      simp only [eventTmpl, barTmpl]
      repeat' split
      all_goals first | rfl | trivial
    obtain rfl := callbackFrame_fires h hf
    exact hS
  case barSyncN id n aligned =>
    rw [hop] at hf
    have h : CallbackFrame (· = next s) (eventTmpl Assumptions.all l g s
        (.barSyncN id n aligned)) := by
      simp only [eventTmpl, barTmpl]
      repeat' split
      all_goals first | rfl | trivial
    obtain rfl := callbackFrame_fires h hf
    exact hS
  case fence f => exact hAdv (op := .fence f) trivial (hop ▸ hf)
  case setMaxReg inc n =>
    exact hAdv (op := .setMaxReg inc n) trivial (hop ▸ hf)

end
end PTX.Kernels.TmlFa4Fwd.Correction
