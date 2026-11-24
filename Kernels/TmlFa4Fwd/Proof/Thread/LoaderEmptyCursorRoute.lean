-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorStep
import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader
  (loaderOutCore loaderRingWrites loaderPipelineStepRegs reuseEntry reuseArrival
    recurringStageInputs recurringEmptyWait recurringPacketSite copyCommitPc
    RingShape loaderPipelineStepShape)

noncomputable section

/-- Routes with no K/V-ring events between a cursor advance and its next packet entry. -/
inductive CursorRoute where
  | beforePriming | betweenPriming | beforeSeed | primingToSeed | drain
  | throughPriming (stage : Fin 2) | throughReuse
  | seedDispatch | warmV | warmK | steadyK
  | packet (site : Fin 4)
  | packetAfterPoll (site : Fin 4)

/-- A route's instructions before reaching a packet entry or the drain boundary. -/
def CursorRoute.inside : CursorRoute → Nat → Bool
  | .beforePriming, pc => decide (174 ≤ pc ∧ pc < 515)
  | .betweenPriming, pc => decide (520 ≤ pc ∧ pc < 780)
  | .beforeSeed, pc => decide (785 ≤ pc ∧ pc < 909)
  | .primingToSeed, pc => decide (174 ≤ pc ∧ pc < 909)
  | .drain, pc => decide (1744 ≤ pc ∧ pc < 1901)
  | .throughPriming stage, pc => decide ((if stage = 0 then 515 else 780) ≤ pc ∧ pc < 1744)
  | .throughReuse, pc => decide (909 ≤ pc ∧ pc < 1744)
  | .seedDispatch, pc => decide (911 ≤ pc ∧ pc < 914)
  | .warmV, pc => decide (1143 ≤ pc ∧ pc < 1203)
  | .warmK, pc => decide ((916 ≤ pc ∧ pc < 957) ∨ (1348 ≤ pc ∧ pc < 1427))
  | .steadyK, pc => decide ((1396 ≤ pc ∧ pc < 1427) ∨ (1741 ≤ pc ∧ pc < 1744))
  | .packet site, pc => decide (reuseEntry site ≤ pc ∧ pc < reuseArrival site)
  | .packetAfterPoll site, pc =>
    decide ((recurringEmptyWait site).pc + 3 ≤ pc ∧ pc < reuseArrival site)

/-- The packet entrances or drain boundary at the end of each route. -/
def CursorRoute.stops : CursorRoute → List Nat
  | .beforePriming => [515, 1862, 1901]
  | .betweenPriming => [780]
  | .beforeSeed => [909]
  | .primingToSeed => [909, 1862, 1901]
  | .drain => [1901]
  | .throughPriming _ | .throughReuse => [1744]
  | .seedDispatch => [914, 1353]
  | .warmV => [1203]
  | .warmK => [957, 1427, 1744]
  | .steadyK => [1427, 1744]
  | .packet site | .packetAfterPoll site => [reuseArrival site]

/-- The cursor and address-base registers retained along this route. -/
def CursorRoute.registers : CursorRoute → List Nat
  | .beforePriming | .betweenPriming | .beforeSeed | .primingToSeed | .drain
  | .throughPriming _ | .throughReuse => [1062, 2535]
  | .warmV => [1139, 2064, 2535]
  | .seedDispatch | .warmK | .steadyK => [7179, 7180, 2535]
  | .packet site | .packetAfterPoll site =>
    [(recurringStageInputs site).1, (recurringEmptyWait site).phase, 2535]

private def CursorRoute.accepts (r : CursorRoute) (pc : Nat) : Bool :=
  r.inside pc || r.stops.contains pc

private def routeCode (r : CursorRoute) (pc : Nat) (op : Op) : Bool :=
  !r.inside pc ||
  (r.accepts (pc + 1) && r.registers.all (fun reg => !(loaderRingWrites op).contains reg) &&
    match op with
    | .bra dest _ => r.accepts dest
    | .brx .. => false
    | _ => true)

private theorem routeBounds (r : CursorRoute) {pc : Nat} (h : r.inside pc = true) :
    174 ≤ pc ∧ pc < 1901 := by
  cases r <;> simp only [CursorRoute.inside, decide_eq_true_eq] at h
  case throughPriming stage =>
    have hLo : 174 ≤ (if stage = 0 then 515 else 780) := by split <;> decide
    exact ⟨hLo.trans h.1, h.2.trans (by decide)⟩
  case packet site =>
    fin_cases site <;> dsimp [reuseEntry, reuseArrival, recurringEmptyWait, recurringPacketSite,
      copyCommitPc] at h <;> omega
  case packetAfterPoll site =>
    fin_cases site <;> dsimp [recurringEmptyWait, reuseArrival, recurringPacketSite, copyCommitPc]
      at h <;> omega
  all_goals omega

private theorem routeCodeAt (r : CursorRoute) {pc : Nat} {ins : Instr}
    (hHere : r.inside pc = true) (hc : kernel.code[pc]? = some ins) :
    (r.accepts (pc + 1) && r.registers.all (fun reg => !(loaderRingWrites ins.op).contains reg) &&
      match ins.op with
      | .bra dest _ => r.accepts dest
      | .brx .. => false
      | _ => true) = true := by
  let entries := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have checked : entries.all (fun (ins, pc) => routeCode r pc ins.op) = true := by
    cases r
    case throughPriming stage => fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl)
    case packet site => fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
    case packetAfterPoll site => fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
    all_goals (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hLo, hHi⟩ := routeBounds r hHere
  have hSeen : (ins, pc) ∈ entries := by
    apply List.mem_of_getElem? (i := pc - 174)
    dsimp [entries]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc]
    rfl
  simpa only [routeCode, hHere, Bool.not_true, Bool.false_or] using
    List.all_eq_true.mp checked _ hSeen

private theorem CursorRoute.step {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (r : CursorRoute) (hHere : r.inside s.pc = true)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    (r.inside u.pc = true ∨ u.pc ∈ r.stops) ∧
      ∀ reg ∈ r.registers, u.regs reg = s.regs reg := by
  have hBounds := routeBounds r hHere
  have keep (reg : Nat) (hr : reg ∈ r.registers) : u.regs reg = s.regs reg := by
    apply loaderPipelineStepRegs hBounds.1 hBounds.2 _ hStep
    intro ins hc
    have hCert := routeCodeAt r hHere hc
    rw [Bool.and_eq_true] at hCert
    simpa using List.all_eq_true.mp (Bool.and_eq_true_iff.mp hCert.1).2 reg hr
  have finish (h : r.accepts u.pc = true) : r.inside u.pc = true ∨ u.pc ∈ r.stops := by
    simpa only [CursorRoute.accepts, Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq]
      using h
  refine ⟨finish ?_, keep⟩
  rcases hStep with ⟨_, hTau⟩ | ⟨e, _, hEvent⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at *
      rwa [← loaderOutCore hBounds.1 (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    have hCert := routeCodeAt r hHere hc
    rw [Bool.and_eq_true] at hCert
    have hFall := (Bool.and_eq_true_iff.mp hCert.1).1
    rcases tau_core_frame hc hCore with rfl | hFrame
    · exact hFall
    have hPc := hFrame.pc
    cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
    case bra target uniform =>
      rw [hPc]
      simpa only [hop] using hCert.2
    case brx => simp [hop] at hCert
    all_goals exact hPc.symm ▸ hFall
  · obtain ⟨tmpl, hOut, hFire⟩ := hEvent
    have hCore : EStep kernel [] l g s e (some u) :=
      ⟨tmpl, by rwa [← loaderOutCore hBounds.1 (by omega)], hFire⟩
    obtain ⟨ins, hc, _, _⟩ := estep_event_source hCore
    have hFall := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (routeCodeAt r hHere hc)).1).1
    rcases (estep_return_pc hCore (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · rw [h]
      simp [CursorRoute.accepts, hHere]
    · exact h.symm ▸ hFall

/-- A cut of an actual route keeps its original prefix walk and its exact visit suffix. -/
theorem CursorRoute.cutWalk {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (r : CursorRoute)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hIn : r.inside s.pc = true) (hShape : RingShape s) :
    (∀ v ∈ vs, r.inside v.pc = true) ∨
      ∃ u pre tail front post, es = pre ++ tail ∧ vs = front ++ post ∧
        (∀ v ∈ front, r.inside v.pc = true) ∧ u.pc ∈ r.stops ∧ RingShape u ∧
        (∀ reg ∈ r.registers, u.regs reg = s.regs reg) ∧
        Walk kernel Assumptions.all l g s pre front ∧
        Walk kernel Assumptions.all l g u tail post := by
  have step {t u : TState} {ev : Option Event} {tail : List Event} {post : List Visit}
      (hIn : r.inside t.pc = true) (hShape : RingShape t)
      (hStep : WStep kernel Assumptions.all l g t ev u)
      (hTail : Walk kernel Assumptions.all l g u tail post)
      (ih : r.inside u.pc = true → RingShape u →
        (∀ v ∈ post, r.inside v.pc = true) ∨
          ∃ v pre rest front next, tail = pre ++ rest ∧ post = front ++ next ∧
            (∀ visit ∈ front, r.inside visit.pc = true) ∧ v.pc ∈ r.stops ∧ RingShape v ∧
            (∀ reg ∈ r.registers, v.regs reg = u.regs reg) ∧
            Walk kernel Assumptions.all l g u pre front ∧
            Walk kernel Assumptions.all l g v rest next) :
      (∀ v ∈ visit kernel l g t ev :: post, r.inside v.pc = true) ∨
        ∃ v pre rest front next, ev.toList ++ tail = pre ++ rest ∧
          visit kernel l g t ev :: post = front ++ next ∧
          (∀ visit ∈ front, r.inside visit.pc = true) ∧ v.pc ∈ r.stops ∧ RingShape v ∧
          (∀ reg ∈ r.registers, v.regs reg = t.regs reg) ∧
          Walk kernel Assumptions.all l g t pre front ∧
          Walk kernel Assumptions.all l g v rest next := by
    have hPrepend {pre : List Event} {visits : List Visit}
        (hw : Walk kernel Assumptions.all l g u pre visits) :
        Walk kernel Assumptions.all l g t (ev.toList ++ pre)
          (visit kernel l g t ev :: visits) := by
      rcases hStep with ⟨rfl, ht⟩ | ⟨event, rfl, he⟩
      · exact .tau ht hw
      · exact .ev he hw
    obtain ⟨hNext, hRegs⟩ := r.step hIn hStep
    have hr := routeBounds r hIn
    have hu := loaderPipelineStepShape hr.1 hr.2 hShape hStep
    rcases hNext with hNext | hStop
    · rcases ih hNext hu with hAll |
        ⟨v, pre, rest, front, next, rfl, rfl, hPre, hv, hV, hOld, hw, hw'⟩
      · refine .inl (fun v hv => ?_)
        rcases List.mem_cons.mp hv with rfl | hMem
        · simpa only [visit_pc] using hIn
        · exact hAll _ hMem
      · refine .inr ⟨v, ev.toList ++ pre, rest, visit kernel l g t ev :: front, next,
          by simp [List.append_assoc], rfl, ?_,
          hv, hV, (fun reg hr => (hOld reg hr).trans (hRegs reg hr)), hPrepend hw, hw'⟩
        intro v hMem
        rcases List.mem_cons.mp hMem with rfl | hMem
        · simpa only [visit_pc] using hIn
        · exact hPre _ hMem
    · exact .inr ⟨u, ev.toList, tail, [visit kernel l g t ev], post, rfl, rfl,
        by simp [visit_pc, hIn], hStop, hu, hRegs, by simpa using hPrepend (.stop u), hTail⟩
  induction hw with
  | stop => exact .inl (by simp)
  | tau h ht ih => exact step hIn hShape (.inl ⟨rfl, h⟩) ht ih
  | ev h ht ih => exact step hIn hShape (.inr ⟨_, rfl, h⟩) ht ih
  | last h => exact .inl (by simp [visit_pc, hIn])

/-- Between packets an actual route either stays within the certified interval or
reaches a permitted endpoint with the cursor registers preserved. -/
theorem CursorRoute.cut {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (r : CursorRoute)
    (hw : Walk kernel Assumptions.all l g s es vs) (hIn : r.inside s.pc = true) :
    (∀ e ∈ es, r.inside e.pc = true) ∨
      ∃ u pre tail post, es = pre ++ tail ∧ (∀ e ∈ pre, r.inside e.pc = true) ∧
        u.pc ∈ r.stops ∧
        (∀ reg ∈ r.registers, u.regs reg = s.regs reg) ∧
        Walk kernel Assumptions.all l g u tail post := by
  have step {t u : TState} {ev : Option Event} {tail : List Event} {post : List Visit}
      (hIn : r.inside t.pc = true) (hStep : WStep kernel Assumptions.all l g t ev u)
      (hEvent : ∀ e ∈ ev.toList, r.inside e.pc = true)
      (hTail : Walk kernel Assumptions.all l g u tail post)
      (ih : r.inside u.pc = true →
        (∀ e ∈ tail, r.inside e.pc = true) ∨
          ∃ v pre rest next, tail = pre ++ rest ∧ (∀ e ∈ pre, r.inside e.pc = true) ∧
            v.pc ∈ r.stops ∧ (∀ reg ∈ r.registers, v.regs reg = u.regs reg) ∧
            Walk kernel Assumptions.all l g v rest next) :
      (∀ e ∈ ev.toList ++ tail, r.inside e.pc = true) ∨
        ∃ v pre rest next, ev.toList ++ tail = pre ++ rest ∧
          (∀ e ∈ pre, r.inside e.pc = true) ∧ v.pc ∈ r.stops ∧
          (∀ reg ∈ r.registers, v.regs reg = t.regs reg) ∧
          Walk kernel Assumptions.all l g v rest next := by
    obtain ⟨hNext, hRegs⟩ := r.step hIn hStep
    rcases hNext with hNext | hStop
    · rcases ih hNext with hAll | ⟨v, pre, rest, next, rfl, hPre, hv, hOld, hw⟩
      · exact .inl (fun e h => (List.mem_append.mp h).elim (hEvent e) (hAll e))
      · refine .inr ⟨v, ev.toList ++ pre, rest, next, by simp [List.append_assoc], ?_,
          hv, (fun reg hr => (hOld reg hr).trans (hRegs reg hr)), hw⟩
        intro e h
        exact (List.mem_append.mp h).elim (hEvent e) (hPre e)
    · exact .inr ⟨u, ev.toList, tail, post, rfl, hEvent, hStop, hRegs, hTail⟩
  induction hw with
  | stop => exact .inl (by simp)
  | tau h ht ih => exact step hIn (.inl ⟨rfl, h⟩) (by simp) ht ih
  | ev h ht ih =>
    refine step hIn (.inr ⟨_, rfl, h⟩) ?_ ht ih
    intro e he
    obtain rfl : e = _ := by simpa using he
    rwa [estep_source_pc h]
  | last h =>
    refine .inl (fun e he => ?_)
    obtain rfl : e = _ := by simpa using he
    rwa [estep_source_pc h]

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
