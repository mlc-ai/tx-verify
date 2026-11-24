-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarriers
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Proof.NamedBarrierSites
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue

private def participantEntry (role : Fin 3) : Nat := ![3103, 7747, 1912] role

private def participantFinal (role : Fin 3) : Nat := ![7741, 9204, 2764] role

/-- The arrival that ends a participating lane's use of the shared Tensor Memory allocation. -/
@[no_expose] def FinalAllocationArrival (X : Execution) (i : EvId) (mode : BarMode) : Prop :=
  ∃ role : Fin 3, X.get i = some ⟨participantFinal role, .bar 2 (some 416) mode⟩

theorem FinalAllocationArrival.arrival {X : Execution} {i : EvId} {mode : BarMode}
    (h : FinalAllocationArrival X i mode) : BarrierArrival X i 2 (some 416) mode := by
  obtain ⟨_, he⟩ := h
  exact ⟨_, he, rfl⟩

theorem FinalAllocationArrival.decoded {X : Execution} {i : EvId} {mode : BarMode}
    (h : FinalAllocationArrival X i mode) :
    ∃ site ∈ [2764, 7741, 9204], X.get i = some ⟨site, .bar 2 (some 416) mode⟩ := by
  obtain ⟨role, he⟩ := h
  exact ⟨_, (by decide : ∀ i : Fin 3, participantFinal i ∈ [2764, 7741, 9204]) role, he⟩

theorem FinalAllocationArrival.of_decoded {X : Execution} {i : EvId} {mode : BarMode}
    {site : Nat} (hs : site ∈ [2764, 7741, 9204])
    (he : X.get i = some ⟨site, .bar 2 (some 416) mode⟩) : FinalAllocationArrival X i mode := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact ⟨2, he⟩
  · exact ⟨0, he⟩
  · exact ⟨1, he⟩

private def finalBranch (role : Fin 3) (op : Op) : Bool :=
  (op.isLocal || Epilogue.ordinaryEvent op) &&
  match op with
  | .bra dest _ => participantEntry role ≤ dest && dest ≤ participantFinal role
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem finalWindow : ∀ role : Fin 3,
    ((kernel.code.drop (participantEntry role)).take
      (participantFinal role + 1 - participantEntry role)).all (finalBranch role ·.op) = true :=
  by decide +kernel

private theorem finalControl {role : Fin 3} {pc : Nat} {ins : Instr}
    (hLo : participantEntry role ≤ pc) (hHi : pc ≤ participantFinal role)
    (hCode : kernel.code[pc]? = some ins) : finalBranch role ins.op = true := by
  apply List.all_eq_true.mp (finalWindow role) ins
  apply List.mem_of_getElem? (i := pc - participantEntry role)
  rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]

set_option maxRecDepth 100000 in
private theorem finalSegments : ∀ role : Fin 3,
    Assumptions.swExp2Sites.all (fun pc =>
      if participantEntry role ≤ pc ∧ pc ≤ participantFinal role then
        match cuteExp2.matchAt kernel pc with
        | some seg => participantEntry role ≤ seg.stop && seg.stop ≤ participantFinal role
        | none => false
      else true) = true := by decide +kernel

private theorem finalMarker (role : Fin 3) : ∃ ins, kernel.code[participantFinal role]? = some ins ∧
    ins.guard = none ∧ barOp ins.op = true := by
  have hAudit : ∀ r : Fin 3, (kernel.code[participantFinal r]?.map fun ins =>
      ins.guard.isNone && barOp ins.op) = some true := by decide +kernel
  obtain ⟨ins, hc, hShape⟩ := Option.map_eq_some_iff.mp (hAudit role)
  obtain ⟨hg, hb⟩ := Bool.and_eq_true_iff.mp hShape
  exact ⟨ins, hc, Option.isNone_iff_eq_none.mp hg, hb⟩

private theorem beforeFinalStep (role : Fin 3) {l : Launch} {g : Nat} {s u : TState}
    {event : Option Event} (hLo : participantEntry role ≤ s.pc)
    (hHi : s.pc ≤ participantFinal role) (hStep : WStep kernel Assumptions.all l g s event u) :
    participantEntry role ≤ u.pc ∧ barrierRemaining (participantFinal role) s =
      event.toList.countP (barrierMark (participantFinal role)) +
        barrierRemaining (participantFinal role) u := by
  have branch {ins dest uniform} (hc : kernel.code[s.pc]? = some ins)
      (ho : ins.op = .bra dest uniform) : participantEntry role ≤ dest ∧
        dest ≤ participantFinal role := by
    have h := (Bool.and_eq_true_iff.mp (finalControl hLo hHi hc)).2
    simpa [ho] using h
  have indirect {ins idx dests uniform} (hc : kernel.code[s.pc]? = some ins) :
      ins.op ≠ .brx idx dests uniform := by
    intro ho
    simpa [finalBranch, ho] using finalControl hLo hHi hc
  have segment {segment : SegMatch CuteSlot} (hm : s.pc ∈ Assumptions.swExp2Sites)
      (hs : cuteExp2.matchAt kernel s.pc = some segment) :
      participantEntry role ≤ segment.stop ∧ segment.stop ≤ participantFinal role := by
    have h := List.all_eq_true.mp (finalSegments role) s.pc hm
    rw [ite_eq_left ⟨hLo, hHi⟩, hs] at h
    simpa using h
  refine ⟨?_, markedBarrierTransition (finalMarker role)
    (fun hc ho => iff_of_true hHi (branch hc ho).2) indirect
    (fun _ hm hs => iff_of_true hHi (segment hm hs).2) hStep⟩
  rcases hStep with ⟨_, ht⟩ | ⟨_, _, he⟩
  · obtain ⟨ins, hc, _, hExec⟩ := Softmax.tauScoreSource ht
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · change participantEntry role ≤ s.pc + 1
      omega
    rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨seg, hm, hs, hr⟩
    · have hPc := hFrame.pc
      cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dest uni => exact hPc.symm ▸ (branch hc ho).1
      case brx idx ds uni => exact (indirect hc ho).elim
      all_goals omega
    · exact (Softmax.scoreSegmentFrame hr).1.symm ▸ (segment hm hs).1
  · obtain ⟨ins, hc, hl, hf⟩ := estep_event_source he
    have hOp := (Bool.and_eq_true_iff.mp (finalControl hLo hHi hc)).1
    have hOrdinary : Epilogue.ordinaryEvent ins.op = true := by simpa [hl] using hOp
    rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOrdinary) hf with h | h <;> omega

private theorem finalMarkerBeforeExit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (role : Fin 3)
    {g start finish : Nat} {s : TState} {outcome : Option TState}
    (hStart : start ≤ finish) (hs : s.pc = participantEntry role)
    (he : X.get (g,finish) = some ⟨9205, .exit⟩)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop start) outcome) :
    ∃ i < finish, ∃ id count mode,
      X.get (g,i) = some ⟨participantFinal role, .bar id count mode⟩ := by
  let marker := participantFinal role
  have hBounds := (by decide : ∀ r : Fin 3,
    participantEntry r ≤ participantFinal r ∧ participantFinal r < 9205) role
  have hFound : (⟨9205, .exit⟩ : Event) ∈ (X.tr g).drop start := by
    apply List.mem_of_getElem? (i := finish - start)
    rwa [List.getElem?_drop, Nat.add_sub_of_le hStart]
  obtain ⟨_, hw⟩ := TmlFa4Fwd.Mma.walkFromRun hr
  obtain ⟨_, before, rest, _, hTrace, _, _, _, hCount, hGood, _⟩ :=
    hw.cut_marked_where (P := fun t => participantEntry role ≤ t.pc)
      (cut := fun t => marker < t.pc) (good := fun e => e.pc ≤ marker)
      (barrierRemaining marker) (barrierMark marker)
      (fun t _ h => by simp [barrierRemaining, Nat.not_le_of_lt h])
      (fun hLo hHi => beforeFinalStep role hLo (Nat.le_of_not_gt hHi))
      (fun _ hHi he => (estep_source_pc he) ▸ Nat.le_of_not_gt hHi)
      hs.ge hFound (by
        intro t _ hHi hBad
        change t.pc = 9205 at hBad
        exact hHi (by rw [hBad]; exact hBounds.2))
  have hc : 0 < before.countP (barrierMark marker) := by
    rw [hCount]
    simp [barrierRemaining, hs, marker, hBounds.1]
  obtain ⟨e, hMem, hMarked⟩ := List.countP_pos_iff.mp hc
  have hPc : e.pc = marker := by simpa [barrierMark] using hMarked
  obtain ⟨pos, hGet⟩ := List.mem_iff_getElem?.mp hMem
  have hPos := (List.getElem?_eq_some_iff.mp hGet).1
  have hEarlier : start + pos < finish := by
    by_contra! hLate
    have hAt : (before ++ rest)[finish - start]? = some ⟨9205, .exit⟩ := by
      rwa [← hTrace, List.getElem?_drop, Nat.add_sub_of_le hStart]
    rw [List.getElem?_append_left (by omega)] at hAt
    have hBound := hGood _ (List.mem_of_getElem? hAt)
    change 9205 ≤ marker at hBound
    exact (Nat.not_le_of_gt hBounds.2) hBound
  have hActual : X.get (g,start+pos) = some e := by
    change (X.tr g)[start+pos]? = _
    rw [show (X.tr g)[start+pos]? = ((X.tr g).drop start)[pos]? by rw [List.getElem?_drop],
      hTrace, List.getElem?_append_left hPos, hGet]
  obtain ⟨_, trace⟩ := hX.thr _ (event_thread_lt hX hActual)
  have hLen : finish < (X.tr g).length := PTX.len_of_get he
  have hPast : start + pos + 1 < (X.tr g).length := by omega
  obtain ⟨_, _, hEvent, _⟩ := trace.after_event hActual hPast
  obtain ⟨ins, hc, _, hb⟩ := finalMarker role
  obtain ⟨_, id, count, mode, hKind⟩ := markedBarrierContinues
    ((estep_source_pc hEvent).symm.trans hPc) hc hb hEvent
  have hEq : e = ⟨participantFinal role, .bar id count mode⟩ := by
    cases e
    simp only [Event.mk.injEq]
    exact ⟨hPc, hKind⟩
  exact ⟨start + pos, hEarlier, id, count, mode, hEq ▸ hActual⟩

private theorem finalExitEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g finish : Nat} (hw : warpIndex l g < 13) (he : X.get (g,finish) = some ⟨9205, .exit⟩) :
    ∃ role : Fin 3, ∃ start ≤ finish, ∃ s o, s.pc = participantEntry role ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop start) o := by
  by_cases hMma : warpIndex l g = 12
  · obtain ⟨hIndex, u, o, hu, hr⟩ := mmaStartAfterAllocation hp hX he hMma (by decide)
    exact ⟨2, TmlFa4Fwd.Mma.allocationBarrierPos l g + 2, hIndex, u, o, hu.1, hr⟩
  have hg := event_thread_lt hX he
  obtain ⟨pos, t, o, hLe, ht, hr⟩ := Epilogue.commonDispatchOfLateEvent hp hX hg he (by decide)
  have hLen := PTX.len_of_get he
  have hNonempty : (X.tr g).drop pos ≠ [] := by
    intro h
    exact Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hLe)
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  obtain ⟨u, _, hHint, hu, hRun⟩ := firstRegisterHintFromCommon hp hg warp ht hr hNonempty
  have hBefore : pos < finish := by
    by_contra! h
    have hEq : pos = finish := by omega
    rw [hEq, he] at hHint
    have := congrArg Event.kind (Option.some.inj hHint)
    cases this
  by_cases hSoftmax : warpIndex l g < 8
  · have hSite : registerHintPc warp + 1 = participantEntry 0 := by
      dsimp [warp, registerHintPc, dispatchParamPc, participantEntry]
      split_ifs <;> omega
    exact ⟨0, pos+1, hBefore, u, o, hu.1.trans hSite, hRun⟩
  · have hSite : registerHintPc warp + 1 = participantEntry 1 := by
      dsimp [warp, registerHintPc, dispatchParamPc, participantEntry]
      split_ifs <;> omega
    exact ⟨1, pos+1, hBefore, u, o, hu.1.trans hSite, hRun⟩

/-- Each exiting participant in the allocation rendezvous has made its final arrival. -/
theorem finalAllocationArrivalBeforeExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g finish : Nat} (hw : warpIndex l g < 13)
    (he : ∃ pc, X.get (g,finish) = some ⟨pc, .exit⟩) :
    ∃ i < finish, ∃ mode, FinalAllocationArrival X (g,i) mode := by
  obtain ⟨pc, he⟩ := he
  obtain rfl := actualExitPc hX he
  obtain ⟨role, start, hLe, s, o, hs, hRun⟩ := finalExitEntry hp hX hw he
  obtain ⟨i, hBefore, id, cnt, mode, hGet⟩ := finalMarkerBeforeExit hX role hLe hs he hRun
  obtain ⟨_, hCount, _, _, _, _, hId⟩ := actualNamedBarrier hp hX hGet
  have hValue : namedBarrierCount (participantFinal role) = some 416 :=
    (by decide : ∀ r : Fin 3, namedBarrierCount (participantFinal r) = some 416) role
  have hc := hCount.trans hValue
  obtain rfl := hId hc
  obtain rfl := hc
  exact ⟨i, hBefore, mode, ⟨role, hGet⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread
