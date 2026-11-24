-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueReadyWindow
import Kernels.TmlFa4Fwd.Proof.Thread.MmaDescriptorRole
import Lemmas.Flow.Final
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyShuffleAlignment
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveRanks

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.Kernels.TmlFa4Fwd.Thread
open PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

private def ValueObservation (l : Launch) (use : Nat) (e : Event) : Prop :=
  (∃ recv ok, e.kind = .shfl .idx (b32 (valueDescriptorLow l use)) 0 31 recv ok) ∧ use % 2 = 1

private abbrev ValueReadyTrace (l : Launch) := DescriptorTrace valueSelect (ValueObservation l)

private theorem valueSelectAway {e : Event} (h1 : e.pc ≠ 2308) (h2 : e.pc ≠ 2559) :
    valueSelect e = false := by simp [valueSelect, h1, h2]

private theorem traceOfValueWindow {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (steady : Bool) {g use : Nat} {s : TState}
    {es : List Event} {visits : List Visit} (hOdd : use % 2 = 1)
    (hs : At s ((valueDescriptorSite steady).prepare - 3) (ringFrame l 7207 7208 use))
    (hw : Walk kernel Assumptions.all l g s es visits)
    (after : ∀ {u tail post}, At u ((valueDescriptorSite steady).prepare + 9)
        (ringFrame l 7207 7208 use) →
      post.length < visits.length → Walk kernel Assumptions.all l g u tail post →
      ValueReadyTrace l (use + 1) tail) :
    ValueReadyTrace l (use + 1) es := by
  by_cases hMark : es.filterMap valueReadyMark = []
  · exact descriptorTraceQuiet (descriptorProjectionEmpty hMark).1
  obtain ⟨pre, tail, recv, ok, hSplit, hQuiet, hExit⟩ :=
    firstValueDescriptorOfReadyWindow hp steady hs hw hMark
  obtain ⟨hNo, hCount⟩ := descriptorProjectionEmpty hQuiet
  rw [hSplit]
  apply descriptorTraceAppend (observes := ValueObservation l) hNo
  rw [hCount, List.length_nil, Nat.add_zero]
  apply descriptorTraceAtHead (select := valueSelect) (observes
    := ValueObservation l) rfl ⟨⟨recv, ok, rfl⟩, hOdd⟩
  rcases hExit with rfl | ⟨u, post, hu, hLen, hW⟩
  · exact descriptorTraceQuiet (by simp)
  · exact after hu hLen hW

private def valueRemainder : ReadyInterval := ⟨2309, 2344, [2344], [2535, 7207, 7208]⟩

set_option maxRecDepth 100000 in
private theorem valueRemainderAudit :
    (((kernel.code.drop 2309).take (2344-2309)).zipIdx 2309).all
      (fun (ins,pos) => valueRemainder.code pos ins) = true := by kernel_rfl

private theorem valueRemainderCode {pos : Nat} {ins : Instr}
    (hs : valueRemainder.inside pos) (hc : kernel.code[pos]? = some ins) :
    valueRemainder.code pos ins = true := by
  have hLo : 2309 ≤ pos := hs.1
  have hHi : pos < 2344 := hs.2
  apply List.all_eq_true.mp valueRemainderAudit (ins,pos)
  apply List.mem_of_getElem? (i := pos-2309)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem traceAfterSteadyDescriptor {l : Launch} {g use : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (ht : At s 2309 (ringFrame l 7207 7208 use))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u tail post}, At u 2344 (ringFrame l 7207 7208 use) →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      ValueReadyTrace l (use+1) tail) : ValueReadyTrace l (use+1) es := by
  have hShape : RoleShape s := ⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩
  have hWarp : s.regs 1062 = some (b32 12) := holds_mem ht.2.2.2.2 (by
    simp [ringFrame,readyFrame])
  have hErase (e : Event) (he : valueRemainder.inside e.pc) : valueReadyMark e = none := by
    have hLo : 2309 ≤ e.pc := he.1
    have hHi : e.pc < 2344 := he.2
    have hNo := readyEventOutside 4 (e := e)
      (show 2297 ≤ e.pc ∧ e.pc < 2344 from ⟨by omega, hHi⟩)
    have hOff : valueSelect e = false := valueSelectAway (by omega) (by omega)
    simp [valueReadyMark, descriptorProjection, hOff, hNo]
  rcases certifiedIntervalCut valueReadyMark valueRemainder (by decide) valueRemainderCode
    hErase hw (by rw [ht.1]; decide) ⟨hShape,hWarp⟩ ht.2.2.2.2
    (by simp [ringFrame,readyFrame,valueRemainder]) with h |
      ⟨u,pre,tail,post,hEs,hMark,hLen,hPc,hFault,hRole,hRegs,hWalk⟩
  · exact descriptorTraceQuiet (descriptorProjectionEmpty h).1
  obtain ⟨hQuiet, hReady⟩ := descriptorProjectionEmpty hMark
  have hu : u.pc = 2344 := by simpa [valueRemainder] using hPc
  have hRun := after ⟨hu,hRole.1.2.2 (by omega),hRole.1.2.1,hFault,hRegs⟩ hLen hWalk
  rw [hEs]
  exact descriptorTraceAppend hQuiet (by simpa [hReady] using hRun)

set_option maxRecDepth 100000 in
private theorem afterValueFloor :
    (kernel.code.drop 2560).all (fun i => staysPastEvent 2560 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterValueSegments : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some s => decide (2560 ≤ s.stop)
    | none => false) = true := by kernel_rfl

private theorem noMoreValueDescriptors {l : Launch} {g use : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hFloor : 2560 ≤ s.pc)
    (hw : Walk kernel Assumptions.all l g s es vs) : ValueReadyTrace l use es := by
  apply descriptorTraceQuiet
  intro e he
  have h := eventTailEvents afterValueFloor afterValueSegments hw hFloor e he
  exact valueSelectAway (by omega) (by omega)

private theorem valueTailTrace {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g use : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (hOdd : use % 2 = 1) (ht : At t 2534 (ringFrame l 7207 7208 use))
    (hw : Walk kernel Assumptions.all l g t es vs) : ValueReadyTrace l use es := by
  apply descriptorTraceInterval (observes := ValueObservation l) 7 (by rw [ht.1]; decide)
    (fun e h => by
      have hLo : 2534 ≤ e.pc := h.1
      have hHi : e.pc < 2542 := h.2
      exact valueSelectAway (by omega) (by omega))
    ⟨rfl, ht.2⟩ (by simp [ringFrame, readyFrame])
      (by simp [ringFrame, readyFrame, readyInterval]) hw
  intro u tail post hExit hu _ hWalk
  have hu' : At u 2542 (ringFrame l 7207 7208 use) :=
    ⟨by simpa [readyInterval] using hExit, hu.2⟩
  apply descriptorTraceLocal (select := valueSelect) (observes := ValueObservation l)
    (readyAddress hp g 2 use) hu' hWalk
  intro v visits hv _ hV
  apply descriptorTracePoll (select := valueSelect) (observes := ValueObservation l) hp 3
    (by simp [descriptorReadyWait, waitSite, readyAddressSite, ringFrame, readyFrame])
    (by simp [descriptorReadyWait, waitSite, readyAddressSite])
    (by simp [descriptorReadyWait, waitSite, readyAddressSite, ringFrame])
    (fun _ => by simp [descriptorReadyWait, waitSite, valueSelect]) hv hV
  intro w rest wVisits _ hz hW
  have hAt : At w 2548 (ringFrame l 7207 7208 use) :=
    ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.2⟩
  exact traceOfValueWindow hp false hOdd hAt hW (fun hu _ hW =>
    noMoreValueDescriptors (by rw [hu.1]; decide) hW)

private theorem valueWindows {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) : DescriptorWindows l g valueSelect (ValueObservation l) := by
  refine ⟨?_, ?_, ?_, ?_, valueTailTrace hp, ?_⟩
  · intro e h
    exact valueSelectAway (by omega) (by omega)
  · intro i e h
    fin_cases i <;> simp [h, descriptorReadyWait, waitSite, valueSelect]
  · intro use t es vs hOdd ht hw after
    apply traceOfValueWindow hp true hOdd ht hw
    intro u rest post hu hLen hWalk
    exact traceAfterSteadyDescriptor hu hWalk (fun hAt hShort hW =>
      after hAt (hShort.trans hLen) hW)
  · intro use t es vs _ ht hw after
    apply descriptorTraceInterval (observes := ValueObservation l) 5 (by rw [ht.1]; decide)
      (fun e h => by
        have hLo : 2355 ≤ e.pc := h.1
        have hHi : e.pc < 2524 := h.2
        exact valueSelectAway (by omega) (by omega))
      ⟨rfl, ht.2⟩ (by simp [ringFrame, readyFrame])
      (by simp [ringFrame, readyFrame, readyInterval]) hw
    intro u tail post hExit hu hLen hWalk
    exact after ⟨by simpa [readyInterval] using hExit, hu.2⟩ hLen hWalk
  · intro t es vs ht hw
    exact noMoreValueDescriptors (by rw [ht.1]; decide) hw

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (steady : Bool) {g index : Nat}
    {sent recv : Value} {b c : Nat} {ok : Bool} (hWarp : Prologue.warpIndex l g = 12)
    (he : X.get (g,index) =
      some ⟨(valueDescriptorSite steady).prepare + 8, .shfl .idx sent b c recv ok⟩)
include hp hX steady hWarp he

/-- At either recurring V broadcast, the send word uses the latest completed ready acquire. -/
theorem actualValueDescriptorSentForReadyUse :
    let d := atPrefix l X g index
    let use := d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2 - 1
    sent = b32 (valueDescriptorLow l use) ∧ b = 0 ∧ c = 31 ∧ use % 2 = 1 := by
  have hSelect : valueSelect ⟨(valueDescriptorSite steady).prepare + 8,
      .shfl .idx sent b c recv ok⟩ = true := by
    cases steady <;> simp [valueSelect, valueDescriptorSite]
  obtain ⟨⟨reply, valid, hWire⟩, hOdd⟩ :=
    actualDescriptorTrace hp hX hWarp he (by change 1907 <
      (valueDescriptorSite steady).prepare + 8; cases steady <;> decide)
      hSelect (descriptorTraceFromEntry hp (valueWindows hp g))
  obtain ⟨_, hWord, hIndex, hClamp, _, _⟩ := Kind.shfl.inj hWire
  exact ⟨hWord, hIndex, hClamp, hOdd⟩


/-- The matching lane-zero sender uses the receiving lane's ready cursor. -/
theorem actualValueDescriptorReceivedForReadyUse :
    let d := atPrefix l X g index
    let use := d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2 - 1
    recv = b32 (valueDescriptorLow l use) ∧ use % 2 = 1 := by
  obtain ⟨_, rfl, rfl, hOdd⟩ := actualValueDescriptorSentForReadyUse hp hX steady hWarp he
  let pc := (valueDescriptorSite steady).prepare + 8
  let station : Fin 3 := if steady then 0 else 1
  have hStation : descriptorShuffleSite station = pc := by cases steady <;> rfl
  have hEvt : X.get (g,index) = some ⟨pc, .shfl .idx sent 0 31 recv ok⟩ := he
  let rank := ((X.tr g).take index).countP Execution.isShfl
  let peer := g - laneOf l g
  have hRank : X.ShflK (g,index) rank := ⟨⟨_, _, _, _, _, _, _, he⟩, rfl⟩
  obtain ⟨j, a, b, reply, valid, hPeerRank, hPeer⟩ :=
    cacheDescriptorShuffleSource hp hX station hWarp (hStation.symm ▸ hEvt) hRank
  have hPeer' : X.get (peer,j) = some ⟨pc,.shfl .idx recv a b reply valid⟩ := hStation ▸ hPeer
  have hSame : SameWarp l g peer :=
    (laneZero_sameWarp (by rw [hp.block]; decide) (event_thread_lt hX he)).1
  have hPeerWarp := hSame.2.symm.trans hWarp
  have hBounds : 2145 ≤ pc ∧ pc < 2768 := by cases steady <;> decide
  have hAvoid : ∀ j : Fin 4, pc ≠ (slotWait j).pc + 1 := by
    intro j
    cases steady <;> fin_cases j <;> decide
  have hEq := readyUsesAtMatchedShuffle hp hX hSame hRank hPeerRank hEvt hPeer'
    rfl rfl hBounds hAvoid hWarp hPeerWarp
  have hSent := (actualValueDescriptorSentForReadyUse hp hX steady hPeerWarp hPeer').1
  dsimp only at hEq hSent hOdd ⊢
  exact ⟨by rw [hEq]; exact hSent, hOdd⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
