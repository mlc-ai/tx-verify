-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaValueAnchorReady
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
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

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
private theorem shortValueTail :
    (kernel.code.drop 2548).all (fun i => Thread.staysPastEvent 2548 i.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem shortValueSegments :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (2548 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem markerSome {e v : Event} (h : valueAnchorShuffle e = some v) :
    e = v ∧ (2307 ≤ e.pc ∧ e.pc < 2534 ∨ 2558 ≤ e.pc) ∧ Execution.isShfl e = true := by
  unfold valueAnchorShuffle at h
  split at h
  · rename_i hm
    exact ⟨Option.some.inj h, hm⟩
  · contradiction

private theorem markerEmpty {es : List Event} (h : es.filterMap valueAnchorShuffle ≠ []) :
    ∃ e ∈ es, (2307 ≤ e.pc ∧ e.pc < 2534 ∨ 2558 ≤ e.pc) ∧ Execution.isShfl e = true := by
  cases hMap : es.filterMap valueAnchorShuffle with
  | nil => exact (h hMap).elim
  | cons e tail =>
    obtain ⟨v,hV,hSome⟩ := List.mem_filterMap.mp (show e ∈ es.filterMap valueAnchorShuffle by
      rw [hMap]; exact List.mem_cons_self)
    exact ⟨v,hV,(markerSome hSome).2⟩

private theorem walkShuffle {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {mode : ShflMode} {sent : Value} {b c : Nat}
    {k : Value → Bool → TState}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hOut : out kernel Assumptions.all l g s = .ev (.shfl mode sent b c k))
    (hEvents : es ≠ []) :
    ∃ recv ok tail post, es = ⟨s.pc, .shfl mode sent b c recv ok⟩ :: tail ∧
      Walk kernel Assumptions.all l g (k recv ok) tail post := by
  cases hw with
  | stop => contradiction
  | tau h _ => simp [Tau,hOut] at h
  | ev h hTail =>
    obtain ⟨other,hTpl,hFire⟩ := h
    obtain rfl := Out.ev.inj (hOut.symm.trans hTpl)
    obtain ⟨recv,ok,rfl,hAfter⟩ := hFire
    obtain rfl := Option.some.inj hAfter
    exact ⟨recv,ok,_,_,rfl,hTail⟩
  | last h =>
    obtain ⟨other,hTpl,hFire⟩ := h
    obtain rfl := Out.ev.inj (hOut.symm.trans hTpl)
    obtain ⟨_,_,_,hImpossible⟩ := hFire
    cases hImpossible

/-- Evidence that the trace reaches the descriptor broadcast in the initial value path. -/
def valueBroadcastReached (es : List Event) : Prop :=
  1 < (es.filterMap valueAnchorShuffle).length ∨
    ∃ e ∈ es.filterMap valueAnchorShuffle, e.pc ≠ 2307 ∧ e.pc ≠ 2558

private theorem valueBroadcastReached.ne_nil {es : List Event} (h : valueBroadcastReached es) :
    es.filterMap valueAnchorShuffle ≠ [] := by
  intro hNil
  simp [valueBroadcastReached,hNil] at h

private theorem valueBroadcastsFromWait {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (steady : Bool) {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s ((waitSite (initialValueWaitSite steady)).pc + 3)
      (initialValueWaitFacts l steady)) (hw : Walk kernel Assumptions.all l g s es vs)
    (hReached : valueBroadcastReached es) :
    ∃ recv ok pre prob tail u post,
      es = pre ++ prob :: valueDescriptorEvent l steady recv ok :: tail ∧
      pre.filterMap valueAnchorShuffle = [] ∧ valueAnchorShuffle prob = some prob ∧
      At u ((valueDescriptorSite steady).prepare + 9)
        [((valueDescriptorSite steady).output,recv),(1062,b32 12)] ∧
      Walk kernel Assumptions.all l g u tail post := by
  let site := valueDescriptorSite steady
  let start := (waitSite (initialValueWaitSite steady)).pc + 3
  let F := [(7207, b32 (kvSlot 1)), (2535, b32 l.sharedBase), (1062, b32 12)]
  have hBounds : 1907 ≤ start ∧ start ≤ site.prepare ∧ site.prepare + 8 < 2768 := by
    cases steady <;> decide
  have hF : Holds s.regs F := by
    have hRegs := hs.2.2.2.2
    exact ⟨hRegs.2.1, hRegs.2.2.2.1, hRegs.2.2.2.2.1, trivial⟩
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩, hF.2.2.1⟩
  have hAudit : ((kernel.code.drop start).take (site.prepare - start)).all
      (pvCutCode start site.prepare (F.map Prod.fst)) = true := by
    cases steady <;> set_option maxRecDepth 100000 in kernel_rfl
  have hShort : steady = false → ∀ e ∈ es, 2548 ≤ e.pc := by
    intro h
    subst steady
    exact Thread.eventTailEvents shortValueTail shortValueSegments hw (by rw [hs.1]; decide)
  obtain ⟨target,hTarget,hMark,_⟩ := markerEmpty hReached.ne_nil
  have hTargetLate : site.prepare < target.pc := by
    cases steady
    · have := hShort rfl target hTarget
      change 2551 < target.pc
      omega
    · change 2300 < target.pc
      omega
  obtain ⟨t, pre, rest, visits, hSplit, htPc, htShape, htF, htWalk, htLater, hBefore⟩ :=
    pvWalkCut hBounds.1 (by omega) hAudit hw (show start ≤ s.pc ∧ s.pc ≤ site.prepare by
      rw [hs.1]; exact ⟨le_rfl, hBounds.2.1⟩) hShape hF hTarget hTargetLate.le
  have hNeutral : pre.filterMap valueAnchorShuffle = [] := List.filterMap_eq_nil_iff.mpr <| by
    intro e he
    have hEarly := hBefore e he
    have hMem : e ∈ es := hSplit ▸ List.mem_append_left _ he
    have hBelow : ¬ (2307 ≤ e.pc ∧ e.pc < 2534 ∨ 2558 ≤ e.pc) := by
      cases steady
      · have := hShort rfl e hMem
        change e.pc < 2551 at hEarly
        omega
      · change e.pc < 2300 at hEarly
        omega
    simp [valueAnchorShuffle,hBelow]
  have hRestReached : valueBroadcastReached rest := by
    simpa [valueBroadcastReached,hSplit,hNeutral] using hReached
  have ht : At t site.prepare F :=
    ⟨htPc, htShape.1.2.2 (by rw [htPc]; cases steady <;> decide), htShape.1.2.1,
      normalBeforeLaterEvent htWalk htLater (by rw [htPc]; exact hTargetLate), htF⟩
  obtain ⟨v,hLocal,hv⟩ := valueDescriptorLocalWithProbability hp g steady 1 t ht
  have hStraight : ((kernel.code.drop site.prepare).take (7-1)).all
      (fun i => schedulerFallsThrough i.op) = true := by
    cases steady <;> set_option maxRecDepth 100000 in kernel_rfl
  have hLocal' := localRun (show 1904 ≤ site.prepare by omega) (by omega) htPc hStraight hLocal
  rcases advanceWalkLocals hLocal' htWalk with hEmpty | ⟨post,_,_,hvWalk⟩
  · exact (hRestReached.ne_nil (by rw [hEmpty]; rfl)).elim
  let G := [(site.input,b32 (valueDescriptorLow l 1)),(1062,b32 12)]
  have hvProb := hv.mono (show Holds v.regs [((valueProbabilityRegs steady).1,b32 64)] from
    ⟨hv.2.2.2.2.1,trivial⟩)
  have hvWord : At v (site.prepare+7) G := hv.mono hv.2.2.2.2.2
  obtain ⟨r,o,following,followingVisits,hProb,hFollowing⟩ :=
    walkShuffle hvWalk (valueProbabilityShuffle hp steady hvProb)
      (fun h => hRestReached.ne_nil (by rw [h]; rfl))
  let prob : Event := ⟨v.pc,.shfl .idx (b32 64) 0 31 r o⟩
  have hProbMarked : valueAnchorShuffle prob = some prob := by
    rcases steady with _ | _ <;> simp [prob, valueAnchorShuffle, hvWord.1,
      site,valueDescriptorSite,Execution.isShfl]
  have hProbPc : prob.pc = 2307 ∨ prob.pc = 2558 := by
    cases steady <;> simp [prob,hvWord.1,site,valueDescriptorSite]
  have hTailNonempty : following ≠ [] := by
    intro h
    change rest = prob :: following at hProb
    simp [valueBroadcastReached,hProb,h,hProbMarked] at hRestReached
    exact hProbPc.elim hRestReached.1 hRestReached.2
  have hb := hvWord.set (r := (valueProbabilityRegs steady).2) (v := r) (by
    cases steady <;> simp [G,site,valueDescriptorSite,valueProbabilityRegs])
  have hbWord := hb.mono (show Holds _ [(site.input,b32 (valueDescriptorLow l 1))] from
    ⟨hb.2.2.2.2.2.1,trivial⟩)
  obtain ⟨recv,ok,tail,post,hDescriptor,hWalk⟩ :=
    walkShuffle hFollowing (valueDescriptorShuffle hp steady 1 hbWord) hTailNonempty
  have hbWarp := hb.mono (show Holds _ [(1062,b32 12)] from ⟨hb.2.2.2.2.2.2.1,trivial⟩)
  have hState := hbWarp.set (r := site.output) (v := recv) (by
    cases steady <;> simp [site,valueDescriptorSite])
  refine ⟨recv,ok,pre,prob,tail,_,post,?_,hNeutral,hProbMarked,?_,hWalk⟩
  · simp [hSplit,hProb,hDescriptor,hb.1,prob,valueDescriptorEvent,site,Nat.add_assoc]
  · simpa [Nat.add_assoc] using hState

/-- The second actual shuffle after the common initial release is the slot-one
V descriptor broadcast on either path, even if the prefix stops at the broadcast. -/
theorem initialValueBroadcastFromAnchor {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 2272 (readyFrame l)) (hw : Walk kernel Assumptions.all l g s es vs)
    (hReached : valueBroadcastReached es) :
    ∃ steady recv ok pre prob tail u post,
      es = pre ++ prob :: valueDescriptorEvent l steady recv ok :: tail ∧
      pre.filterMap valueAnchorShuffle = [] ∧ valueAnchorShuffle prob = some prob ∧
      At u ((valueDescriptorSite steady).prepare + 9)
        [((valueDescriptorSite steady).output,recv),(1062,b32 12)] ∧
      Walk kernel Assumptions.all l g u tail post ∧
      0 < (pre.filterMap readyEvent).length := by
  obtain ⟨steady,t,pre,rest,visits,hSplit,hClean,ht,hWalk,hReady⟩ :=
    valueSuccessFromAnchor hp hs hw hReached.ne_nil
  have hRest : valueBroadcastReached rest := by
    simpa [valueBroadcastReached,hSplit,hClean] using hReached
  obtain ⟨recv,ok,pre',prob,tail,u,post,hEvent,hClean',hProb,hu,huWalk⟩ :=
    valueBroadcastsFromWait hp steady ht hWalk hRest
  refine ⟨steady,recv,ok,pre++pre',prob,tail,u,post,
    by simp [hSplit,hEvent,List.append_assoc],by simp [hClean,hClean'],hProb,hu,huWalk,?_⟩
  rw [List.filterMap_append,List.length_append]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Mma
