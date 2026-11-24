-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringCopyGeometry
public import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Flow.Code.Part025

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The lane, stage, and swizzle column are actual at the beginning of any recurring
packet which computes its own swizzle. Every selected copy in that packet uses this stage. -/
theorem actualRecurringSwizzleGeometry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (site : Fin 3)
    {g index : Nat} {target : Loc}
    (he : X.get (g, index) =
      some ⟨reuseArrival (recurringSwizzlePacket site), .asyncArrive target true⟩) :
    let packet := recurringPacketSite (recurringSwizzlePacket site)
    let entry := recurringSwizzleEntry site
    ∃ (stage : Fin 3) (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ s.pc = entry ∧ RingShape s ∧
      target = Prologue.initObject l (g / l.block) (readySlot stage) ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents entry (copyCommitPc packet + 2) vs)[index - start]? =
        some ⟨copyCommitPc packet + 1, .asyncArrive target true⟩ ∧
      ∀ (group : Fin 16) (upper : Bool) (sp : AsyncCopy.Spec),
        ⟨packetPlanePc packet group upper, .copy sp⟩ ∈
          loaderSliceEvents entry (copyCommitPc packet) vs →
        sp.dst = {loc := ⟨.shared, g / l.block,
          kvCopyAddress l.sharedBase stage (g % l.block) group upper⟩, size := 16} := by
  dsimp only
  obtain ⟨stage, start, s, vs, hStart, hs, hLane, hw, hSeen⟩ :=
    actualReuseCheckpointWithLane hp hX (recurringSwizzlePacket site) he
  obtain ⟨_, _, _, _, hTarget, _⟩ := reuseEmptyPrefixFromCheckpoint hp
    (recurringSwizzlePacket site) stage hs hw (List.mem_of_getElem? hSeen)
  have hf : At s (recurringSwizzleEntry site)
      (recurringSwizzleEntryFacts l site (g % l.block) stage) := by
    fin_cases site
    · exact hs.mono ⟨hLane.1, hs.2.2.2.2.2.1, hLane.warmColumn hs.1, hs.2.2.2.2.1, trivial⟩
    · exact hs.mono ⟨hLane.1, hs.2.2.2.2.2.1, hs.2.2.2.2.1, trivial⟩
    · exact hs.mono ⟨hLane.1, hs.2.2.2.2.2.1, hLane.steadyColumn hs.1, hs.2.2.2.2.1, trivial⟩
  exact ⟨stage, start, s, vs, hStart, hs.1, ringShapeOfAt hs, hTarget, hw, hSeen,
    fun group upper sp h =>
      recurringCopyDestinationFromEntry hp stage.isLt site hf hw group upper h⟩

/-- The paired-value stage is the successor of the steady key swizzle's stage.
A returning event in the value packet witnesses the actual barrier-entry cursor. -/
theorem steadyVBarrierAfterSwizzle {l : Launch}
    {g : Nat} (k : Fin 3) {s : TState} {es : List Event} {vs : List Visit}
    {e : Event} (he : ¬ Ends e) (hLater : 1608 ≤ e.pc)
    (hs : At s 1451 [(7179, b32 k), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : e ∈ loaderSliceEvents 1451 1736 vs) :
    ∃ pre rest t visits,
      es = pre ++ rest ∧ (∀ prior ∈ pre, prior.pc < 1608) ∧
      At t 1608 [(1170, b32 ((k.val + 1) % 3)), (2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g t rest visits ∧
      e ∈ loaderSliceEvents 1451 1736 visits := by
  let stage : Fin 3 := ⟨(k.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
  let F := [(7179, b32 k), (2535, b32 l.sharedBase)]
  let G := [(1170, b32 stage), (2535, b32 l.sharedBase)]
  have hCode : ((kernel.code.drop 1451).take (1603 - 1451)).all
      (fun ins => loaderPipelineCutOp 1451 1603 1735 [7179, 2535] ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t, first, tail, front, visits, hSplit, _, hFront, ht, hShape, hf, hFirst, hTail, hSaw⟩ :=
    loaderObservedCut (F := F) (cut := 1603) (lower := 1451) (stop := 1736) (e := e)
      le_rfl (by decide) (by decide) (by decide) hCode hw ⟨hs.1.ge, hs.1.le.trans (by decide)⟩
      (ringShapeOfAt hs) hs.2.2.2.2 hSeen (by omega) he
  have hRaw {s : TState} {es : List Event} {vs : List Visit}
      (hw : Walk kernel Assumptions.all l g s es vs)
      (hm : e ∈ loaderSliceEvents 1451 1736 vs) : e ∈ es := by
    rw [hw.events]
    obtain ⟨v, hv, hev⟩ := List.mem_filterMap.mp hm
    exact List.mem_filterMap.mpr ⟨v, List.takeWhile_subset _ hv, hev⟩
  have hAt := pipelineAtCut ht hShape hf (walkWithContinuingEventClean hTail (hRaw hTail hSaw) he)
    ⟨_, Flow.code_1603, rfl⟩
  obtain ⟨u, hr, hu⟩ := steadyVStageRun (g := g) k t (hAt.mono ⟨hf.1, trivial⟩)
  have hSegment : ((kernel.code.drop 1603).take (1606 - 1603)).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op &&
        [2535].all fun r => !(loaderRingWrites ins.op).contains r) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨_, hKeep⟩ := loaderSegmentFrame (regs := [2535]) (by decide) (by decide)
    hSegment hr ht.ge (by rw [ht])
  have hg : Holds u.regs G := ⟨hu.2.2.2.2.1, (hKeep 2535 (by simp)).trans hf.2.1, trivial⟩
  obtain ⟨uv, hW, _, hU⟩ := loaderEventAfterLocal hr hTail hSaw
  have hEntry : ((kernel.code.drop 1606).take (1608 - 1606)).all
      (fun ins => loaderPipelineCutOp 1606 1608 1735 [1170, 2535] ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v, second, rest, middle, vv, hSplit', _, hMiddle, hv, hShape', hReg, hSecond, hV,
    hFound⟩ :=
    loaderObservedCut (F := G) (cut := 1608) (lower := 1606) (stop := 1736) (e := e)
      (by decide) (by decide) (by decide) (by decide) hEntry hW
      ⟨hu.1.ge, by rw [hu.1]; decide⟩ (ringShapeOfAt hu) hg hU
      hLater he
  have hv' := pipelineAtCut hv hShape' hReg (walkWithContinuingEventClean hV (hRaw hV hFound) he)
    ⟨_, Flow.code_1608, rfl⟩
  refine ⟨first ++ second, rest, v, vv, by rw [hSplit, hSplit', List.append_assoc],
    ?_, hv', hV, hFound⟩
  intro prior hPrior
  rcases List.mem_append.mp hPrior with hEarlier | hApproach
  · exact (preCutEventPc hFirst (fun a ha => (hFront a ha).2) hEarlier).trans
      (by decide : 1603 < 1608)
  · exact preCutEventPc hSecond (fun a ha => (hMiddle a ha).2) hApproach

private theorem steadyVReadySlot {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (k : Fin 3) {s : TState} {es : List Event} {vs : List Visit} {target : Loc}
    (hs : At s 1451 [(7179, b32 k), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : ⟨reuseArrival 3, .asyncArrive target true⟩ ∈ loaderSliceEvents 1451 1736 vs) :
    target = Prologue.initObject l (g / l.block)
      (readySlot ⟨(k.val + 1) % 3, Nat.mod_lt _ (by decide)⟩) := by
  let stage : Fin 3 := ⟨(k.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
  obtain ⟨_, _, _, _, _, _, hAt, hTail, hEvent⟩ :=
    steadyVBarrierAfterSwizzle k (by simp [Ends]) (show 1608 ≤ reuseArrival 3 by decide) hs hw hSeen
  obtain ⟨_, _, _, _, hTarget, _⟩ :=
    reuseEmptyPrefixFromEarlierScope hp 3 stage (by decide) hAt hTail hEvent
  exact hTarget

/-- The actual paired K swizzle and following stage transition determine the
destination of every selected copy in the steady V packet. -/
theorem actualSteadyVSwizzleGeometry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {target : Loc}
    (he : X.get (g, index) = some ⟨reuseArrival 3, .asyncArrive target true⟩) :
    ∃ (k : Fin 3) (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ s.pc = 1451 ∧ RingShape s ∧
      target = Prologue.initObject l (g / l.block)
        (readySlot ⟨(k.val + 1) % 3, Nat.mod_lt _ (by decide)⟩) ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents 1451 (reuseArrival 3 + 1) vs)[index - start]? =
        some ⟨reuseArrival 3, .asyncArrive target true⟩ ∧
      ∀ (group : Fin 16) (upper : Bool) (sp : AsyncCopy.Spec),
        ⟨packetPlanePc 5 group upper, .copy sp⟩ ∈ loaderSliceEvents 1451 1734 vs →
        sp.dst = {loc := ⟨.shared, g / l.block,
          kvCopyAddress l.sharedBase ((k.val + 1) % 3) (g % l.block) group upper⟩, size := 16} := by
  obtain ⟨k, start, s, vs, hStart, hs, hLane, hw, hSaw⟩ := actualSteadyVSwizzleCheckpoint hp hX he
  have hAt : At s 1451 (recurringSwizzleInputs l (g % l.block) 2 ++ [(7179, b32 k)]) :=
    hs.mono ⟨hLane.1, hs.2.2.2.2.2.1, hLane.steadySwizzleColumn hs.1, hs.2.2.2.2.1, trivial⟩
  have hReady := steadyVReadySlot hp k hs hw (List.mem_of_getElem? hSaw)
  exact ⟨k, start, s, vs, hStart, hs.1, ringShapeOfAt hs, hReady, hw, hSaw, fun group upper sp h =>
    steadyVCopyDestinationFromSwizzle hp k hAt hw group upper h⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
