-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionStatistics
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalLayout
import Kernels.TmlFa4Fwd.Flow.Code.Part132

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Prologue Epilogue

/-- The first terminal statistics arrival retains the state that resumes after synchronization. -/
structure FirstTerminalStatisticsCursor (p : Params) (l : Launch) (X : Execution)
    (g batch lane : Nat) where
  index : Nat
  state : TState
  ending : Option TState
  waited : Thread.CorrectionWaits X (warpLane l g lane,index) .terminal 0
  ready : At state 8466 (finalizeLayoutFacts l (warpLane l g lane) ++
    (7134,b32 p.scaleLog2Bits) :: correctionBeforeRescale p l g batch lane)
  recorded : Run kernel Assumptions.all l (warpLane l g lane) {}
    ((X.tr (warpLane l g lane)).take (index+1)) (some state)
  remaining : Run kernel Assumptions.all l (warpLane l g lane) state
    ((X.tr (warpLane l g lane)).drop (index+1)) ending

/-- Both the single-visit path and the rescale loop exit preserve this tile
frame when laying out the terminal statistic and its slot notification. -/
theorem terminalCreditSetup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch lane : Nat} {s : TState}
    (hs' : At s 8447 (correctionBeforeRescale p l g batch lane)) :
    let thread := warpLane l g lane
    let regs := finalizeLayoutFacts l thread ++
      (7134,b32 p.scaleLog2Bits)::correctionBeforeRescale p l g batch lane
    ∃ v, Relation.ReflTransGen (Tau kernel Assumptions.all l thread) s v ∧ At v 8464 regs ∧
      out kernel Assumptions.all l thread v = .ev (.arrive
        ⟨.shared,thread/l.block,l.sharedBase+200⟩ 0 (next (mbarStateDest v (some 9257)))
          1 true .cta) ∧ ∀ pair ∈ regs, pair.1 ≠ 9257 := by
  let thread := warpLane l g lane
  let F := correctionBeforeRescale p l g batch lane
  let F' := (7134,b32 p.scaleLog2Bits)::F
  have hFresh : ∀ pair ∈ F, pair.1 ≠ 7134 := by
    intro pair hm h
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    rw [h] at hMem
    exact (of_decide_eq_true rfl : 7134 ∉ F.map Prod.fst) hMem
  obtain ⟨t,hScale,ht⟩ := finalizeScaleStep hp (g := thread) hs' hFresh
  obtain ⟨v,hLayout,hv⟩ := finalizeLayout hp (g := thread) ht
    (by simp [thread,correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts])
    (by simp [thread,correctionBeforeRescale,tileSetupFrame,correctionActiveTileFacts,
      correctionTileFrame,afterCreditFacts,creditFacts,entryFacts,nonzeroBarrierFacts])
    (by simp [thread,correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts])
    (by simp [thread,correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts])
    (by set_option maxRecDepth 100000 in kernel_rfl)
  let regs := finalizeLayoutFacts l thread ++ F'
  have hCode : kernel.code[8464]? = some ⟨none,
      .mbarArrive 1628 0 (.imm 0) (.reg 6498) false true .cta (some 9257)⟩ := Flow.code_8464
  have hModel : out kernel Assumptions.all l thread v = out kernel [] l thread v := by
    apply Assumptions.out_all_eq_nil _ _ _ (hv.1.symm ▸ hCode) rfl
    all_goals rw [hv.1]; decide
  have hSlot : v.regs 1628 = some (b32 (l.sharedBase+200)) :=
    holds_lookup hv.2.2.2.2 (by rfl)
  have hLimit : l.sharedBase+200+0 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+200+0)%8 = 0 := by have := hp.shared.1; omega
  have hOut := correctionReleaseOut hv hModel hCode hSlot hv.2.2.2.2.1 hLimit hAlign
  refine ⟨v,(Relation.ReflTransGen.single hScale).trans hLayout,hv,
    by simpa only [Nat.add_zero] using hOut,?_⟩
  intro pair hm h
  have hMem := List.mem_map_of_mem (f := Prod.fst) hm
  rw [h] at hMem
  exact (of_decide_eq_true rfl : 9257 ∉ regs.map Prod.fst) hMem

/-- Join the first terminal statistics generation at the reached slot release. -/
theorem terminalCursorAfterCredit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch lane : Nat} (hg : warpLane l g lane < l.threads)
    (cur : OpeningTripCursor l X (warpLane l g lane) 8465
      (finalizeLayoutFacts l (warpLane l g lane) ++
        (7134,b32 p.scaleLog2Bits)::correctionBeforeRescale p l g batch lane)) :
    ∃ d : FirstTerminalStatisticsCursor p l X g batch lane, d.index = cur.pos := by
  let thread := warpLane l g lane
  have hPc : statsBarrierPc 0 false = 8465 := by decide
  have hCode' := statsBarrierCode (0 : Fin 2) false
  rw [hPc] at hCode'
  have hAt' := cur.checkpoint
  have hBar : cur.ready.regs (statsBarrierReg 0) = some (b32 (statsBarrierId l thread 0)) :=
    holds_lookup hAt'.2.2.2.2 (by rfl)
  have hModel' : out kernel Assumptions.all l thread cur.ready =
      out kernel [] l thread cur.ready := by
    apply Assumptions.out_all_eq_nil _ _ _ (hAt'.1.symm ▸ hCode') rfl
    all_goals rw [hAt'.1]; decide
  obtain ⟨he,hPrefix,hTail⟩ :=
    statsSyncOfCursor hMax hg cur (statsSyncOut hp 0 hAt' hCode' hModel' hBar)
  exact ⟨⟨cur.pos,next cur.ready,cur.ending,
    Thread.terminalWaitObservation 0 ((hAt'.1.trans hPc.symm) ▸ he),
    hAt'.next,hPrefix,hTail⟩,rfl⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch lane : Nat}
    (hg : warpLane l g lane < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2)
    (c : OpeningCorrectionStatistics p l X g batch lane 1)
    (hRelease : c.index+1 = (X.tr (warpLane l g lane)).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Step.Released l Y (warpLane l g lane))
include hp hMax hg hb hLo hHi hSingle c hRelease

/-- After opening statistics, a single-visit correction lane joins the terminal rendezvous. -/
theorem OpeningCorrectionStatistics.firstTerminalCursorAndCreditOfMaximal :
    X.Arrive (warpLane l g lane,c.index+1)
        ⟨.shared,warpLane l g lane/l.block,l.sharedBase+200⟩ 0 1 true .cta ∧
      Nonempty (FirstTerminalStatisticsCursor p l X g batch lane) := by
  let thread := warpLane l g lane
  let F := correctionBeforeRescale p l g batch lane
  obtain ⟨_,s,hSetup,hs⟩ := correctionLaneRescaleSetup hp hb hLo hHi c.ready
  have hs' : At s 8447 F := by
    simpa only [correctionRescaleSetupFacts,ite_eq_left hSingle] using hs
  obtain ⟨v,hSteps,hv,hOut,hFresh⟩ := terminalCreditSetup hp hs'
  obtain ⟨hCredit,⟨cur⟩⟩ := c.notifyRecordedOfMaximal hg hRelease
    ((run_rtg hSetup).trans hSteps) hOut (At.clear_state hv hFresh)
  obtain ⟨d,_⟩ := terminalCursorAfterCredit hp hMax hg cur
  exact ⟨hCredit,⟨d⟩⟩

/-- After opening statistics, a single-visit correction lane joins the terminal rendezvous. -/
theorem OpeningCorrectionStatistics.firstTerminalAndCreditOfMaximal :
    X.Arrive (warpLane l g lane,c.index+1)
        ⟨.shared,warpLane l g lane/l.block,l.sharedBase+200⟩ 0 1 true .cta ∧
      ∃ j, Thread.CorrectionWaits X (warpLane l g lane,j) .terminal 0 := by
  obtain ⟨hCredit,⟨cursor⟩⟩ := c.firstTerminalCursorAndCreditOfMaximal hp hMax hg hb hLo hHi
    hSingle hRelease
  exact ⟨hCredit,cursor.index,cursor.waited⟩

/-- After opening statistics, a single-visit correction lane joins the terminal rendezvous. -/
theorem OpeningCorrectionStatistics.firstTerminalOfMaximal :
    ∃ j, Thread.CorrectionWaits X (warpLane l g lane,j) .terminal 0 :=
  (c.firstTerminalAndCreditOfMaximal hp hMax hg hb hLo hHi hSingle hRelease).2
end

/-- Keep the terminal word frame and the actual lane suffix through named synchronization. -/
theorem FirstTerminalStatisticsCursor.resumeAtCursorOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hMax : Maximal l kernel Assumptions.all m X)
    {g batch lane : Nat} (c : FirstTerminalStatisticsCursor p l X g batch lane)
    (hRelease : c.index+1 = (X.tr (warpLane l g lane)).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Y.MemWrites = X.MemWrites ∧ Step.Released l Y (warpLane l g lane)) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      ∃ cur : OpeningTripCursor l Y (warpLane l g lane) 8466
        (finalizeLayoutFacts l (warpLane l g lane) ++
          (7134,b32 p.scaleLog2Bits) :: correctionBeforeRescale p l g batch lane),
        cur.pos = c.index+1 := by
  let thread := warpLane l g lane
  obtain ⟨_,he,_⟩ := c.waited
  have hb : c.index+1 ≤ (X.tr thread).length := len_of_get he
  by_cases hLast : c.index+1 = (X.tr thread).length
  · obtain ⟨Y,hY,hTrace,hWrites,hRel⟩ := hRelease hLast
    have hBound : c.index+1 ≤ (Y.tr thread).length := by rwa [hTrace]
    have hRecord := c.recorded
    have hRemain := c.remaining
    rw [← hTrace] at hRecord hRemain
    exact ⟨Y,hY,hTrace,hWrites,
      ⟨⟨c.index+1,c.state,c.state,c.ending,Nat.succ_pos _,hBound,fun _ => hRel,
        c.ready,hRecord,hRemain,.refl⟩,rfl⟩⟩
  · exact ⟨X,hMax,rfl,rfl,
      ⟨⟨c.index+1,c.state,c.state,c.ending,Nat.succ_pos _,hb,
        fun h => (hLast h).elim,c.ready,c.recorded,c.remaining,.refl⟩,rfl⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
