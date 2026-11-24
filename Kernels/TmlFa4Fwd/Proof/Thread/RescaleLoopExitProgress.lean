-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionTerminal
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleSignalProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleLoopFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The last rescale iteration reaches the first terminal statistics wait,
retaining the same output layout and statistic frame as on single-visit tiles. -/
theorem firstTerminalOfRescaleExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g batch lane : Nat}
    (hg : warpLane l g lane < l.threads)
    (c : OpeningTripCursor l X (warpLane l g lane) 8447
      (rescaleLoopFacts (correctionRescaleFrame p l g batch) 1 lane)) :
    X.Arrive (warpLane l g lane,c.pos)
        ⟨.shared,warpLane l g lane/l.block,l.sharedBase+200⟩ 0 1 true .cta ∧
      ∃ d : FirstTerminalStatisticsCursor p l X g batch lane, d.index = c.pos+1 := by
  let thread := warpLane l g lane
  have hLayout : Holds c.ready.regs (correctionBeforeRescale p l g batch lane) :=
    ((holds_append _ _ _).1 c.checkpoint.2.2.2.2.2).2
  obtain ⟨v,hSteps,hv,hOut,hFresh⟩ := terminalCreditSetup hp (c.checkpoint.mono hLayout)
  let a : OpeningTripCursor l X thread 8464 (finalizeLayoutFacts l thread ++
      (7134,b32 p.scaleLog2Bits)::correctionBeforeRescale p l g batch lane) :=
    ⟨c.pos,c.before,v,c.ending,c.positive,c.bounded,c.released,hv,
      c.recorded,c.remaining,c.localSteps.trans hSteps⟩
  obtain ⟨he,b,hPos⟩ := unitArrivalOfMaximal hMax hg a hOut hFresh
  obtain ⟨d,hD⟩ := terminalCursorAfterCredit hp hMax hg b
  exact ⟨⟨_,he⟩,d,hD.trans hPos⟩

end PTX.Kernels.TmlFa4Fwd.Correction
