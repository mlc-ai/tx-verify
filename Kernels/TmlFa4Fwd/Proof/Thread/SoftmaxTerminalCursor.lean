-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalRetire
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxIdleProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Correction

private theorem activeTerminalStageCompare (l : Launch) (g : Nat) (warp : Fin 8) (parity : Nat) :
    Seg kernel Assumptions.all l g 1 7733 ((7258,b32 parity) :: idleCarry l warp) 7734
      ((680,.pred (decide (3 < warp.val))) :: (7258,b32 parity) :: idleCarry l warp) := by
  have hWarp31 : warp.val < 2 ^ 31 := by have := warp.isLt; omega
  have hWarp32 : warp.val < 2 ^ 32 := by omega
  have hThree : toSigned 32 (truncBits 32 3#64) = (3 : Int) := by decide
  intro t ht
  simp only [idleCarry] at ht ⊢
  seg_fp ht using
    simp [truncBits_ofNat hWarp32 (by decide), compare, signedIdleWord hWarp31,
      hThree, Option.getD_some]

private theorem activeTerminalAddressLow (l : Launch) (g : Nat) (warp : Fin 8) (parity : Nat)
    (hBase : l.sharedBase + 232448 ≤ 2 ^ 18) :
    Seg kernel [] l g 4 7734
      ((680,.pred false) :: (7258,b32 parity) :: idleCarry l warp)
      7738 ((5864,b32 (l.sharedBase+192)) :: (7258,b32 parity) :: idleCarry l warp) := by
  intro t ht
  simp only [idleCarry] at ht ⊢
  have hh := congrArg (Value.bits 32) (terminalAddressBits false hBase)
  have hWord : truncBits 32 (BitVec.ofNat 64 l.sharedBase) = BitVec.ofNat 64 l.sharedBase :=
    truncBits_ofNat (by omega) (by decide)
  seg_fp ht using
    (simp only [show (some IType.u == some IType.s) = false by decide,
      Bool.false_eq_true, ↓reduceIte, hWord]; exact hh)

private theorem activeTerminalAddressHigh (l : Launch) (g : Nat) (warp : Fin 8) (parity : Nat)
    (hBase : l.sharedBase + 232448 ≤ 2 ^ 18) :
    Seg kernel [] l g 4 7734
      ((680,.pred true) :: (7258,b32 parity) :: idleCarry l warp)
      7738 ((5864,b32 (l.sharedBase+200)) :: (7258,b32 parity) :: idleCarry l warp) := by
  intro t ht
  simp only [idleCarry] at ht ⊢
  have hh := congrArg (Value.bits 32) (terminalAddressBits true hBase)
  have hWord : truncBits 32 (BitVec.ofNat 64 l.sharedBase) = BitVec.ofNat 64 l.sharedBase :=
    truncBits_ofNat (by omega) (by decide)
  seg_fp ht using
    (simp only [show (some IType.u == some IType.s) = false by decide,
      Bool.false_eq_true, ↓reduceIte, hWord]; exact hh)

private theorem activeTerminalAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (warp : Fin 8) (parity : Nat) :
    Seg kernel Assumptions.all l g 5 7733 ((7258,b32 parity) :: idleCarry l warp) 7738
      (terminalPollFacts l g warp parity) := by
  intro t ht
  obtain ⟨u,hu,hU⟩ := activeTerminalStageCompare l g warp parity t ht
  have hB := warp.isLt
  by_cases hStage : 3 < warp.val
  · have hStageVal : (stageOf warp).val = 1 := by change warp.val / 4 = 1; omega
    rw [decide_eq_true hStage] at hU
    obtain ⟨v,hv,hV⟩ := activeTerminalAddressHigh l g warp parity hp.shared.2.1 u hU
    exact ⟨v,run_comp hu (terminalTransport hU.1 hv),
      by simpa only [terminalPollFacts,waitLoc,waitSite,hStageVal] using hV⟩
  · have hStageVal : (stageOf warp).val = 0 := by change warp.val / 4 = 0; omega
    rw [decide_eq_false hStage] at hU
    obtain ⟨v,hv,hV⟩ := activeTerminalAddressLow l g warp parity hp.shared.2.1 u hU
    exact ⟨v,run_comp hu (terminalTransport hU.1 hv),
      by simpa only [terminalPollFacts,waitLoc,waitSite,hStageVal] using hV⟩

/-- The reached end of the scheduler drain retains the actual parity to be
used by the softmax lane's final credit acquire. -/
@[no_expose] def TerminalSchedulerFinished (l : Launch) (X : Execution) (g : Nat)
    (warp : Fin 8) (parity : Nat) : Prop :=
  Nonempty (OpeningTripCursor l X g 7733 ((7258,b32 parity) :: idleCarry l warp))

theorem TerminalSchedulerFinished.ofCursor {l : Launch} {X : Execution} {g : Nat}
    {warp : Fin 8} {parity : Nat}
    (c : OpeningTripCursor l X g 7733 ((7258,b32 parity) :: idleCarry l warp)) :
    TerminalSchedulerFinished l X g warp parity := ⟨c⟩

/-- Computing the terminal credit address preserves the real visit-dependent parity. -/
theorem terminalPollOfSchedulerFinished {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g : Nat} (warp : Fin 8) (parity : Nat)
    (hDrain : TerminalSchedulerFinished l X g warp parity) :
    Nonempty (OpeningTripCursor l X g 7738 (terminalPollFacts l g warp parity)) := by
  obtain ⟨c⟩ := hDrain
  obtain ⟨u,hRun,hAt⟩ := activeTerminalAddress hp g warp parity c.ready c.checkpoint
  exact ⟨⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hAt,c.recorded,
    c.remaining,c.localSteps.trans (run_rtg hRun)⟩⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
