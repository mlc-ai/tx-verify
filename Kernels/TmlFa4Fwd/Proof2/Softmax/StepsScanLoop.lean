-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoopWord
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoopDown
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoopUp0
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoopUp1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoopUp2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoopUp3
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoopUp4
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanLoopTotal

@[expose] public section

/-! # The softmax warps' scan: the scheduler loop's sites

`stepAt_scan_loop`: the step obligations of the `loop` scan's eight sites (`word`, `down`, the
five `up` steps and `total`), each proved in its own file (`StepsScanLoopWord.lean` and
friends) so that they check in parallel, and this theorem dispatching over the state's site. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_scan_loop (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .word .loop ∨ d.site = .down .loop ∨ (∃ j, d.site = .up .loop j) ∨
      d.site = .total .loop) :
    (codeD p L g).StepAt d := by
  rcases hs with h | h | ⟨j, h⟩ | h
  · exact stepAt_scan_loop_word hp _hg d hk ha h
  · exact stepAt_scan_loop_down hp _hg d hk ha h
  · fin_cases j
    · exact stepAt_scan_loop_up0 hp _hg d hk ha h
    · exact stepAt_scan_loop_up1 hp _hg d hk ha h
    · exact stepAt_scan_loop_up2 hp _hg d hk ha h
    · exact stepAt_scan_loop_up3 hp _hg d hk ha h
    · exact stepAt_scan_loop_up4 hp _hg d hk ha h
  · exact stepAt_scan_loop_total hp _hg d hk ha h

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
