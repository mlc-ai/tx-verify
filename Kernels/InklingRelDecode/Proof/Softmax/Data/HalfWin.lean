-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsLoad
public import Kernels.InklingRelDecode.Proof.Lib.WinSet

@[expose] public section

/-! # The windows of the bias path, checked

The setup code of the softmax (pcs 576 to 948, the loop's first loads and the epilogue's start) is
one window `ceWin`: local steps stay inside and none enters it, so a state of a lane inside it
comes from the state after an event at its edge. The events that matter for the bias registers are
the barrier of pc 575, the 64 preloads and the arrival of pc 1013. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.InklingRelDecode.Proof.Lib

set_option maxRecDepth 100000

noncomputable section

/-- The window of the setup: the code after the barrier of pc 575 and the arrival of pc 1013. -/
def ceWin : List (Nat × Nat) := [(576, 948), (1013, 1261), (2560, 2603), (2609, 2846)]
/-- The part of it from the arrival of pc 1013 on. -/
def hiWin : List (Nat × Nat) := [(1013, 1261), (2560, 2603), (2609, 2846)]
/-- The part of it from the loop's loads on. -/
def hi2Win : List (Nat × Nat) := [(1049, 1261), (2560, 2603), (2609, 2846)]
/-- The part of it without the arrival's code. -/
def loWin : List (Nat × Nat) := [(576, 948), (1049, 1261), (2560, 2603), (2609, 2846)]

theorem ce_fwd : fwdOk ceWin [] = true := by decide +kernel
theorem ce_enter : enterOk ceWin 0 = true := by decide +kernel
theorem ce_zero : inS ceWin 0 = false := by decide +kernel
theorem hi_fwd : fwdOk hiWin [] = true := by decide +kernel
theorem hi2_fwd : fwdOk hi2Win [] = true := by decide +kernel
theorem lo_fwd : fwdOk loWin [] = true := by decide +kernel
theorem ce_events : ∀ q ∈ entryEvents ceWin, q = 575 ∨ (680 ≤ q ∧ q ≤ 806 ∧ q % 2 = 0) ∨
    q = 1012 ∨ q = 1013 ∨ 1124 ≤ q := by decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
