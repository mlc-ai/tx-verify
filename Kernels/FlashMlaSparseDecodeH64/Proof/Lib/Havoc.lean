-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Lemmas.Flow.Havoc

@[expose] public section

/-! # The havoc hook table of the kernel

`Havoc.Hooks` accounts for the assumptions that select a segment. No assumption of this kernel
takes a segment (`asms_segment_free`): the peer-score packs (pcs 394 to 473,
`Assumptions.peerPack`) and the dead packs (`Assumptions/DeadPack.lean`) are single-instruction
local rules folded into `sharedBits`, so `rulesFrame` (`Lib/RulesFrame.lean`) covers them and a
havoc crossing of the peer region needs no hook. The table is empty. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.KernelHavoc
open PTX PTX.Flow

/-- No pc of the kernel starts an assumption segment. -/
def hooks (_ : Nat) : Option Havoc.Hook := none

theorem hooks_ok {L : Launch} {g : Nat} : Havoc.Hooks Assumptions.all L g hooks := by
  intro t a u _ _ ha hr
  rw [asms_segment_free L g t a ha] at hr
  cases hr

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.KernelHavoc
