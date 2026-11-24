-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ShapeSmWait
public import Kernels.InklingRelDecode.Proof.Thread.EvWMma
public import Kernels.InklingRelDecode.Proof.Thread.EvWLoader
public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiBase

@[expose] public section

/-! # The positions of the six polls

The six poll sites of the program (the softmax region's `waitS` and `waitO`, the loader's `wait`,
the MMA warp's `kvWait` and `pWait`, the epilogue's `wait`) are at six distinct positions
(`pollIdx` tells them apart), and the poll branch after each is selected by the kernel's
assumption `pollAgree` (`uniPoll`). Both facts are computed on the program text. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Wp
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The positions of the six poll sites. -/
def pollPcs : List Nat :=
  [Sm.evPc .waitS, Sm.evPc .waitO, Loader.Site.wait.pc, Mma.Site.kvWait.pc, Mma.Site.pWait.pc,
    Epi.evPc .wait]

/-- The index of a poll position in `pollPcs`. -/
def pollIdx (pc : Nat) : Nat := pollPcs.idxOf pc

theorem idx_waitS : pollIdx (Sm.evPc .waitS) = 0 := by decide +kernel
theorem idx_waitO : pollIdx (Sm.evPc .waitO) = 1 := by decide +kernel
theorem idx_loader : pollIdx Loader.Site.wait.pc = 2 := by decide +kernel
theorem idx_kvWait : pollIdx Mma.Site.kvWait.pc = 3 := by decide +kernel
theorem idx_pWait : pollIdx Mma.Site.pWait.pc = 4 := by decide +kernel
theorem idx_epi : pollIdx (Epi.evPc .wait) = 5 := by decide +kernel

/-- **The poll branch after each poll site is selected by `pollAgree`.** -/
theorem pollPcs_sel : ∀ pc ∈ pollPcs, Assumptions.all.any (·.uniPoll (pc + 1)) = true := by
  decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Wp
