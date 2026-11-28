-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Lemmas.Flow.Polls
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaExit
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind

@[expose] public section

/-! # The MMA lane that exited has polled `bar_q_tma`

`mma_qPollExit`: from any event of the MMA code after the election, a lane that exited made its
one successful poll of `qTma` (the reference counts at the exit, `mma_exit_full`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- The MMA lane that exited has made the polls of `l` that its ledger counts at the exit. -/
private theorem poll_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k x pc : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hr0 : 1853 < e0.pc ∧ e0.pc < 2162) (hw : warp L y = 4)
    (hx : X.get (y, x) = some ⟨pc, .exit⟩) {l : Loc}
    (hq : Mma.cntAt (Mma.objs L y) 31 (blocksOf P L (y / L.block)) 0 true (.acq l) = 1) :
    1 ≤ okPolls l (X.tr y) := by
  have h3 := mma_exit_full hp hX hFw he0 hu0 hr0 hx (.acq l) (by simp)
  have hc := lane4_okPolls hp hX hFw hw x l
  have hle : okPolls l ((X.tr y).take x) ≤ okPolls l (X.tr y) :=
    (List.take_sublist _ _).countP_le
  rw [h3, hq] at hc
  exact hc ▸ hle

/-- **The MMA lane that exited has polled `qTma`**, from any event of the MMA code after the
election. -/
theorem mma_qPollExit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k x pc : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hr0 : 1853 < e0.pc ∧ e0.pc < 2162) (hw : warp L y = 4)
    (hx : X.get (y, x) = some ⟨pc, .exit⟩) :
    1 ≤ okPolls (mbarLoc L (y / L.block) .qTma) (X.tr y) :=
  poll_exit hp hX hFw he0 hu0 hr0 hw hx (by
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.obj_qTma hp, Mma.obj_qUt hp, Mma.obj_ready hp,
      Mma.obj_so hp, Mma.mloc_eq_iff, Mma.ind])

/-- **The MMA lane that exited has polled `qUtccp`** (pc 1983), from any event of the MMA code
after the election. -/
theorem mma_qUtPollExit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k x pc : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hr0 : 1853 < e0.pc ∧ e0.pc < 2162) (hw : warp L y = 4)
    (hx : X.get (y, x) = some ⟨pc, .exit⟩) :
    1 ≤ okPolls (mbarLoc L (y / L.block) .qUtccp) (X.tr y) :=
  poll_exit hp hX hFw he0 hu0 hr0 hw hx (by
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.obj_qTma hp, Mma.obj_qUt hp, Mma.obj_ready hp,
      Mma.obj_so hp, Mma.mloc_eq_iff, Mma.ind])

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
