-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WqGuard

@[expose] public section

/-! # `Safety.Protocol.warpUniform` from `PollSynced`

ERR-NONUNIFORM-GUARD compares, between two lanes of a warp, the records of the instructions that
compare a guard or an index (`Instr.laneCompared`). In this program they are the six poll branches
and the six guarded `.sync.aligned` `tcgen05` instructions of `Wq.U` (`Wq.lane_ok`). At the
latter the guards agree in every record of every walk (`Wq.not_divergentAt`, a register
invariant of every thread state). The local steps of the kernel's assumptions land at the next
position or off the poll branches (`Wq.localLands`). What is left is the order of the polls of one
position at different objects (`PollSynced`): `not_warpDivergent_synced'` then gives
`¬ WarpDivergent`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Wq
open PTX PTX.Proof

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **No warp-divergent execution**, given that polls of one position at different objects by two
lanes of a warp are ordered (`PollSynced`). -/
theorem warpUniform_of (hpre : Pre Q L mem0) (hsync : PollSynced L kernel Assumptions.all X) :
    ¬ WarpDivergent L kernel Assumptions.all X := by
  have hb := hpre.block
  have hn : L.ntid = ⟨L.block, 1, 1⟩ := by rw [hpre.ntid, hb]
  exact not_warpDivergent_synced' lane_ok (not_divergentAt hn hb) localLands hsync

end
end PTX.Kernels.InklingRelDecode.Proof.Wq
