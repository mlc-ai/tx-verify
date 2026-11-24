-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Lemmas.Kernel.ReadValue
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0}

/-- The lower residue selected by the ballot is the work before the batch in this group. -/
theorem precedingGroupWork (p : Params) {first batch : Nat}
    (hFirst : first ≤ batch) (hb : batch < p.batch) (hGroup : batch < first + 31) :
    tilePrefix p first * p.heads +
      (∑ lane ∈ Finset.range (batch - first), groupLaneTiles p first lane) * p.heads =
      tilePrefix p batch * p.heads := by
  rw [← Nat.add_mul]
  congr 1
  rw [groupTiles_eq p (by omega) (by omega)]
  rw [Nat.min_eq_right (show batch - first ≤ 31 by omega),
    Nat.add_sub_of_le hFirst, Nat.min_eq_right (by omega)]

set_option maxRecDepth 3000 in

set_option maxRecDepth 3000 in

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
