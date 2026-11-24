-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
import Kernels.TmlFa4Fwd.Proof.Lib.PollSpin

@[expose] public section

/-! # ERR-POLL-SHAPE: every poll is a canonical spin (`poll_canonical`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Flow

/-- **ERR-POLL-SHAPE**: every poll is a canonical spin. -/
theorem noPollShapeUnsafe {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) : ¬ PollShapeUnsafe kernel X := by
  rintro ⟨i, pc, loc, q, ok, acq, sc, he, hn, _⟩
  exact hn (poll_canonical hX he)

end PTX.Kernels.TmlFa4Fwd.Proof
