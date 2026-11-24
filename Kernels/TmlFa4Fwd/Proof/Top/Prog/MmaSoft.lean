-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Lag
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Blk
import Kernels.TmlFa4Fwd.Proof.Top.Released

@[expose] public section

/-! # E2: the polls of warp 12 whose producer is a softmax warp

The progress class this file owns, proved (`Prog.mmaSoft`): a poll of a P barrier is blocked by a
softmax or correction lane short of the round (`Protocol/P/Blk.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- **The polls of warp 12 whose producer is a softmax warp (`Progress.MmaLagFrom false`).** -/
theorem Prog.mmaSoft (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    Progress.MmaLagFrom false p L m := by
  intro X hX hub g d n r hg hw hσ hpoll _ ⟨w, hQ⟩ ho
  have hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none := by
    intro l r hr
    cases hf : r.fault with
    | none => rfl
    | some f => exact (noTma_of_safe hs hX (.inl ⟨l, r, hr, by simp [hf]⟩)).elim
  obtain ⟨hR, ht, hn, hok, hst⟩ := mma_p_poll hp hX hub hg hw hσ hpoll hQ
    (by simpa [Progress.fromLoader] using ho)
  exact p_lag hp hX (launchFollow hp hX) hff hub hg hw hσ hR ht hn hok hst

end PTX.Kernels.TmlFa4Fwd.Proof.Top
