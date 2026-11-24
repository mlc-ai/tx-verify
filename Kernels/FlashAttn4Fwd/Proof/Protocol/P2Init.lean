-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.InitFirst
public import Kernels.FlashAttn4Fwd.Proof.Protocol.P2Obj

@[expose] public section

/-! # The second P-ready objects are initialized first

`P2Init`: stage `st`'s second P-ready object of the pair led by `c` (count 8) is initialized
first, once, without fault. Its users are of its cluster (`InitFirst.Users`): the arrivals are
softmax threads of the pair led by `c`, the polls are the leader's, and no copy completes on it
(`P2Facts`). The generic `InitFirst.init_first` gives the rest, as for `InitFirst.pReadyInit`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.InitFirst
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`P2Init`**: every second P-ready object is initialized first, once, with count 8. -/
theorem p2Init (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (hp : P2Facts L X) :
    Score.P2Init L X := by
  intro c st _ hst
  refine init_first hpre hX hc htm hi (.pReady2 ⟨st, hst⟩) c ⟨fun hg he => ?_, fun hg he => ?_,
    fun he hm => absurd hm (hp.p2_tensor hst he)⟩
  · obtain ⟨hl, -⟩ := hp.p2_arrive hg hst he
    show _ = c / 2
    rw [← hl, leadCta]
    omega
  · obtain ⟨rfl, -⟩ := hp.p2_poll hg hst he
    rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof.InitFirst
