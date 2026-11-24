-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaIdleRendezvous
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAlignedTensor
import Kernels.TmlFa4Fwd.Proof.MmaTail

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue
open Correction (OpeningTripCursor)

/-- Once the drain scheduler reaches relinquish, maximality records the actual collective. -/
theorem relinquishOfDrainCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g 2763 F) :
    MmaRelinquishPrefix l X g := by
  have hAt := c.checkpoint
  have hOut : out kernel Assumptions.all l g c.ready =
      .ev (.tc (.resource .one none .relinquish) (next c.ready)) := by
    rw [out_eq_core (by rw [hAt.1]; decide) (by rw [hAt.1]; decide),
      out_event hAt.2.2.2.1 (hAt.1.symm ▸ Flow.code_2763) rfl rfl]
    change Out.ev (tcTmpl l g c.ready (.tcRelinquish .one)) = _
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    simp [tcTmpl,hBlock,ofExec,pure,Except.pure]
  let hn : Next kernel Assumptions.all l g c.before c.ready
      (.tc (.resource .one none .relinquish) (next c.ready)) := ⟨c.localSteps,hOut⟩
  obtain ⟨he,hFault,hPast,hRest⟩ :=
    relinquishAtCursor hMax hg c.positive c.bounded c.released hAt.1 hn c.recorded c.remaining
  exact ⟨c.pos,next c.ready,c.ending,he,Thread.mmaResourceCollectiveOrdinal hp hMax.1 hw he rfl,
    congrArg (·+1) hAt.1,hFault,hPast,hRest⟩

end PTX.Kernels.TmlFa4Fwd.Mma
