-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVScratch
public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Lemmas.Flow.Fire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue

noncomputable section

private def gapEvent (e : Event) : Prop :=
  Execution.isShfl e = false ∧ isFullWarpVote e = false ∧ ∀ a bs, e.kind ≠ .wr a bs

/-- The stable V ABI needed after the final priming K copy. -/
def primingVHandoffFrame (p : Params) (l : Launch) (head : Nat) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (7295, b64 (l.localBase + 96))] ++ primingVScratchAbi p l head

end
end PTX.Kernels.TmlFa4Fwd.Loader
