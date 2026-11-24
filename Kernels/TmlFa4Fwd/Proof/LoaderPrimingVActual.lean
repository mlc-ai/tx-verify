-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVKnownMetadata
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVMaskReplay
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVCommitCursor
import Kernels.TmlFa4Fwd.Flow.Code.Part008

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

theorem vFrameAfterMasks (p : Params) (l : Launch) (g batch qHead qTile kTile lane : Nat)
    {R : Nat → Option Value}
    (h : Holds R (primingMaskFrame p l batch qHead qTile kTile (Prologue.warpIndex l g) lane 16)) :
    Holds R (vPacketAfterKFrame p l g batch (qHead / 6) kTile
      (fun _ => vPrimingResidual p batch qTile) lane) := by
  obtain ⟨hMasks, hFrame⟩ := (holds_append ..).mp h
  unfold vPacketAfterKFrame vPacketFrame primingVPacketFrame
  refine (holds_append ..).mpr ⟨?_, (holds_append ..).mpr ⟨?_, hMasks⟩⟩
  · simp only [primingVHandoffFrame, primingVScratchAbi, List.cons_append, List.nil_append, Holds]
    repeat' apply And.intro
    all_goals first | trivial | exact holds_lookup hFrame rfl
  · exact ⟨holds_lookup hFrame rfl, holds_lookup hFrame rfl, holds_lookup hFrame rfl,
      holds_lookup hFrame rfl, holds_lookup hFrame rfl, trivial⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
