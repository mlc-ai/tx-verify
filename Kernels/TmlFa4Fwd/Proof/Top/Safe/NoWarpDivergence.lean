-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Lemmas.Flow.PollSynced
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Poll
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Poll
import Kernels.TmlFa4Fwd.Proof.Loader.Export.Poll
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Poll
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Lands
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Poll

@[expose] public section

/-! # ERR-NONUNIFORM-GUARD: warp-collective guards are uniform

The safety class of Core's `Unsafe` this file owns, proved (`Safe.noWarpDivergence`): every lane-
compared instruction is a poll branch that `pollAgree` selects (`Softmax/Export/Lands.lean`), and
two lanes of a warp polling at one position poll one barrier or are ordered (`poll_synced`): the
softmax, correction and output warps' polls name one barrier per position and warp, the MMA warp's
are ordered by their elections, the loader's by their shuffles (`<Role>/Export/Poll.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **Two lanes of a warp polling at one position are ordered** unless they poll one barrier. -/
theorem poll_synced (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (hFw : Follow p l X) :
    PollSynced l kernel Assumptions.all X := by
  intro g h k k' pc mo mo' pr pr' ok ok' acq acq' sc sc' _ _ _ hs he he' hb hd
  have hne : mo ≠ mo' := by
    rcases hd with hd | hd
    · exact hd
    · rw [pollBranch_sel hb] at hd; cases hd
  have hw16 := Prologue.warpIndex_lt hp g
  by_cases h8 : Prologue.warpIndex l g < 8
  · exact absurd (soft_poll_same hp hX hFw h8 hs he he') hne
  by_cases h12 : Prologue.warpIndex l g ≤ 11
  · exact absurd (corr_poll_same hp hX hFw (by omega) h12 hs he he') hne
  by_cases h : Prologue.warpIndex l g = 12
  · exact (mma_poll_same hp hX hFw h hs he he').resolve_left hne
  by_cases h : Prologue.warpIndex l g = 13
  · exact absurd (out_poll_same hp hX hFw h hs he he') hne
  · exact (ld_poll_same hp hX hFw (by omega) hs he he').resolve_left hne

/-- **ERR-NONUNIFORM-GUARD.** -/
theorem Safe.noWarpDivergence (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) :
    ¬ WarpDivergent l kernel Assumptions.all X :=
  not_warpDivergent_synced pollGuards localLands (poll_synced hp hX (launchFollow hp hX))

end PTX.Kernels.TmlFa4Fwd.Proof.Top
