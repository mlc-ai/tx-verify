-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src

@[expose] public section

/-! # The correction warps' collective bound in `CorrPre`

`CorrPre` (`Ready.lean`) asks for the first-pass bound `collCount n ≤ cmax p` only at correction
states outside the rescale rounds (`Cr.round`) and the final stage (`Cr.tailOff`); at a state of
`preReady` those are first-pass states (`Cr.late = false`). This file gives that bound from the
correction warps' reference invariant (`CorrWarp.Ref`, which `CorrWarp.good` proves at every
followed state): the time table's sites outside the rounds and the final stage are outside the
pc ranges of the reference's rescale count (`cr_out`), so `CorrWarp.ccoll_le` applies. Written by
lane T1 next to lane T4's `Ready.lean`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A site outside the time table's rescale rounds and final stage is outside the reference's
round and tail pc ranges. -/
theorem cr_out (s : Correction.Site) (hr : Cr.round s = false) (ht : Cr.tailOff s = none) :
    Correction.inRound s.pc = false ∧ Correction.tailR s = false := by
  cases s <;> simp only [Cr.round, Cr.tailOff, reduceCtorEq, Bool.true_eq_false] at hr ht
  all_goals first
    | decide
    | (rename_i k; cases k <;> decide)
    | (rename_i k j; cases k <;> fin_cases j <;> decide)
    | (rename_i k; fin_cases k <;> decide)

/-- **The first-pass bound of `CorrPre`**: a correction state that holds the correction warps'
reference invariant with no undefined behaviour so far, outside the rescale rounds and the final
stage and in the first pass, is past at most `cmax p` warp collectives. -/
theorem corr_coll {w : Nat} (hp : Pre p L m) {d : Correction.Control.D} {n : Cls → Nat}
    (hR : CorrWarp.Ref p L w g (.inr ⟨.correction, d⟩, n)) (hub : n .ub = 0)
    (hr : Cr.round d.site = false) (ht : Cr.tailOff d.site = none) (hl : Cr.late d.site = false) :
    collCount n ≤ cmax p := by
  obtain ⟨-, hF⟩ := hR hub
  obtain ⟨h1, h2⟩ := cr_out d.site hr ht
  exact CorrWarp.ccoll_le hp hF h1 h2 hl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
