-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcCount
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The `tcgen05` events of a correction control state

A state's event is a warp-collective `tcgen05` event where its site has one (`corr_tcSite`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (nexts tw)

set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g : Nat} {e : Event}

set_option maxHeartbeats 2000000 in
/-- A state's event is a warp-collective `tcgen05` event where its site has one. -/
theorem corr_tcSite {d : Correction.Control.D} (hev : Correction.Control.Ev p L g d e)
    (hne : ∀ f, e.kind ≠ .ub f) : isTcColl e = decide (0 < tw d.site) := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hne
  cases s
  case rvote st =>
    obtain ⟨_, b, hk⟩ := hev
    simp only at hk
    subst hk
    rfl
  all_goals simp only [Correction.Control.Ev, Correction.Control.D.scheduler, Correction.Ev,
    Correction.rdOrUb, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals first
    | exact absurd rfl (hne _)
    | rfl

end PTX.Kernels.TmlFa4Fwd.Proof
