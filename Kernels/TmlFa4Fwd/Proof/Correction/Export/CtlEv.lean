-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Shape

@[expose] public section

/-! # The event shapes of a correction control state -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {g : Nat}

/-- A control state's event of no ballot is of the role's shape. -/
theorem corr_ctl_ev {d : Correction.Control.D} {e : Event} (hev : Correction.Control.Ev p L g d e)
    (hv : ∀ m a b, e.kind ≠ .vote m a b) : Correction.Ev p L g d.scheduler e := by
  obtain ⟨site, v, kk⟩ := d
  cases site <;> first
    | exact hev
    | (obtain ⟨_, _, hk⟩ := hev; exact absurd hk (hv _ _ _))

/-- A control state at no rescale ballot has events of the role's shape. -/
theorem corr_ctl_ev_site {d : Correction.Control.D} {e : Event}
    (hev : Correction.Control.Ev p L g d e) (hv : ∀ st, d.site ≠ .rvote st) :
    Correction.Ev p L g d.scheduler e := by
  obtain ⟨site, v, kk⟩ := d
  cases site <;> first | exact hev | exact absurd rfl (hv _)

end PTX.Kernels.TmlFa4Fwd.Proof
