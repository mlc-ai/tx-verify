-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Common.DataSound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX.Proof PTX.Flow Correction
noncomputable section

/-- The payload condition at the five families of correction data reads. -/
def ReadPayload : Site → Kind → Prop
  | .rscale _, .rd _ bs => ∃ s : Sc, rebuild 3 bs = .ok s.val
  | .fmax _, .rd _ bs => ∃ x : EReal, x ≠ ⊤ ∧
    rebuild 3 bs = .ok (Assumption.erealValue .f32 x)
  | .fsum _, .rd _ bs => ∃ x, rebuild 3 bs = .ok (fv x) ∧ 0 ≤ x
  | .rld _ _, .tc (.ld _ vals _) => (flN 16 vals).isSome
  | .fld _ _, .tc (.ld _ vals _) => (flN 8 vals).isSome
  | _, _ => True

/-- A trace condition on read results. The program counters uniquely identify these kernel
instructions even before the lane is known to follow its role. -/
def ReadPayloads (X : Execution) : Prop :=
  ∀ g k (s : Site) e, X.get (g,k) = some e → e.pc = s.pc → ReadPayload s e.kind

theorem dataSrc_of_reads {p L m X} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (h : ReadPayloads X) : DataSrc p L X := by
  intro g k d n e he hst _ hd
  have hpc : e.pc = d.site.pc := Frame.event_pc (fun g hg => threadD_sound hp hg) hX he hst
  have hr := h g k d.site e he hpc
  obtain ⟨s,v,j⟩ := d
  cases s with
  | rscale _ | fsum _ | fmax _ =>
    intro a bs hk
    simpa only [hk, ReadPayload] using hr
  | rld _ _ | fld _ _ =>
    intro a vals sh hk
    simpa only [hk, ReadPayload] using hr
  | _ => cases hd

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
