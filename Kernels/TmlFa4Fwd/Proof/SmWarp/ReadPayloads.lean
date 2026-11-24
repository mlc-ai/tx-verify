-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Expect
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Common.DataSound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX.Proof PTX.Flow Softmax
noncomputable section

/-- Only the sixteen four-word bias loads and the score loads read data of a prescribed kind. -/
def ReadPayload : Site → Kind → Prop
  | .bld _ _, .rd _ bs => ∃ v, rebuild 3 bs = .ok v ∧ biasOk v = true
  | .sld _ _, .tc (.ld _ vals _) => ∀ v ∈ vals, ∃ x, v = .float .f32 x
  | _, _ => True

def ReadPayloads (X : Execution) : Prop :=
  ∀ g k (s : Site) e, X.get (g,k) = some e → e.pc = s.pc → ReadPayload s e.kind

theorem expectRest_of_reads {p L m X g k d n e} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (h : ReadPayloads X)
    (he : X.get (g,k) = some e)
    (hst : Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.softmax,d⟩,n))) :
    ExpectRest p L g d e := by
  have hpc : e.pc = d.site.pc := Frame.event_pc (fun g hg => threadD_sound hp hg) hX he hst
  have hr := h g k d.site e he hpc
  obtain ⟨s,v,j,acc⟩ := d
  cases s with
  | bld _ _ =>
    intro a bs hk
    simpa only [hk, ReadPayload] using hr
  | sld _ _ =>
    intro a vals sh hk
    simpa only [hk, ReadPayload] using hr
  | _ => trivial

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
