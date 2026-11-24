-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Common.DataState
import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX.Flow Softmax

theorem data_event {p L m X g k e d n} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hd : DataStoreSafe p L g)
    (he : X.get (g,k) = some e)
    (hσ : Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.softmax,d⟩,n))) :
    EvS p L g d e ∧ (codeT p L g).inv d := by
  obtain ⟨_, _, _, hat, hi, hc, hf⟩ :=
    Frame.fired_site (fun _ hg => threadD_sound hp hg) hX he hσ
  exact ⟨shapeS hp hd hat hi.1 hc hf, hi⟩

theorem data_ref {p L g d c} (h : Control.Ref p L g (Control.erase d,c)) :
    Softmax.Ref p L g (d,c) := by
  obtain ⟨⟨rb,rp,h⟩⟩ := h
  exact ⟨⟨rb,rp,h.cnt,h.elect,h.barr,h.pre,h.bias,h.plain,h.after,h.fin,h.noTile,h.wait⟩⟩

end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
