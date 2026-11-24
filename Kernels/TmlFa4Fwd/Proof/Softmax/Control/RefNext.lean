-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Ref
public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Shape
import Kernels.TmlFa4Fwd.Proof.Softmax.RefStep
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Representative

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow
noncomputable section

variable {p : Params} {L : Launch} {g : Nat} {m : Mem0} {d d' : D} {e : Event} {n : Cnt → Nat}

/-- Only the site, substep and control words contribute to the reference counts. -/
private theorem transport (hp : Pre p L m) (hJ : Ref p L g (d,n)) {a : Softmax.D} {ev : Event}
    (he : Softmax.Ev p L g d.scheduler ev) (hu : ∀ f, ev.kind ≠ .ub f)
    (hs : Softmax.succ p L g d.scheduler ev = some (some a))
    (hsite : a.site = d'.site) (hv : (erase a).v = d'.v) (hk : a.k = d'.k)
    (hb : ∀ c, cls L g c ev = cls L g c e) :
    Ref p L g (d', Code.bump (cls L g) n e) := by
  obtain ⟨⟨r,l,hr⟩⟩ := hJ
  obtain ⟨r',l',h⟩ := counts_step hp hr he hu hs
  have hh : Code.bump (cls L g) n ev = Code.bump (cls L g) n e := by
    funext c
    simp only [Code.bump, hb]
  rw [hh] at h
  obtain ⟨s,v,k,acc⟩ := d'
  cases hsite
  cases hv
  cases hk
  exact ⟨⟨r',l',h.cnt,h.elect,h.barr,h.pre,h.bias,h.plain,h.after,h.fin,h.noTile,h.wait⟩⟩

theorem ref_kept (hp : Pre p L m) (hJ : Ref p L g (d,n)) (he : Ev p L g d e)
    (hu : ∀ f, e.kind ≠ .ub f) (hn : succ p L g d e = some (some d')) :
    Ref p L g (d', Code.bump (cls L g) n e) := by
  obtain ⟨a, ev, hev, hu', hs, hsite, hv, hk, hb, _⟩ :=
    represents hp hJ he hu hn
  exact transport hp hJ hev hu' hs hsite hv hk hb

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
