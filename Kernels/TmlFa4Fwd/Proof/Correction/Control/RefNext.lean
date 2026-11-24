-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ref
import Kernels.TmlFa4Fwd.Proof.Correction.RefStep
import Kernels.TmlFa4Fwd.Proof.Correction.RefNext
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Representative

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event} {n : Cnt → Nat}

theorem ref_init : Ref p L g ((code p L g).init, fun _ => 0) :=
  Ref.of_data Correction.ref_init

/-- A strict step can use a representative data event when it has the same ledger effect. -/
private theorem transport {a : Correction.D} {e' : Event} (hJ : Ref p L g (d,n))
    (he : Correction.Ev p L g d.scheduler e') (hu : ∀ f, e'.kind ≠ .ub f)
    (hs : Correction.succ p L g d.scheduler e' = some (some a)) (hd : erase a = d')
    (hb : ∀ c, cls L g c e' = cls L g c e) :
    Ref p L g (d', Code.bump (cls L g) n e) := by
  obtain ⟨r,l,hr⟩ := hJ
  obtain ⟨r',l',h⟩ := counts_step hr he hu hs
  have hh : Code.bump (cls L g) n e' = Code.bump (cls L g) n e := by
    funext c
    simp only [Code.bump, hb]
  rw [hh] at h
  cases hd
  exact ⟨r',l',h.cnt,h.st,h.lse,h.sub,h.pre,h.loop,h.tail⟩

theorem ref_kept (hJ : Ref p L g (d,n)) (he : Ev p L g d e) (hu : ∀ f, e.kind ≠ .ub f)
    (hn : succ p L g d e = some (some d')) : Ref p L g (d', Code.bump (cls L g) n e) := by
  obtain ⟨a, ev, hev, hu', hs, hsite, hv, hk, hb, _⟩ :=
    represents hJ he hu hn
  exact transport hJ hev hu' hs (by cases d'; cases hsite; cases hv; cases hk; rfl) hb

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
