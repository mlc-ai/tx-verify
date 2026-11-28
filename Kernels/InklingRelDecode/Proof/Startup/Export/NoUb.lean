-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Kernels.InklingRelDecode.Proof.Common.LaneNoUb
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.Sound
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # No undefined behaviour while a thread is in the startup

A thread whose events up to and including the one at hand are all at pcs below 27 (the startup's
code) has no undefined behaviour there (`noUb_early`). The lane's first undefined-behaviour event
(`Frame.noUb_strict_lane`) would fire from a state of the startup, strictly good because the
startup's steps are strict, and the startup's templates are not undefined behaviour
(`safe_site`); the startup dies only on the base word's load, which `BaseRead` excludes
(`live_site`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Startup.Export
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode
open PTX.Kernels.InklingRelDecode.Proof

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A thread whose events up to and including this one are the startup's has no undefined
behaviour here.** -/
theorem noUb_early (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e)
    (early : ∀ j ≤ k, ∀ e', X.get (g, j) = some e' → e'.pc < 27) (f : Fault) :
    e.kind ≠ .ub f := by
  have nu := Frame.noUbBefore_of_get hX he
  refine lane_noUb hp hX hf base hg he (Rest := fun _ => False) ?_ ?_ (fun _ _ _ h => h.elim)
    (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim) f
  case refine_2 =>
    intro σ _ hpc
    exact Or.inl ((state_role σ).startup (by rw [← hpc]; exact early k le_rfl e he))
  intro j d hj hd
  left
  have hk' : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hj' : j < (X.tr g).length := by omega
  obtain ⟨ej, hej⟩ : ∃ ej, X.get (g, j) = some ej := ⟨_, List.getElem?_eq_getElem hj'⟩
  have hu : ∀ f, ej.kind ≠ .ub f := fun f => nu j hj ej hej f
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX hej hd hu
  have lt := early j hj.le ej hej
  exact (state_role d).startup (by rw [← pc]; exact lt)

end
end PTX.Kernels.InklingRelDecode.Proof.Startup.Export
