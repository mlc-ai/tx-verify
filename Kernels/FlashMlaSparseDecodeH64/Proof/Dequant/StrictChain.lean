-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.FollowD
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Gen.DataStepsS
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictGlue
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Lemmas.Kernel.StrictSite
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # The strict chain of a dequantizer lane

`dq_strict`: the data thread machine's state before an event of a lane of warps 8-11 is strictly
good (`Code.Good`) and fires the event from its site's template, with no fault alternative, when
the events before it are no undefined behaviour and the data they read is valid. The step before
it is strict for its event (`Frame.strict_site`): the startup's (`startup_steps`), or the data
machine's (`dataStepFor_all`), whose only event condition, that a scale element's bytes rebuild,
is the valid data (`DqValid`) the lane read. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Dequant
open Dequant.Data

/-- A valid scale or raw load's bytes rebuild. -/
theorem wfE_of_valid {k j : Nat} (hv : DqValid X g k) (hj : j < k) {e : Event}
    (he : X.get (g, j) = some e) {r : Nat} (hr : r < 4) (hpc : e.pc = dqScalePc r) : WfE e := by
  obtain ⟨-, hs⟩ := hv j hj e he
  obtain ⟨w, hw, -⟩ := hs r hr hpc
  intro x bs hk
  unfold readWord at hw
  rw [hk] at hw
  cases hb : rebuild 3 bs with
  | ok v => exact ⟨v, rfl⟩
  | error f => simp [hb, Except.toOption] at hw

/-- **The step before a state of a dequantizer lane is strict.** -/
theorem dq_prev (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12) {k j : Nat} (hj : j + 1 = k)
    {e : Event} (he : X.get (g, k) = some e) (hv : DqValid X g k)
    (hub : ∀ (f : Fault) (ej : Event), X.get (g, j) = some ej → ej.kind ≠ .ub f)
    {dj σ : (threadD P L g).D} {ej : Event} (hej : (X.tr g)[j]? = some ej)
    (hdj : Frame.stateAt (threadD P L) X g j = some (some dj))
    (hn : (threadD P L g).next dj ej = some (some σ)) : (threadD P L g).StepFor dj ej := by
  have hg := Frame.lt_of_get hX he
  rcases deq_slot hFw hw hg hdj with ⟨b, hb⟩ | ⟨dd, hdd⟩
  · obtain ⟨q, n⟩ := dj
    obtain rfl : q = .inl b := hb
    refine fun {t u} ins hat hi hc hf => (Code.counted_stepFor (Code.glue_inl_stepFor
      (fun hx => (startup_steps hp b hx).stepFor ej) threadD_handoff) n) ins hat hi hc hf
  · obtain ⟨q, n⟩ := dj
    obtain rfl : q = .inr ⟨.inl .dequant, dd⟩ := hdd
    have hget : X.get (g, j) = some ej := hej
    have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
    have hfu : ∀ f, ej.kind ≠ .ub f := fun f => hub f ej hget
    have hpc := Frame.event_pcU hsD hX hget hdj hfu
    have hstep : (dequantDCode P L g (warpW L g)).StepFor dd ej := by
      apply dataStepFor_all (w := warpW L g) hp dd ej
      rintro ⟨r, hr⟩
      have hpc' : ej.pc = dqScalePc r.val := by
        rw [hpc, ← scale_pc r]
        show dd.c.site.pc = _
        rw [hr]
      exact wfE_of_valid hv (by omega) hget r.isLt hpc'
    refine fun {t u} ins hat hi hc hf => (Code.counted_stepFor
      (Code.glue_inr_stepFor (i := Sum.inl Entry.dequant) hstep) n) ins hat hi hc hf

end Dequant

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
