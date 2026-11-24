-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualQkBlock
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

@[expose] public section

/-! # Causal tracking at an actual softmax mask read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow Protocol GemmRing

/-- The mask-read guard follows from actual QK results and the causally prior mask writes. -/
theorem mask_next_tracked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maskRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  have hg := Frame.lt_of_get hX he
  have hRole : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  let cta := ctaOf L g
  obtain ⟨lane, hLane⟩ := softmax_thread hpre (cta := cta) rfl hRole
  obtain ⟨issuer, hIssuer⟩ := exists_issuer (cta := cta) hpre hX (fun h hh => (hs h hh).machine)
  rw [hLane] at he hd hPrior ⊢
  have hLen := (PTX.len_of_get he).le
  have hValues := Result.qk_values_of_mask hpre hX hs hIssuer hd hsite hLen
  exact MaskReadback.next_of_actual_scores hpre hX hs he hd hsite hPrior
    (ScoreMaskStep.exchange_ready_of_qk_values hpre hX hs hIssuer hd hsite hLen hValues)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
