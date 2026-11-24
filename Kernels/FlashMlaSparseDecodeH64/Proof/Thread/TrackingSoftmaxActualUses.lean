-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxActualPhase

@[expose] public section

/-! # A concrete softmax return has observed a phase for every use of its slot -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- A concrete visit and the phase record for its matching mask acquire. -/
structure ActualSoftmaxPhaseUse (L : Launch) (X : Execution) (g start : Nat) (slot : Fin 4)
    (use : Nat) where
  visit : ActualSoftmaxVisit L X g start (4 * use + slot.val)
  phase : ActualMaskPhase X (ready L (ctaOf L g) slot) g visit.pollPos (use % 2)

/-- All slot uses through this concrete return contribute different noninitial phases. -/
theorem actual_softmax_phase_uses {start i : Nat} {e : Event} {slot : Fin 4} {n : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hStart : start ≤ i)
    (hAnchor : FirstMaskAnchor P L X g start) (hTag : e.pc = Wg0.Site.validFree.pc)
    (hUse : 4 * n + slot.val ≤
      (((X.tr g).drop start).take (i - start)).countP isProbabilityPublication) :
    ∃ uses : (a : Fin (n + 1)) → ActualSoftmaxPhaseUse L X g start slot a,
      StrictMono (fun a => (uses a).phase.before.phase) ∧
      ∀ a, a.val + 1 ≤ (uses a).phase.before.phase ∧ (uses a).visit.pollPos < i := by
  classical
  have existsUse (a : Fin (n + 1)) : Nonempty (ActualSoftmaxPhaseUse L X g start slot a) := by
    obtain ⟨v⟩ := actual_softmax_visits hpre hX hs he hStart hAnchor hTag
      (4 * a.val + slot.val) (by have := a.isLt; omega)
    have hSlot : indexSlot (4 * a.val + slot.val) = slot := by
      apply Fin.ext
      change (4 * a.val + slot.val) % 4 = slot.val
      have := slot.isLt
      omega
    have hParity : (4 * a.val + slot.val) / 4 % 2 = a.val % 2 := by have := slot.isLt; omega
    have hw := v.getPoll
    rw [hSlot, hParity] at hw
    obtain ⟨phase⟩ := actual_mask_phase hpre hX hs hAnchor v.pollFromStart hw
    exact ⟨⟨v, phase⟩⟩
  let uses (a : Fin (n + 1)) := (existsUse a).some
  have hSeq : StrictMono (fun a => (uses a).phase.before.phase) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro a
    have hLt : 4 * a.castSucc.val + slot.val < 4 * a.succ.val + slot.val := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    have hBefore := (uses a.castSucc).visit.poll_lt hX hLt (uses a.succ).visit
    exact (uses a.castSucc).phase.phase_lt hX hBefore (uses a.succ).phase
  have hNoninitial : 1 ≤ (uses 0).phase.before.phase := by
    have hp := (uses 0).phase.nextParity
    change (uses 0).phase.before.phase % 2 ≠ 0 at hp
    omega
  have hLower (a : Fin (n + 1)) : a.val + 1 ≤ (uses a).phase.before.phase := by
    induction a using Fin.induction with
    | zero => exact hNoninitial
    | succ a ih =>
      have h := hSeq (show a.castSucc < a.succ from Fin.castSucc_lt_succ)
      change (uses a.castSucc).phase.before.phase < (uses a.succ).phase.before.phase at h
      change a.val + 1 ≤ (uses a.castSucc).phase.before.phase at ih
      change a.val + 1 + 1 ≤ (uses a.succ).phase.before.phase
      omega
  refine ⟨uses, hSeq, fun a => ⟨hLower a, (uses a).visit.pollBefore.trans_le ?_⟩⟩
  by_contra! hAfter
  have hCount := actual_softmax_return_count_lt hX he (uses a).visit.getRelease
    hTag (uses a).visit.releaseSite hStart hAfter
  rw [← (uses a).visit.ordinal] at hCount
  have := a.isLt
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
