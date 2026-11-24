-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualIndexPool
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadyDescent

@[expose] public section

/-! # A concrete softmax release depends on a late index publication -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A softmax release above the given slot use requires a causally earlier publication
from an index producer above the same use. -/
theorem actual_softmax_depends_on_later_producer {g i start block n : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hStart : start ≤ i)
    (hAnchor : FirstMaskAnchor P L X g start) (hTag : e.pc = Wg0.Site.validFree.pc)
    (hBlock : block = (((X.tr g).drop start).take (i - start)).countP isProbabilityPublication)
    (hLater : n < block / 4) :
    ∃ (h j : Nat) (f : Event) (z : Wg1Index.D) (extra : Bool),
      X.get (h, j) = some f ∧ Frame.stateAt (Machine.code P L) X h j = some (some (.index z)) ∧
      ctaOf L h = ctaOf L g ∧ z.block % 4 = block % 4 ∧ z.site = .ready extra ∧
      n < z.block / 4 ∧ baseCausality L X (h, j) (g, i) := by
  let slot := indexSlot block
  let m := ready L (ctaOf L g) slot
  have hUse : 4 * (n + 1) + slot.val ≤
      (((X.tr g).drop start).take (i - start)).countP isProbabilityPublication := by
    rw [← hBlock]
    change 4 * (n + 1) + block % 4 ≤ block
    omega
  obtain ⟨uses, hOrdered, hUses⟩ :=
    actual_softmax_phase_uses hpre hX hs he hStart hAnchor hTag hUse
  let waits (a : Fin (n + 1 + 1)) : IndexPhaseWait X m g i 32 := by
    let u := uses a
    have hslot : indexSlot (4 * a.val + slot.val) = slot := by
      apply Fin.ext
      change (4 * a.val + slot.val) % 4 = slot.val
      have := slot.isLt
      omega
    have hParity : (4 * a.val + slot.val) / 4 % 2 = a.val % 2 := by have := slot.isLt; omega
    have hPoll := u.visit.getPoll
    rw [hslot, hParity] at hPoll
    have hp : 0 < u.phase.before.phase := by
      change 0 < (uses a).phase.before.phase
      have := (hUses a).1
      omega
    refine ⟨u.visit.pollPos, 264, a.val % 2, (hUses a).2, hPoll, u.phase.pos, u.phase.record,
      u.phase.before, u.phase.get, u.phase.source, u.phase.clean, u.phase.waited, u.phase.state,
      u.phase.expected, hp, ?_⟩
    change observedAt (X.objects (ready L (ctaOf L g) slot)) u.phase.pos = _
    simp only [observedAt, u.phase.get, Option.bind_some, u.phase.completion, ite_eq_left hp]
  obtain ⟨positions, hCard, hOrigins⟩ :=
    actual_index_phase_pool hpre hX hs (.inl rfl : m = ready L (ctaOf L g) slot ∨
      m = free L (ctaOf L g) slot) he waits hOrdered
  apply later_producer_of_ready_pool hpre hX hs hCard
  intro k hk
  obtain ⟨r, h, j, tag, hr, hid, hGet, hOrder⟩ := hOrigins k hk
  obtain ⟨⟨hc, z, hSlot, ⟨extra, hSite⟩, hz⟩, _⟩ :=
    actual_index_ready_arrive hpre hX hs hGet rfl
  exact ⟨r, h, j, _, z, extra, hr, hid, hc, hSlot, hSite, hGet, hz, hOrder⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
