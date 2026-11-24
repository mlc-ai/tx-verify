-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingAccessOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader

@[expose] public section

/-! # CTA-local index and raw buffer rings -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol

open PTX PTX.Flow PTX.MbarRing IndexRingThreads

/-- The lane elected by warp five is shared by index release and raw publication. -/
theorem selected_tma {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) :
    ∃ lane : Fin 32, IndexRing.TmaConsumer P L X cta lane ∧
      RawRing.Issuer P L X cta (cta * L.block + 160 + lane.val) := by
  obtain ⟨lane, h⟩ := Wg1TmaLeader.cta_issuer (cta := cta) hpre hX hs
  refine ⟨lane, ?_, ?_⟩
  · intro g i e d _ hc hd hst
    have hne : d.site ≠ .elect := by simp [hd]
    rw [h g i d hc hst hne]
    unfold laneOf
    rw [tidOf_eq hpre, hpre.block]
    have := lane.isLt
    omega
  · intro g i d hc hst hd
    apply h g i d hc hst
    rcases hd with hd | ⟨k, hd⟩
    all_goals simp [hd]

/-- The selected TMA lane and its CTA's four index rings. -/
structure CtaRings (P : Params) (L : Launch) (X : Execution) (cta : Nat) where
  lane : Fin 32
  rawIssuer : RawRing.Issuer P L X cta (cta * L.block + 160 + lane.val)
  index (slot : Fin 4) : Unit.Ring L kernel Assumptions.all X (IndexRing.ready L cta slot)
    (IndexRing.free L cta slot) 32 129 (producerThread L cta) (consumerThread L cta lane)

/-- The tracked execution supplies a selected lane and the index rings for its CTA. -/
noncomputable def ctaRings {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcta : cta < L.grid) (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) : CtaRings P L X cta :=
  let chosen := selected_tma (cta := cta) hpre hX hs
  { lane := Classical.choose chosen
    rawIssuer := (Classical.choose_spec chosen).2
    index := fun _ =>
      IndexRing.unit_ring_of_lane hpre hX hcta hs ht (Classical.choose_spec chosen).1 }

/-- The raw slot's exact ring uses the same elected TMA lane as the index rings. -/
noncomputable def CtaRings.raw {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} (R : CtaRings P L X cta) (slot : Fin 2)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    Items.Ring L kernel Assumptions.all X 1 128 1 (fun _ => 17) :=
  RawRing.items (slot := slot) _ hpre hX hs ht R.rawIssuer

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol
