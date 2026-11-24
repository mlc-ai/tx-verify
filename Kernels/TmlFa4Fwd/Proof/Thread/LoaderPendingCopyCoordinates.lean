-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingDestination
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingEarlier
import Kernels.TmlFa4Fwd.Proof.LoaderCopyFootprint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvCopyVectorsApart)

/-- Each pending recurring copy identifies the physical vector and byte of its
logical use, independently of a later publication at that use. -/
theorem pendingCopyCoveredCoordinates {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy : EvId} {e : Event} (he : X.get copy = some e)
    (hVector : recurringVectorEvent e) {spec : Spec} (hKind : e.kind = .copy spec)
    {loc : Loc} (hCover : spec.dst.Covers loc) :
    ∃ (lane : Fin 64) (pair : Fin 16) (upper : Bool) (offset : Nat), offset < 16 ∧
      loc = ⟨.shared, copy.1 / l.block,
        kvCopyAddress l.sharedBase (kvUseStage (recurringUseBefore X copy)) lane pair upper +
          offset⟩ := by
  obtain ⟨g,index⟩ := copy
  have hCopy := actualCopyOfRecurringVector he hVector hKind
  obtain ⟨lane,hLane⟩ := copyProducer hp hX hCopy
  obtain ⟨pair,upper,hDst⟩ := pendingRecurringVectorDestination hp hX he hVector hKind
  dsimp only at hDst
  change g = producer l (g/l.block) lane at hLane
  have hMod : (g%l.block)%64 = lane.val := by rw [hLane,producerLaneMod hp]
  let slot := kvUseStage (recurringUseBefore X (g,index))
  have hAddress : kvCopyAddress l.sharedBase slot (g%l.block) pair upper =
      kvCopyAddress l.sharedBase slot lane pair upper := by
    simp only [kvCopyAddress, hMod, Nat.mod_eq_of_lt lane.isLt]
  change spec.dst = {loc := ⟨.shared,g/l.block,
    kvCopyAddress l.sharedBase slot (g%l.block) pair upper⟩, size := 16} at hDst
  rw [hAddress] at hDst
  obtain ⟨hSpace,hCta,hLo,hHi⟩ := hDst ▸ hCover
  let base := kvCopyAddress l.sharedBase slot lane pair upper
  change base ≤ loc.addr at hLo
  change loc.addr < base + 16 at hHi
  let offset := loc.addr - base
  refine ⟨lane,pair,upper,offset,by dsimp [offset]; omega,?_⟩
  have hAddr : loc.addr = base + offset := by dsimp [offset]; omega
  cases loc
  simp only [Loc.mk.injEq]
  exact ⟨hSpace,hCta,hAddr⟩

/-- Overlapping actual recurring vectors identify the same logical ring slot,
including when either producer still has an open copy group. -/
theorem pendingCopiesSameSlot {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {a b : EvId} {e f : Event} (he : X.get a = some e) (hf : X.get b = some f)
    (hA : recurringVectorEvent e) (hB : recurringVectorEvent f) {s t : Spec}
    (hs : e.kind = .copy s) (ht : f.kind = .copy t) {loc : Loc}
    (hCover : s.dst.Covers loc) (hOther : t.dst.Covers loc) :
    kvUseStage (recurringUseBefore X a) = kvUseStage (recurringUseBefore X b) := by
  obtain ⟨la,pa,ua,oa,hoa,ha⟩ := pendingCopyCoveredCoordinates hp hX he hA hs hCover
  obtain ⟨lb,pb,ub,ob,hob,hb⟩ := pendingCopyCoveredCoordinates hp hX hf hB ht hOther
  apply Fin.ext
  by_contra! hNe
  have hApart := kvCopyVectorsApart (a := la.val) (b := lb.val) (u := ua) (v := ub) hp.shared.1
    pa.isLt pb.isLt (.inl hNe)
  have hEq := congrArg Loc.addr (ha.symm.trans hb)
  change kvCopyAddress l.sharedBase (kvUseStage (recurringUseBefore X a)) la pa ua + oa =
    kvCopyAddress l.sharedBase (kvUseStage (recurringUseBefore X b)) lb pb ub + ob at hEq
  rcases hApart with h | h <;> omega

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
