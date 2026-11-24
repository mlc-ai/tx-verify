-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SelectedCacheCopyUse
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActualCacheUseBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (packetPlanePc recurringPacketSite kCopyPc vCopyPc kvUseStage)

private theorem recurringVectorPcLower (site : Fin 4) (pair : Fin 16) (upper : Bool) :
    917 ≤ packetPlanePc (recurringPacketSite site) pair upper := by
  revert site pair upper
  decide +kernel

private theorem primingVectorPcBefore (pair : Fin 16) (upper : Bool) :
    kCopyPc pair + (if upper then 1 else 0) < 917 ∧
    vCopyPc pair + (if upper then 1 else 0) < 917 := by
  revert pair upper
  decide +kernel

/-- The actual selected loader packet's rank lies inside the visited KV range
of the request chosen by the publishing CTA. -/
theorem PublishedCopyGroup.recurringUseBound {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {pub : EvId} (group : PublishedCopyGroup l X pub)
    {owner use : Nat} (hPub : X.AsyncArrive pub (readyObject l owner (kvUseStage use)) true)
    (hPhase : (atPrefix l X pub.1 pub.2).published.countP
      (fun q => q.slot == kvUseStage use) = use/3)
    (hRecurring : 2 ≤ use) {j : Nat} {spec : AsyncCopy.Spec}
    (hMember : (j,spec) ∈ group.copies)
    {batch : Nat} (hLo : tilePrefix p batch*p.heads ≤ pub.1/l.block)
    (hHi : pub.1/l.block < tilePrefix p (batch+1)*p.heads) :
    use < 2 * Mma.trips p batch (assignedCoordinates p batch (pub.1/l.block)).1 := by
  obtain ⟨hUse,e,he,⟨site,pair,upper,src,rfl⟩,_⟩ :=
    group.recurringMemberAtUse hp hX hPub hPhase hRecurring hMember
  have hpSite := recurringVectorPcLower site pair upper
  have hCopy := ((group.member j spec).mp hMember).2.2
  have hKey (col : Fin 16) (hi : Bool) : ¬ PrimingKeyVector X (pub.1,j) col hi spec := by
    intro h
    have hEqual := congrArg Event.pc (Option.some.inj (he.symm.trans h))
    change packetPlanePc (recurringPacketSite site) pair upper =
      kCopyPc col + (if hi then 1 else 0) at hEqual
    have := (primingVectorPcBefore col hi).1
    omega
  have hValue (col : Fin 16) (hi : Bool) : ¬ PrimingValueVector X (pub.1,j) col hi spec := by
    intro h
    have hEqual := congrArg Event.pc (Option.some.inj (he.symm.trans h))
    change packetPlanePc (recurringPacketSite site) pair upper =
      vCopyPc col + (if hi then 1 else 0) at hEqual
    have := (primingVectorPcBefore col hi).2
    omega
  obtain ⟨actual,_,hL,hH,hBound⟩ := recurringCopyUseBound hp hX hFrame hCopy hKey hValue
  change tilePrefix p actual*p.heads ≤ pub.1/l.block at hL
  change pub.1/l.block < tilePrefix p (actual+1)*p.heads at hH
  have hBatch : actual = batch := by
    rcases lt_trichotomy actual batch with h | rfl | h
    · exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_right p.heads
        (tilePrefix_mono p (show actual+1 ≤ batch by omega))).trans hLo)).elim hH
    · rfl
    · exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_right p.heads
        (tilePrefix_mono p (show batch+1 ≤ actual by omega))).trans hL)).elim hHi
  subst actual
  simpa only [hUse] using hBound

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
