-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingPacketGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
import Kernels.TmlFa4Fwd.Proof.LoaderCopyFootprint
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX
open PTX.Kernels.TmlFa4Fwd.Loader

/-- Every actual copy, including a pending member of an open group, has the
destination of one full vector in its lane's cache ring. -/
theorem copyDestination {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {spec : AsyncCopy.Spec} (hCopy : X.Copy i spec) :
    i.1 < l.threads ∧ ∃ (slot : Fin 3) (pair : Fin 16) (upper : Bool),
      spec.dst = {loc := ⟨.shared, i.1 / l.block,
        kvCopyAddress l.sharedBase slot (i.1 % l.block) pair upper⟩, size := 16} := by
  obtain ⟨g, j⟩ := i
  obtain ⟨pc, hGet⟩ := hCopy
  obtain ⟨hLo, hHi, hOrdinary⟩ := actualCopyAtInLoader hX hGet
  obtain ⟨site, hBegin, hEnd⟩ := loaderCopyPcInPacket hLo hHi hOrdinary
  obtain ⟨pair, upper, rfl⟩ := packetCopyCoordinates site hBegin hEnd hOrdinary
  obtain ⟨slot, hDst⟩ := actualCopyPrefixDestination hp hX site pair upper hGet
  exact ⟨PTX.Proof.event_thread_lt hX hGet, slot, pair, upper, hDst⟩

/-- The producer's logical lane is its position in the two loader warps. -/
theorem producerLaneMod {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (owner : Nat) (lane : Fin 64) :
    (producer l owner lane % l.block) % 64 = lane.val := by
  have := lane.isLt
  unfold producer readyProducer
  rw [hp.block]
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {a b : EvId} {owner : Nat} {slot : Fin 3}
include hp hX

/-- Copies from two actual publications to the same slot can share a byte
only when they come from the same physical loader lane and vector position. -/
theorem copiesSharingSlotByteSameIssuer (ga : PublishedCopyGroup l X a)
    (gb : PublishedCopyGroup l X b) (ha : X.AsyncArrive a (readyObject l owner slot) true)
    (hb : X.AsyncArrive b (readyObject l owner slot) true) {i j : Nat} {sa sb : AsyncCopy.Spec}
    {loc : Loc} (hai : (i, sa) ∈ ga.copies) (hbj : (j, sb) ∈ gb.copies) (hca : sa.dst.Covers loc)
    (hcb : sb.dst.Covers loc) :
    a.1 = b.1 ∧ sa.dst = sb.dst := by
  obtain ⟨pairA, upperA, hA⟩ := ga.destination hp hX ha hai
  obtain ⟨pairB, upperB, hB⟩ := gb.destination hp hX hb hbj
  have hSlotA := ga.slotFor hp hX ha
  have hSlotB := gb.slotFor hp hX hb
  obtain ⟨_, hGetA⟩ := ha
  obtain ⟨_, hGetB⟩ := hb
  obtain ⟨laneA, hLaneA⟩ := readyArrivalProducer hp hX slot hGetA
  obtain ⟨laneB, hLaneB⟩ := readyArrivalProducer hp hX slot hGetB
  dsimp only at hA hB
  rw [hSlotA] at hA
  rw [hSlotB] at hB
  have noDiff : ¬ ((a.1 % l.block) % 64 ≠ (b.1 % l.block) % 64 ∨
      pairA.val ≠ pairB.val ∨ upperA ≠ upperB) := by
    intro hDiff
    have hApart := kvCopyVectorsApart hp.shared.1 (k := slot.val) (s := slot.val)
      pairA.isLt pairB.isLt (.inr hDiff)
    rw [hA] at hca
    rw [hB] at hcb
    obtain ⟨_, _, hLoA, hHiA⟩ := hca
    obtain ⟨_, _, hLoB, hHiB⟩ := hcb
    change kvCopyAddress l.sharedBase slot (a.1 % l.block) pairA upperA ≤ loc.addr at hLoA
    change loc.addr < kvCopyAddress l.sharedBase slot (a.1 % l.block) pairA upperA + 16 at hHiA
    change kvCopyAddress l.sharedBase slot (b.1 % l.block) pairB upperB ≤ loc.addr at hLoB
    change loc.addr < kvCopyAddress l.sharedBase slot (b.1 % l.block) pairB upperB + 16 at hHiB
    omega
  push Not at noDiff
  obtain ⟨hLane, hPair, hUpper⟩ := noDiff
  have hLanes : laneA = laneB := Fin.ext (by
    rwa [hLaneA, hLaneB, producerLaneMod hp, producerLaneMod hp] at hLane)
  have hIssuer : a.1 = b.1 := hLaneA.trans (hLanes ▸ hLaneB.symm)
  obtain rfl := Fin.ext hPair
  exact ⟨hIssuer, by rw [hA, hB, hIssuer, hUpper]⟩

/-- A single loader lane has only one publication of a given generation on
a physical ready slot. The ordinals are those of the abstract role history. -/
theorem publicationUniqueAtSlot (ha : X.AsyncArrive a (readyObject l owner slot) true)
    (hb : X.AsyncArrive b (readyObject l owner slot) true) (hIssuer : a.1 = b.1)
    (hRank : (atPrefix l X a.1 a.2).published.countP (fun pub => pub.slot == slot) =
      (atPrefix l X b.1 b.2).published.countP (fun pub => pub.slot == slot)) :
    a = b := by
  have hOrdinal := (publicationOrdinalAtObject hp hX ha).symm.trans
    (hRank.trans (publicationOrdinalAtObject hp hX hb))
  obtain ⟨g, i⟩ := a
  obtain ⟨g', j⟩ := b
  change g = g' at hIssuer
  subst g'
  obtain ⟨_, hGetA⟩ := ha
  obtain ⟨_, hGetB⟩ := hb
  have hIndex := readyOrdinalUnique hGetA hGetB hOrdinal
  exact Prod.ext rfl hIndex

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
