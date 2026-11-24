-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingKeyPrefix
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingValuePrefix
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderCopyFootprint
import Kernels.TmlFa4Fwd.Proof.Thread.SelectedCacheCopyUse
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader
  (primingPacketSite packetPlanePc copyCommitPc actualAsyncArrival loaderStartupAsyncAddress
    readySlot readySlot_address loaderPipelineCutOp kCopyPc vCopyPc kvCopyVectorsApart)

/-- A priming key or value copy together with its physical initial slot. -/
def PrimingCacheVector (X : Execution) (copy : EvId) (stage : Fin 2)
    (pair : Fin 16) (upper : Bool) (spec : AsyncCopy.Spec) : Prop :=
  if stage = 0 then PrimingKeyVector X copy pair upper spec
  else PrimingValueVector X copy pair upper spec

/-- The initial K packet is issued to slot zero. -/
theorem PrimingKeyVector.primingCacheVector {X : Execution} {copy : EvId}
    {pair : Fin 16} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : PrimingKeyVector X copy pair upper spec) : PrimingCacheVector X copy 0 pair upper spec :=
  by simpa [PrimingCacheVector] using h

/-- The initial V packet is issued to slot one. -/
theorem PrimingValueVector.primingCacheVector {X : Execution} {copy : EvId}
    {pair : Fin 16} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : PrimingValueVector X copy pair upper spec) :
    PrimingCacheVector X copy 1 pair upper spec :=
  by simpa [PrimingCacheVector] using h

private theorem PrimingCacheVector.decoded {X : Execution} {copy : EvId} {stage : Fin 2}
    {pair : Fin 16} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : PrimingCacheVector X copy stage pair upper spec) :
    X.get copy = some ⟨packetPlanePc (primingPacketSite stage) pair upper,.copy spec⟩ := by
  fin_cases stage
  · have hSite : packetPlanePc (primingPacketSite 0) pair upper =
        kCopyPc pair + (if upper then 1 else 0) := by
      fin_cases pair <;> cases upper <;> decide
    have hGet : PrimingKeyVector X copy pair upper spec := h
    exact (congrArg (fun pc => some (Event.mk pc (.copy spec))) hSite).symm ▸ hGet
  · have hSite : packetPlanePc (primingPacketSite 1) pair upper =
        vCopyPc pair + (if upper then 1 else 0) := by
      fin_cases pair <;> cases upper <;> decide
    have hGet : PrimingValueVector X copy pair upper spec := h
    exact (congrArg (fun pc => some (Event.mk pc (.copy spec))) hSite).symm ▸ hGet

/-- The indexed priming occurrence is a real cp.async issue. -/
theorem PrimingCacheVector.copy {X : Execution} {issue : EvId} {stage : Fin 2}
    {pair : Fin 16} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : PrimingCacheVector X issue stage pair upper spec) : X.Copy issue spec :=
  ⟨_,h.decoded⟩

/-- The two initial packets use their fixed physical slots. -/
theorem PrimingCacheVector.destination {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy : EvId} {stage : Fin 2} {pair : Fin 16} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : PrimingCacheVector X copy stage pair upper spec) :
    spec.dst = {loc := ⟨.shared,copy.1/l.block,
      kvCopyAddress l.sharedBase stage.val (copy.1%l.block) pair upper⟩, size := 16} := by
  fin_cases stage
  · exact PrimingKeyVector.initialKeyDestination hp hX h
  · exact PrimingValueVector.initialValueDestination hp hX h

/-- Overlapping initial cache vectors identify one occurrence on a single loader lane. -/
theorem overlappingPrimingCopiesEq {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {a b : EvId} {sa sb : Fin 2} {pa pb : Fin 16} {ua ub : Bool} {s t : AsyncCopy.Spec}
    (ha : PrimingCacheVector X a sa pa ua s) (hb : PrimingCacheVector X b sb pb ub t)
    {loc : Loc} (hs : s.dst.Covers loc) (ht : t.dst.Covers loc) : a = b := by
  have hLane := (overlappingCopiesSameDestination hp hX ha.copy hb.copy hs ht).1
  obtain ⟨g,i⟩ := a
  obtain ⟨g',j⟩ := b
  change g = g' at hLane
  subst g'
  have hA := ha.destination hp hX ▸ hs
  have hB := hb.destination hp hX ▸ ht
  let first := kvCopyAddress l.sharedBase sa.val (g%l.block) pa ua
  let second := kvCopyAddress l.sharedBase sb.val (g%l.block) pb ub
  have hFirstLo : first ≤ loc.addr := hA.2.2.1
  have hFirstHi : loc.addr < first+16 := hA.2.2.2
  have hSecondLo : second ≤ loc.addr := hB.2.2.1
  have hSecondHi : loc.addr < second+16 := hB.2.2.2
  have hSlotEq : sa.val = sb.val ∧ pa.val = pb.val ∧ ua = ub := by
    by_contra hEqual
    have hDiff : sa.val ≠ sb.val ∨ pa.val ≠ pb.val ∨ ua ≠ ub := by
      by_contra! hNone
      exact hEqual hNone
    have hApart := kvCopyVectorsApart (a := g%l.block) (b := g%l.block) hp.shared.1
      pa.isLt pb.isLt (hDiff.imp_right Or.inr)
    change first+16 ≤ second ∨ second+16 ≤ first at hApart
    rcases hApart with h | h <;> omega
  obtain ⟨hSlot,hPair,rfl⟩ := hSlotEq
  obtain rfl : sa = sb := Fin.ext hSlot
  obtain rfl : pa = pb := Fin.ext hPair
  have hSite : (550 ≤ packetPlanePc (primingPacketSite sa) pa ua ∧
      packetPlanePc (primingPacketSite sa) pa ua ≤ 672) ∨
      (810 ≤ packetPlanePc (primingPacketSite sa) pa ua ∧
        packetPlanePc (primingPacketSite sa) pa ua ≤ 902) := by
    fin_cases sa <;> fin_cases pa <;> cases ua <;> decide
  exact Prod.ext rfl (uniquePrimingCopy hp hX (copyLoaderWarp hp hX ha.copy)
    hSite ha.decoded hb.decoded)

private theorem primingArrivalCut (stage : Fin 2) (bound : Nat) :
    let cut := copyCommitPc (primingPacketSite stage)+1
    ((kernel.code.drop cut).take (1901-cut)).all
      (fun ins => loaderPipelineCutOp cut 1901 bound [2535,1062] ins.op) = true := by
  fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl

/-- A same-lane publication on the priming copy's slot always follows that
copy, including when the consumer acquires any later generation. -/
theorem PrimingCacheVector.beforeSameSlotPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy publication : EvId} {owner : Nat} {stage : Fin 2} {pair : Fin 16}
    {upper : Bool} {spec : AsyncCopy.Spec}
    (hCopy : PrimingCacheVector X copy stage pair upper spec)
    (hLane : copy.1 = publication.1)
    (hPub : X.AsyncArrive publication (readyObject l owner ⟨stage.val,by
      have := stage.isLt
      omega⟩) true) :
    TraceBefore X copy publication := by
  obtain ⟨g,i⟩ := copy
  obtain ⟨g',j⟩ := publication
  change g = g' at hLane
  subst g'
  obtain ⟨pc,hGet⟩ := hPub
  obtain ⟨⟨site,hSite⟩,_,_,_⟩ := actualAsyncArrival hX hGet
  let cut := copyCommitPc (primingPacketSite stage)+1
  have hLower : cut ≤ pc := by
    rw [hSite]
    fin_cases stage <;> fin_cases site <;> try decide
    have hAddr := congrArg Loc.addr
      (loaderStartupAsyncAddress hp hX hGet (hSite.symm ▸ (by decide : 674 ∈ [674,904])))
    simp only [hSite, readyObject, readySlot_address] at hAddr
    have hBad : l.sharedBase + 8 + 32 = l.sharedBase + 32 := hAddr
    omega
  have hBounds : 173 < packetPlanePc (primingPacketSite stage) pair upper ∧
      packetPlanePc (primingPacketSite stage) pair upper < cut := by
    fin_cases stage <;> fin_cases pair <;> cases upper <;> decide
  have hCut : 174 ≤ cut ∧ cut ≤ 1901 := by fin_cases stage <;> decide
  refine ⟨rfl,?_ ,len_of_get hGet⟩
  by_contra! hOrder
  have hEarlier := eventBeforeClosedCut hp hX (copyLoaderWarp hp hX hCopy.copy) hCut
    (primingArrivalCut stage) hGet hCopy.decoded hOrder hBounds.1 hBounds.2
  exact (Nat.not_lt_of_ge hLower) hEarlier

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
