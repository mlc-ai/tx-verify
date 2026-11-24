-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingCopyGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {issue : EvId}
    (group : PublishedCopyGroup l X issue) {target : Loc} (hIssue : X.AsyncArrive issue target true)
include hp hX group hIssue

/-- Each member of an observed priming group has its actual packet vector and destination. -/
theorem primingGroupGeometry (hPriming : group.publication.packet.period = .priming) :
    ∃ packet : Fin 6, DecodedObservation.packetOfSite packet = group.publication.packet ∧
      ∀ {j : Nat} {spec : AsyncCopy.Spec}, (j, spec) ∈ group.copies →
      ∃ pair : Fin 16, ∃ upper : Bool,
        X.get (issue.1, j) = some ⟨packetPlanePc packet pair upper, .copy spec⟩ ∧
        let address := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block)
          pair upper
        spec.dst = {loc := ⟨.shared, issue.1 / l.block, address⟩, size := 16} := by
  obtain ⟨g, index⟩ := issue
  obtain ⟨pc, he⟩ := hIssue
  obtain ⟨⟨site, rfl⟩, _, _, _⟩ := actualAsyncArrival hX he
  obtain ⟨pub, _, hLoc, hObs⟩ := readyObservation hp hX he rfl
  have hState := (congrArg D.published (prefixStep (l := l) he)).trans (advancePublication hObs)
  have hPub : pub = group.publication :=
    (List.cons.inj (hState.symm.trans group.published)).1
  have hPacket : pub.packet = DecodedObservation.packetOfSite site := by
    have hCode : DecodedObservation.observePacket (copyCommitPc site + 1) true =
        some (DecodedObservation.packetOfSite site) := by fin_cases site <;> decide
    simp only [observe, hCode] at hObs
    split at hObs <;> cases hObs
    exact (Option.some.inj (by assumption)).symm
  have hStage : ∃ stage : Fin 2, site = primingPacketSite stage := by
    have ha := hPriming
    rw [← hPub, hPacket] at ha
    fin_cases site
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    all_goals cases ha
  obtain ⟨stage, rfl⟩ := hStage
  let slot : Fin 3 := ⟨stage, by have := stage.isLt; omega⟩
  have hLoc' : target = readyObject l g slot := by
    have hSite : copyCommitPc (primingPacketSite stage) + 1 ∈ [674, 904] := by
      fin_cases stage <;> decide
    rw [loaderStartupAsyncAddress hp hX he hSite]
    fin_cases stage <;> rfl
  have hSlot : group.publication.slot = slot := by
    rw [hPub] at hLoc
    have hAddr := congrArg Loc.addr (hLoc.symm.trans hLoc')
    simp only [readyObject, readySlot_address] at hAddr
    exact Fin.ext (by omega)
  obtain ⟨start, t, visits, hStart, ht, hw, hSeen⟩ := actualPrimingSwizzleCheckpoint hp hX stage he
  have hWindow := primingPacketGeometryWindow stage ht.1 (ringShapeOfAt ht) hw hStart hSeen
  refine ⟨primingPacketSite stage, hPacket.symm.trans (congrArg Publication.packet hPub),
    fun {j} {spec} hCopy => ?_⟩
  obtain ⟨pair, upper, hRaw, hMember⟩ :=
    group.coordinatesInWindow hX (primingPacketSite stage) hCopy hWindow
  have hDst := primingCopyDestinationFromEntry hp stage pair upper ht hw hMember
  exact ⟨pair, upper, hRaw, by simpa only [hSlot] using hDst⟩

/-- An actual ordinary copy in any published packet belongs to its published slot
and has one of the lane's exact 16-byte vectors. -/
theorem PublishedCopyGroup.destination {j : Nat} {spec : AsyncCopy.Spec}
    (hCopy : (j, spec) ∈ group.copies) :
    ∃ pair : Fin 16, ∃ upper : Bool,
      let address := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block)
        pair upper
      spec.dst = {loc := ⟨.shared, issue.1 / l.block, address⟩, size := 16} := by
  by_cases hPriming : group.publication.packet.period = .priming
  · obtain ⟨packet, _, hg⟩ := primingGroupGeometry hp hX group hIssue hPriming
    obtain ⟨pair, upper, _, hDst⟩ := hg hCopy
    exact ⟨pair, upper, hDst⟩
  · exact group.recurringDestination hp hX hIssue hPriming hCopy

private theorem primingVectorAtSite (site : Fin 2)
    (hPriming : group.publication.packet = DecodedObservation.packetOfSite (primingPacketSite site))
    (wanted : Fin 16) (upper : Bool) :
    ∃ j spec, (j, spec) ∈ group.copies ∧
      X.get (issue.1, j) =
        some ⟨packetPlanePc (primingPacketSite site) wanted upper, .copy spec⟩ := by
  have hPeriod : group.publication.packet.period = .priming := by
    rw [hPriming]
    fin_cases site <;> rfl
  obtain ⟨packet, hPacket, hGeometry⟩ := primingGroupGeometry hp hX group hIssue hPeriod
  have hSite : packet = primingPacketSite site := by
    rw [hPriming] at hPacket
    fin_cases site <;> fin_cases packet <;> first | rfl | cases hPacket
  subst packet
  obtain ⟨j, spec, hMember, hDst⟩ :=
    group.coverageOfCoordinates hX (primingPacketSite site) hGeometry wanted upper
  obtain ⟨pair, plane, hGet, hAddress⟩ := hGeometry hMember
  have hEq : kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block) pair plane =
      kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block) wanted upper :=
    congrArg (fun a : Acc => a.loc.addr) (hAddress.symm.trans hDst)
  have hPair : pair.val = wanted.val ∧ plane = upper := by
    by_contra! hDifferent
    have hDifferent' : pair.val ≠ wanted.val ∨ plane ≠ upper := by
      by_cases hSame : pair.val = wanted.val
      · exact .inr (hDifferent hSame)
      · exact .inl hSame
    have hApart := kvCopyAddress_apart (stage := group.publication.slot)
      (lane := issue.1 % l.block) hp.shared.1 pair.isLt wanted.isLt hDifferent'
    omega
  obtain ⟨hPair, hPlane⟩ := hPair
  have hPair' : pair = wanted := Fin.ext hPair
  subst pair plane
  exact ⟨j, spec, hMember, hGet⟩

/-- Recover the actual issue of a vector with the given coordinates in the priming K group. -/
theorem PublishedCopyGroup.primingKeyVector (hPriming : group.publication.packet = ⟨.priming, .key⟩)
    (wanted : Fin 16) (upper : Bool) :
    ∃ j spec, (j, spec) ∈ group.copies ∧
      X.get (issue.1, j) = some ⟨packetPlanePc 0 wanted upper, .copy spec⟩ :=
  primingVectorAtSite hp hX group hIssue 0 hPriming wanted upper

/-- Recover the actual issue of a vector with the given coordinates in the priming V group. -/
theorem PublishedCopyGroup.primingValueVector
    (hPriming : group.publication.packet = ⟨.priming, .value⟩) (wanted : Fin 16) (upper : Bool) :
    ∃ j spec, (j, spec) ∈ group.copies ∧
      X.get (issue.1, j) = some ⟨packetPlanePc 1 wanted upper, .copy spec⟩ :=
  primingVectorAtSite hp hX group hIssue 1 hPriming wanted upper

/-- Every vector coordinate of any published K/V packet has an actual issuing
copy in the loader's recorded group. -/
theorem PublishedCopyGroup.coverage (pair : Fin 16) (upper : Bool) :
    ∃ j spec, (j, spec) ∈ group.copies ∧
      let address := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block)
        pair upper
      spec.dst = {loc := ⟨.shared, issue.1 / l.block, address⟩, size := 16} := by
  by_cases hPriming : group.publication.packet.period = .priming
  · obtain ⟨packet, _, hg⟩ := primingGroupGeometry hp hX group hIssue hPriming
    exact group.coverageOfCoordinates hX packet hg pair upper
  · exact group.recurringCoverage hp hX hIssue hPriming pair upper
end

/-- The group records the physical slot named by its actual publication. -/
theorem PublishedCopyGroup.slotFor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} (group : PublishedCopyGroup l X issue) {owner : Nat} {slot : Fin 3}
    (hIssue : X.AsyncArrive issue (readyObject l owner slot) true) :
    group.publication.slot = slot := by
  obtain ⟨g, index⟩ := issue
  obtain ⟨pc, he⟩ := hIssue
  obtain ⟨pub, _, hLoc, hPub⟩ := readyStep hp hX he rfl
  have hSame := (List.cons.inj (group.published.symm.trans hPub)).1
  have hAddr := congrArg Loc.addr hLoc
  rw [← hSame] at hAddr
  simp only [readyObject, readySlot_address] at hAddr
  exact Fin.ext (by omega)

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
