-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketFacts
import Kernels.TmlFa4Fwd.Proof.LoaderActualRecurringGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderPacketContinuity
import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- Identify a member's actual pair and plane in the adopted address-calculation window.
The first copy and precise commit cutoff come from the same issuing-thread walk. -/
theorem PublishedCopyGroup.coordinatesInWindow {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g start index j lower : Nat} {vs : List Visit}
    (packet : Fin 6) (group : PublishedCopyGroup l X (g, index)) {spec : AsyncCopy.Spec}
    (hCopy : (j, spec) ∈ group.copies)
    (hGeometry :
      (∃ (first : Nat) (spec : AsyncCopy.Spec), start ≤ first ∧ first + 1 < index ∧
        X.get (g, first) = some ⟨copyPacketFirst packet, .copy spec⟩ ∧
        ∀ j e, first ≤ j → j + 1 < index → X.get (g, j) = some e →
          copyPacketFirst packet ≤ e.pc ∧ e.pc < copyCommitPc packet) ∧
      ∀ j e, start ≤ j → j + 1 < index → X.get (g, j) = some e →
        e ∈ loaderSliceEvents lower (copyCommitPc packet) vs) :
    ∃ pair : Fin 16, ∃ upper : Bool,
      X.get (g, j) = some ⟨packetPlanePc packet pair upper, .copy spec⟩ ∧
      ⟨packetPlanePc packet pair upper, .copy spec⟩ ∈
        loaderSliceEvents lower (copyCommitPc packet) vs := by
  obtain ⟨⟨first, firstSpec, hFirst, hBefore, hEvent, hPacket⟩, hWindow⟩ := hGeometry
  obtain ⟨hLo, hHi, hc⟩ := (group.member j spec).mp hCopy
  have hAdjoin : group.commit + 1 = index := group.closesAt
  have firstMember (hOrd : group.first ≤ first) : (first, firstSpec) ∈ group.copies :=
    (group.member first firstSpec).mpr ⟨hOrd, by omega, _, hEvent⟩
  have hAfter : first ≤ j := by
    by_contra! hEarlier
    obtain ⟨k, commitSite, hLeft, hRight, hCommit⟩ :=
      packetEntrySeparatesCopies hX packet hc hEvent rfl hEarlier
    have hSame := group.sameGroup hCopy (firstMember (by omega)) hEarlier
    exact hSame.2.2.2.2 k (copyCommitPc commitSite) hLeft hRight hCommit
  obtain ⟨pc, hGet⟩ := hc
  have hBounds := hPacket j _ hAfter (by omega) hGet
  have hCoordinates := actualPacketCopyCoordinates hX packet hBounds.1 hBounds.2 hGet
  obtain ⟨pair, upper, rfl⟩ := hCoordinates
  exact ⟨pair, upper, hGet, hWindow j _ (hFirst.trans hAfter) (by omega) hGet⟩

private theorem selectedInRecurringWindow {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g start index j : Nat} {s : TState} {vs : List Visit} {target : Loc}
    (site : Fin 4) (group : PublishedCopyGroup l X (g, index)) {spec : AsyncCopy.Spec}
    (hCopy : (j, spec) ∈ group.copies)
    (hStart : start ≤ index) (hPc : s.pc = recurringSelectionStart site) (hs : RingShape s)
    (hw : Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs)
    (hSaw : (loaderSliceEvents (recurringSelectionStart site) (reuseArrival site + 1)
      vs)[index - start]? = some ⟨reuseArrival site, .asyncArrive target true⟩) :
    let packet := recurringPacketSite site
    ∃ pair : Fin 16, ∃ upper : Bool,
      X.get (g, j) = some ⟨packetPlanePc packet pair upper, .copy spec⟩ ∧
      ⟨packetPlanePc packet pair upper, .copy spec⟩ ∈
        loaderSliceEvents (recurringSelectionStart site) (copyCommitPc packet) vs := by
  exact group.coordinatesInWindow hX (recurringPacketSite site) hCopy
    (recurringPacketGeometryWindow site hPc hs hw hStart hSaw)

private theorem readySlotOfTarget {l : Launch} {g : Nat} {a b : Fin 3}
    (h : readyObject l g a = readyObject l g b) : a = b := by
  have he := congrArg Loc.addr h
  simp only [readyObject, readySlot_address] at he
  exact Fin.ext (by omega)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {issue : EvId}
    (group : PublishedCopyGroup l X issue) {target : Loc} (hIssue : X.AsyncArrive issue target true)
    (hRecurring : group.publication.packet.period ≠ .priming)
include hp hX group hIssue hRecurring

/-- Recover each observed member's decoded coordinates in its actual published packet. -/
theorem PublishedCopyGroup.recurringCoordinates :
    ∃ site : Fin 4, DecodedObservation.packetOfSite (recurringPacketSite site) =
        group.publication.packet ∧
      ∀ {j : Nat} {spec : AsyncCopy.Spec}, (j, spec) ∈ group.copies →
      ∃ pair : Fin 16, ∃ upper : Bool,
        X.get (issue.1, j) = some
          ⟨packetPlanePc (recurringPacketSite site) pair upper, .copy spec⟩ ∧
        let address := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block)
          pair upper
        spec.dst = {loc := ⟨.shared, issue.1 / l.block, address⟩, size := 16} := by
  obtain ⟨g, index⟩ := issue
  obtain ⟨pc, hGet⟩ := hIssue
  obtain ⟨⟨raw, rfl⟩, _, _, _⟩ := actualAsyncArrival hX hGet
  obtain ⟨pub, _, hLoc, hObs⟩ := readyObservation hp hX hGet rfl
  have hPublished := (congrArg D.published (prefixStep hGet)).trans (advancePublication hObs)
  have hPub : pub = group.publication := by
    have hEq := hPublished.symm.trans group.published
    exact (List.cons.inj hEq).1
  have hDecode : DecodedObservation.observePacket (copyCommitPc raw + 1) true =
      some (DecodedObservation.packetOfSite raw) := by fin_cases raw <;> decide
  have hForm : pub.packet = DecodedObservation.packetOfSite raw := by
    simp only [observe, hDecode] at hObs
    split at hObs <;> cases hObs
    exact (Option.some.inj (by assumption)).symm
  have hRange : 2 ≤ raw.val := by
    rw [← hPub, hForm] at hRecurring
    fin_cases raw <;> first | exact (hRecurring rfl).elim | decide
  let site : Fin 4 := ⟨raw.val - 2, by have := raw.isLt; omega⟩
  have hSite : recurringPacketSite site = raw := Fin.ext (by
    change raw.val - 2 + 2 = raw.val
    omega)
  have hIssue' : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive target true⟩ := by
    simpa only [reuseArrival, hSite] using hGet
  have hTarget : target = readyObject l g group.publication.slot := by simpa only [hPub] using hLoc
  refine ⟨site, ?_, fun {j} {spec} hCopy => ?_⟩
  · rw [hSite, ← hForm, hPub]
  · by_cases hs : site = 3
    · have hLast : X.get (g, index) = some ⟨reuseArrival 3, .asyncArrive target true⟩ := by
        rw [← hs]
        exact hIssue'
      obtain ⟨k, start, s, vs, hStart, hPc, hShape, hReady, hw, hSaw, hGeom⟩ :=
        actualSteadyVSwizzleGeometry hp hX hLast
      let stage : Fin 3 := ⟨(k.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
      have hSlot : group.publication.slot = stage := readySlotOfTarget (hTarget.symm.trans hReady)
      obtain ⟨pair, upper, hCopyEvent, hMem⟩ :=
        selectedInRecurringWindow hX 3 group hCopy hStart hPc hShape hw hSaw
      have hDst := hGeom pair upper spec hMem
      exact ⟨pair, upper, hs.symm ▸ hCopyEvent, by simpa only [hSlot] using hDst⟩
    have hLt : site.val < 3 := by
      have hMax := site.isLt
      by_contra! h
      exact hs (Fin.ext (by change site.val = 3; omega))
    let jSite : Fin 3 := ⟨site.val, hLt⟩
    have hSmall : recurringSwizzlePacket jSite = site := Fin.ext rfl
    have hEarlier : X.get (g, index) =
        some ⟨reuseArrival (recurringSwizzlePacket jSite), .asyncArrive target true⟩ := by
      rw [hSmall]
      exact hIssue'
    obtain ⟨stage, start, s, vs, hStart, hPc, hShape, hReady, hw, hSaw, hGeom⟩ :=
      actualRecurringSwizzleGeometry hp hX jSite hEarlier
    have hStartPc : recurringSwizzleEntry jSite = recurringSelectionStart site := by
      have hEq (i : Fin 3) :
          recurringSwizzleEntry i = recurringSelectionStart (recurringSwizzlePacket i) := by
        fin_cases i <;> rfl
      simpa only [hSmall] using hEq jSite
    have hPacketPc : s.pc = recurringSelectionStart site := hPc.trans hStartPc
    have hIndexed : (loaderSliceEvents (recurringSelectionStart site) (reuseArrival site + 1)
        vs)[index - start]? = some ⟨reuseArrival site, .asyncArrive target true⟩ := by
      simpa only [hStartPc, hSmall, reuseArrival, Nat.add_assoc] using hSaw
    have hSlot : group.publication.slot = stage := readySlotOfTarget (hTarget.symm.trans hReady)
    obtain ⟨pair, upper, hCopyEvent, hMem⟩ :=
      selectedInRecurringWindow hX site group hCopy hStart hPacketPc hShape hw hIndexed
    have hSelected : ⟨packetPlanePc (recurringPacketSite (recurringSwizzlePacket jSite)) pair upper,
        .copy spec⟩ ∈ loaderSliceEvents (recurringSwizzleEntry jSite)
          (copyCommitPc (recurringPacketSite (recurringSwizzlePacket jSite))) vs := by
      simpa only [hStartPc, hSmall] using hMem
    have hDst := hGeom pair upper spec hSelected
    exact ⟨pair, upper, hCopyEvent, by simpa only [hSlot] using hDst⟩

/-- Every indexed vector in an actual recurring published group writes the decoded
pair and plane for its abstract publication slot and issuing lane. -/
theorem PublishedCopyGroup.recurringDestination {j : Nat} {spec : AsyncCopy.Spec}
    (hCopy : (j, spec) ∈ group.copies) :
    ∃ pair : Fin 16, ∃ upper : Bool,
      let address := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block)
        pair upper
      spec.dst = {loc := ⟨.shared, issue.1 / l.block, address⟩, size := 16} := by
  obtain ⟨_, _, hGeom⟩ := group.recurringCoordinates hp hX hIssue hRecurring
  obtain ⟨pair, upper, _, hDst⟩ := hGeom hCopy
  exact ⟨pair, upper, hDst⟩

omit hp hX group hIssue hRecurring in
private theorem planeInPacket (site : Fin 6) (pair : Fin 16) (upper : Bool) :
    copyPacketFirst site ≤ packetPlanePc site pair upper ∧
      packetPlanePc site pair upper < copyCommitPc site := by
  fin_cases site <;> fin_cases pair <;> cases upper <;> decide

omit hp hX group hIssue hRecurring in
/-- The 32 ordered copies cover the full coordinate set once their decoded
coordinates and destination facts are known. -/
theorem PublishedCopyGroup.coverageOfCoordinates {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} (group : PublishedCopyGroup l X issue) (packet : Fin 6)
    (hGeometry : ∀ {j : Nat} {spec : AsyncCopy.Spec}, (j, spec) ∈ group.copies →
      ∃ pair : Fin 16, ∃ upper : Bool,
        X.get (issue.1, j) = some ⟨packetPlanePc packet pair upper, .copy spec⟩ ∧
        let address := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block)
          pair upper
        spec.dst = {loc := ⟨.shared, issue.1 / l.block, address⟩, size := 16})
    (pair : Fin 16) (upper : Bool) :
    ∃ j spec, (j, spec) ∈ group.copies ∧
      let address := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block)
        pair upper
      spec.dst = {loc := ⟨.shared, issue.1 / l.block, address⟩, size := 16} := by
  let member (i : Fin group.copies.length) : Nat × AsyncCopy.Spec := group.copies[i.val]
  have hm (i : Fin group.copies.length) : member i ∈ group.copies := List.getElem_mem i.isLt
  let good (i : Fin group.copies.length) (c : Fin 16 × Bool) : Prop :=
    X.get (issue.1, (member i).1) = some
      ⟨packetPlanePc packet c.1 c.2, .copy (member i).2⟩ ∧
    let address := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block)
      c.1 c.2
    (member i).2.dst = {loc := ⟨.shared, issue.1 / l.block, address⟩, size := 16}
  have existsGood (i : Fin group.copies.length) : ∃ c, good i c := by
    obtain ⟨j, upper, pc, addr⟩ := hGeometry (hm i)
    exact ⟨⟨j, upper⟩, pc, addr⟩
  let coords (i : Fin group.copies.length) : Fin 16 × Bool := Classical.choose (existsGood i)
  have hGood (i : Fin group.copies.length) : good i (coords i) :=
    Classical.choose_spec (existsGood i)
  have strict (i j : Fin group.copies.length) (hLt : i < j) :
      packetPlanePc packet (coords i).1 (coords i).2 <
        packetPlanePc packet (coords j).1 (coords j).2 := by
    have hIdx : (member i).1 < (member j).1 :=
      group.ordered.rel_getElem_of_lt i.isLt j.isLt hLt
    exact packetCopyPcOrder hX packet (hGood i).1 (hGood j).1
      (planeInPacket packet (coords i).1 (coords i).2) (group.sameGroup (hm i) (hm j) hIdx)
  have hInject : Function.Injective coords := by
    intro i j h
    rcases lt_trichotomy i j with hLt | he | hGt
    · have he := congrArg (fun c => packetPlanePc packet c.1 c.2) h
      exact (Nat.ne_of_lt (strict i j hLt) he).elim
    · exact he
    · have he := congrArg (fun c => packetPlanePc packet c.1 c.2) h.symm
      exact (Nat.ne_of_lt (strict j i hGt) he).elim
  have hCard : Fintype.card (Fin group.copies.length) = Fintype.card (Fin 16 × Bool) := by
    rw [Fintype.card_fin, group.count]
    decide
  have hSurj := ((Fintype.bijective_iff_injective_and_card coords).mpr ⟨hInject, hCard⟩).2
  obtain ⟨i, hi⟩ := hSurj (pair, upper)
  have h := hGood i
  rw [hi] at h
  exact ⟨(member i).1, (member i).2, hm i, h.2⟩

/-- A recurring published group supplies a real copy for every pair and plane of its slot. -/
theorem PublishedCopyGroup.recurringCoverage (pair : Fin 16) (upper : Bool) :
    ∃ j spec, (j, spec) ∈ group.copies ∧
      let address := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block)
        pair upper
      spec.dst = {loc := ⟨.shared, issue.1 / l.block, address⟩, size := 16} := by
  obtain ⟨site, _, hGeometry⟩ := group.recurringCoordinates hp hX hIssue hRecurring
  exact group.coverageOfCoordinates hX (recurringPacketSite site) hGeometry pair upper

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
