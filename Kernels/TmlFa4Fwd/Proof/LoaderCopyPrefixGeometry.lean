-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingCopyGeometry
public import Kernels.TmlFa4Fwd.Proof.LoaderActualRecurringGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderPacketContinuity
import Lemmas.Flow.OpPcsFast
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketGuardWindow

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy

noncomputable section

/-- An actual ordinary copy originates at a decoded instruction in the loader role. -/
theorem actualCopyAtInLoader {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc : Nat} {spec : AsyncCopy.Spec}
    (he : X.get i = some ⟨pc, .copy spec⟩) :
    174 ≤ pc ∧ pc < 1906 ∧ packetCopyAt pc = true := by
  rcases get_source hX he with ⟨_, hFalse⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hFalse
  have hBulk := fires_bulk_op hf rfl
  have hAudit : OpPcsFast kernel.code bulkOp (List.range' 174 (1906 - 174)) = true := by
    decide +kernel
  obtain ⟨hLo, hHi⟩ := List.mem_range'_1.mp (OpPcsFast.mem hAudit hc hBulk)
  change 174 ≤ pc at hLo
  change pc < 1906 at hHi
  have hOrd : ((kernel.code.drop 174).take (1906 - 174)).all
      (fun ins => !bulkOp ins.op || packetCopyOp ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hm : ins ∈ (kernel.code.drop 174).take (1906 - 174) := by
    apply List.mem_of_getElem? (i := pc - 174)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  have hCopy : packetCopyOp ins.op = true := by
    simpa only [hBulk, Bool.not_true, Bool.false_or] using List.all_eq_true.mp hOrd ins hm
  exact ⟨hLo, hHi, by simp [packetCopyAt, hc, hCopy]⟩

private theorem planeInPacket (site : Fin 6) (pair : Fin 16) (upper : Bool) :
    copyPacketFirst site ≤ packetPlanePc site pair upper ∧
      packetPlanePc site pair upper < copyCommitPc site := by
  fin_cases site <;> fin_cases pair <;> cases upper <;> decide

private theorem guardQuietOfObservedSlice {l : Launch} {X : Execution}
    (site : Fin 4) {g start index wait stop lower : Nat} {t u : TState}
    {visits post : List Visit} {event : Event}
    (hScope : stop ≤ reuseArrival site) (hStart : start ≤ wait)
    (hw : Walk kernel Assumptions.all l g t ((X.tr g).drop start) visits)
    (hSeen : (loaderSliceEvents lower stop visits)[index-start]? = some event)
    (he : X.get (g,index) = some event) (hWait : wait < index)
    (hu : u.pc = (recurringEmptyWait site).pc + 3) (hShape : RingShape u)
    (hTail : Walk kernel Assumptions.all l g u ((X.tr g).drop (wait+1)) post) :
    ∀ j, wait < j → j < index → ∀ e, X.get (g,j) = some e → ¬ Thread.Loader.recurringEmptyEvent e :=
    by
  have hIndex : index - (wait+1) < ((X.tr g).drop (wait+1)).length := by
    rw [List.length_drop]
    have hLen : index < (X.tr g).length := len_of_get he
    omega
  have hQuiet := Thread.Loader.packetGuardWindow site hu hShape hTail hIndex
    (fun j hj e hGet hPc => by
      have hActual : X.get (g,wait+1+j) = some e := by
        rwa [List.getElem?_drop] at hGet
      have hPrior := Thread.Loader.beforeObservedSliceEvent hw hSeen
        (show start ≤ wait+1+j by omega) (show wait+1+j < index by omega) hActual
      omega)
  intro j hj hBefore e hGet
  apply hQuiet (j-(wait+1)) (by omega) e
  rwa [List.getElem?_drop,Nat.add_sub_of_le hj]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem actualSwizzledCopyGuard (hX : Consistent l kernel Assumptions.all m X)
    (site : Fin 3) (pair : Fin 16) (upper : Bool) {g index : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) =
      some ⟨packetPlanePc (recurringPacketSite (recurringSwizzlePacket site)) pair upper,
        .copy spec⟩) :
    ∃ (slot : Fin 3) (wait parity : Nat),
      spec.dst = {loc := ⟨.shared, g / l.block,
        kvCopyAddress l.sharedBase slot (g % l.block) pair upper⟩, size := 16} ∧
      X.get (g, wait) = some ⟨(recurringEmptyWait (recurringSwizzlePacket site)).pc,
        .wait (Prologue.initObject l (g / l.block) (emptySlot slot)) parity true true .cta⟩ ∧
      Resumes kernel X (g, wait) (g, index) ∧
      ∀ j, wait < j → j < index → ∀ e, X.get (g,j) = some e →
        ¬ Thread.Loader.recurringEmptyEvent e := by
  let recurring := recurringSwizzlePacket site
  have hRange := planeInPacket (recurringPacketSite recurring) pair upper
  obtain ⟨stage, start, s, vs, hStart, hs, hLane, hw, hSeen⟩ :=
    actualRecurringCopyCheckpoint hp hX recurring he hRange.1 hRange.2
  have hAt : At s (recurringSwizzleEntry site)
      (recurringSwizzleEntryFacts l site (g % l.block) stage) := by
    fin_cases site
    · exact hs.mono ⟨hLane.1, hs.2.2.2.2.2.1, hLane.warmColumn hs.1, hs.2.2.2.2.1, trivial⟩
    · exact hs.mono ⟨hLane.1, hs.2.2.2.2.2.1, hs.2.2.2.2.1, trivial⟩
    · exact hs.mono ⟨hLane.1, hs.2.2.2.2.2.1, hLane.steadyColumn hs.1, hs.2.2.2.2.1, trivial⟩
  have hPc : recurringSelectionStart recurring = recurringSwizzleEntry site := by
    fin_cases site <;> rfl
  have hSamePc : recurringSelectionStart recurring = reuseEntry recurring := by
    fin_cases site <;> rfl
  have hSameReg : recurringSelectionStageReg recurring = (recurringStageInputs recurring).1 := by
    fin_cases site <;> rfl
  have hEmptyAt : At s (reuseEntry recurring)
      [((recurringStageInputs recurring).1, b32 stage), (2535, b32 l.sharedBase)] := by
    simpa only [hSamePc, hSameReg] using hs
  have hEarlier : (recurringEmptyWait recurring).pc <
      copyPacketFirst (recurringPacketSite recurring)
      := by fin_cases site <;> decide
  have hStop :
      (recurringEmptyWait recurring).pc < copyCommitPc (recurringPacketSite recurring) :=
    hEarlier.trans (hRange.1.trans_lt hRange.2)
  obtain ⟨retries, parity, rest, _, hTrace, hResumes, u, post, hu, hShape, hWalk⟩ :=
    recurringCopyEmptyFromCheckpointWithResume hp hX recurring stage he hStart hEmptyAt hw
      hSamePc.le (hEarlier.trans_le hRange.1) hStop (List.mem_of_getElem? hSeen)
  rw [hPc] at hSeen
  have hDst := recurringCopyDestinationFromEntry hp stage.isLt site hAt hw pair upper
    (List.mem_of_getElem? hSeen)
  have hTail : Walk kernel Assumptions.all l g u ((X.tr g).drop (start+retries+1)) post := by
    rw [show start+retries+1 = start+(retries+1) by omega, ← List.drop_drop, hTrace]
    simpa [List.drop_append] using hWalk
  have hQuiet := guardQuietOfObservedSlice recurring
    (stop := copyCommitPc (recurringPacketSite recurring)) (by fin_cases site <;> decide)
    (show start ≤ start+retries by omega) hw hSeen he hResumes.1.2.1 hu hShape hTail
  refine ⟨stage, start + retries, parity, hDst, ?_, hResumes, hQuiet⟩
  change (X.tr g)[start + retries]? = _
  rw [← List.getElem?_drop, hTrace, List.getElem?_append_right (by simp),
    List.length_replicate, Nat.sub_self]
  rfl

private theorem actualSwizzledCopyTarget (hX : Consistent l kernel Assumptions.all m X)
    (site : Fin 3) (pair : Fin 16) (upper : Bool) {g index : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) =
      some ⟨packetPlanePc (recurringPacketSite (recurringSwizzlePacket site)) pair upper,
        .copy spec⟩) :
    ∃ slot : Fin 3, spec.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase slot (g % l.block) pair upper⟩, size := 16} := by
  obtain ⟨slot, _, _, hTarget, _, _, _⟩ := actualSwizzledCopyGuard hp hX site pair upper he
  exact ⟨slot, hTarget⟩

omit hp in
private theorem loaderSliceEvents_upper {lower mid high : Nat} (h : mid ≤ high)
    {vs : List Visit} {e : Event} (he : e ∈ loaderSliceEvents lower mid vs) :
    e ∈ loaderSliceEvents lower high vs := by
  unfold loaderSliceEvents at *
  have hSub : ∀ (xs : List Visit), xs.takeWhile (fun v => lower ≤ v.pc && v.pc < mid) ⊆
      xs.takeWhile (fun v => lower ≤ v.pc && v.pc < high) := by
    intro xs
    induction xs with
    | nil => simp
    | cons v rest ih =>
      by_cases hBounds : lower ≤ v.pc ∧ v.pc < mid
      · have hHigh : v.pc < high := hBounds.2.trans_le h
        simp only [List.takeWhile_cons, hBounds.1, hBounds.2, hHigh, decide_true,
          Bool.and_self, ↓reduceIte]
        intro x hx
        exact (List.mem_cons.mp hx).elim (fun hEq => hEq ▸ List.mem_cons_self)
          (fun hr => List.mem_cons_of_mem _ (ih hr))
      · simp [List.takeWhile_cons, hBounds]
  obtain ⟨v, hv, hV⟩ := List.mem_filterMap.mp he
  exact List.mem_filterMap.mpr ⟨v, hSub vs hv, hV⟩

private theorem actualSteadyVCopyGuard (hX : Consistent l kernel Assumptions.all m X)
    (pair : Fin 16) (upper : Bool) {g index : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) = some ⟨packetPlanePc 5 pair upper, .copy spec⟩) :
    ∃ (slot : Fin 3) (wait parity : Nat),
      spec.dst = {loc := ⟨.shared, g / l.block,
        kvCopyAddress l.sharedBase slot (g % l.block) pair upper⟩, size := 16} ∧
      X.get (g, wait) = some ⟨(recurringEmptyWait 3).pc,
        .wait (Prologue.initObject l (g / l.block) (emptySlot slot)) parity true true .cta⟩ ∧
      Resumes kernel X (g, wait) (g, index) ∧
      ∀ j, wait < j → j < index → ∀ e, X.get (g,j) = some e →
        ¬ Thread.Loader.recurringEmptyEvent e := by
  have hRange := planeInPacket 5 pair upper
  obtain ⟨k, start, s, vs, hStart, hs, hLane, hw, hSeen⟩ :=
    actualRecurringCopyCheckpoint hp hX 3 he hRange.1 hRange.2
  have hAt : At s 1451 (recurringSwizzleInputs l (g % l.block) 2 ++ [(7179, b32 k)]) :=
    hs.mono ⟨hLane.1, hs.2.2.2.2.2.1, hLane.steadySwizzleColumn hs.1, hs.2.2.2.2.1, trivial⟩
  let stage : Fin 3 := ⟨(k.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
  have hDst := steadyVCopyDestinationFromSwizzle hp k hAt hw pair upper
    (List.mem_of_getElem? hSeen)
  let event : Event := ⟨packetPlanePc 5 pair upper, .copy spec⟩
  have hLater : 1611 < event.pc := by
    change 1611 < packetPlanePc 5 pair upper
    fin_cases pair <;> cases upper <;> decide
  have hExtension : event ∈ loaderSliceEvents 1451 1736 vs := by
    apply loaderSliceEvents_upper (mid := copyCommitPc 5) (by decide)
    exact List.mem_of_getElem? hSeen
  obtain ⟨pre, rest, t, tail, hSplit, hEarlier, hFrame, hTail, hAtEvent⟩ :=
    steadyVBarrierAfterSwizzle k (by simp [event, Ends]) (by omega) hs hw hExtension
  have hBefore : start + pre.length ≤ index := by
    by_contra! hTooEarly
    have hGet : ((X.tr g).drop start)[index - start]? = some event := by
      rwa [List.getElem?_drop, Nat.add_sub_of_le hStart]
    rw [hSplit, List.getElem?_append_left (by omega)] at hGet
    exact (Nat.not_lt_of_ge (by omega)) (hEarlier event (List.mem_of_getElem? hGet))
  have hRest : (X.tr g).drop (start + pre.length) = rest := by
    rw [← List.drop_drop, hSplit]
    simp
  have ht : Walk kernel Assumptions.all l g t ((X.tr g).drop (start + pre.length)) tail :=
    hRest.symm ▸ hTail
  obtain ⟨retries, parity, _, _, hTrace, hResumes, u, post, hu, hShape, hWalk⟩ :=
    recurringCopyEmptyFromCheckpointWithResume hp hX 3 stage he hBefore hFrame ht
      (by decide) hLater (by decide) hAtEvent
  have hTail : Walk kernel Assumptions.all l g u
      ((X.tr g).drop (start+pre.length+retries+1)) post := by
    rw [show start+pre.length+retries+1 = (start+pre.length)+(retries+1) by omega,
      ← List.drop_drop, hTrace]
    simpa [List.drop_append] using hWalk
  have hQuiet := guardQuietOfObservedSlice 3 (stop := copyCommitPc 5) (by decide)
    (show start ≤ start+pre.length+retries by omega) hw hSeen he hResumes.1.2.1 hu hShape hTail
  refine ⟨stage, start + pre.length + retries, parity, hDst, ?_, hResumes, hQuiet⟩
  change (X.tr g)[start + pre.length + retries]? = _
  rw [← List.getElem?_drop, hTrace, List.getElem?_append_right (by simp),
    List.length_replicate, Nat.sub_self]
  rfl

private theorem actualSteadyVCopyTarget (hX : Consistent l kernel Assumptions.all m X)
    (pair : Fin 16) (upper : Bool) {g index : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) = some ⟨packetPlanePc 5 pair upper, .copy spec⟩) :
    ∃ slot : Fin 3, spec.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase slot (g % l.block) pair upper⟩, size := 16} := by
  obtain ⟨slot, _, _, hDst, _, _, _⟩ := actualSteadyVCopyGuard hp hX pair upper he
  exact ⟨slot, hDst⟩

private theorem actualPrimingCopyTarget (hX : Consistent l kernel Assumptions.all m X)
    (slot : Fin 2) (pair : Fin 16) (upper : Bool) {g index : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) = some ⟨packetPlanePc (primingPacketSite slot) pair upper, .copy spec⟩) :
    ∃ stage : Fin 3, spec.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase stage (g % l.block) pair upper⟩, size := 16} := by
  have hRange := planeInPacket (primingPacketSite slot) pair upper
  obtain ⟨start, s, vs, _, hs, hw, hSeen⟩ :=
    actualPrimingCopyCheckpoint hp hX slot he hRange.1 hRange.2
  refine ⟨⟨slot, by have := slot.isLt; omega⟩, ?_⟩
  exact primingCopyDestinationFromEntry hp slot pair upper hs hw (List.mem_of_getElem? hSeen)

/-- Every recurring copy is guarded by the successful empty acquire of
its actual destination slot, including before the group has published. -/
theorem actualRecurringCopySlotGuardLatest (hX : Consistent l kernel Assumptions.all m X)
    (site : Fin 4) (pair : Fin 16) (upper : Bool) {g index : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) = some ⟨packetPlanePc (recurringPacketSite site) pair upper, .copy spec⟩)
    :
    ∃ (slot : Fin 3) (wait parity : Nat),
      spec.dst = {loc := ⟨.shared, g / l.block,
        kvCopyAddress l.sharedBase slot (g % l.block) pair upper⟩, size := 16} ∧
      X.get (g, wait) = some ⟨(recurringEmptyWait site).pc,
        .wait (Prologue.initObject l (g / l.block) (emptySlot slot)) parity true true .cta⟩ ∧
      Resumes kernel X (g, wait) (g, index) ∧
      ∀ j, wait < j → j < index → ∀ e, X.get (g,j) = some e →
        ¬ Thread.Loader.recurringEmptyEvent e := by
  fin_cases site
  · exact actualSwizzledCopyGuard hp hX 0 pair upper he
  · exact actualSwizzledCopyGuard hp hX 1 pair upper he
  · exact actualSwizzledCopyGuard hp hX 2 pair upper he
  · exact actualSteadyVCopyGuard hp hX pair upper he

/-- The exact shared destination follows the same-slot empty acquire. -/
theorem actualRecurringCopySlotGuard (hX : Consistent l kernel Assumptions.all m X) (site : Fin 4)
    (pair : Fin 16) (upper : Bool) {g index : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) = some ⟨packetPlanePc (recurringPacketSite site) pair upper, .copy spec⟩)
    :
    ∃ (slot : Fin 3) (wait parity : Nat),
      spec.dst = {loc := ⟨.shared, g / l.block,
        kvCopyAddress l.sharedBase slot (g % l.block) pair upper⟩, size := 16} ∧
      X.get (g, wait) = some ⟨(recurringEmptyWait site).pc,
        .wait (Prologue.initObject l (g / l.block) (emptySlot slot)) parity true true .cta⟩ ∧
      Resumes kernel X (g, wait) (g, index) := by
  obtain ⟨slot, wait, parity, hDst, hPoll, hBefore, _⟩ :=
    actualRecurringCopySlotGuardLatest hp hX site pair upper he
  exact ⟨slot,wait,parity,hDst,hPoll,hBefore⟩

/-- An actual ordinary copy has its decoded lane, pair and vector plane even
when the execution ends before that packet's commit or publication. -/
theorem actualCopyPrefixDestination (hX : Consistent l kernel Assumptions.all m X) (site : Fin 6)
    (pair : Fin 16) (upper : Bool) {g index : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) = some ⟨packetPlanePc site pair upper, .copy spec⟩) :
    ∃ slot : Fin 3, spec.dst = {loc := ⟨.shared, g / l.block,
      kvCopyAddress l.sharedBase slot (g % l.block) pair upper⟩, size := 16} := by
  fin_cases site
  · exact actualPrimingCopyTarget hp hX 0 pair upper he
  · exact actualPrimingCopyTarget hp hX 1 pair upper he
  · exact actualSwizzledCopyTarget hp hX 0 pair upper he
  · exact actualSwizzledCopyTarget hp hX 1 pair upper he
  · exact actualSwizzledCopyTarget hp hX 2 pair upper he
  · exact actualSteadyVCopyTarget hp hX pair upper he

/-- Two pending ordinary copies in the same async group write disjoint vectors.
The group may remain uncommitted in the actual execution prefix. -/
theorem sameGroupCopyDestinationsApart (hX : Consistent l kernel Assumptions.all m X) {i j : EvId}
    {a b : AsyncCopy.Spec} (hGroup : SameAsyncGroup X i j) (ha : X.Copy i a) (hb : X.Copy j b) :
    ¬ a.dst.Overlap b.dst := by
  obtain ⟨g, i⟩ := i
  obtain ⟨other, j⟩ := j
  have hThread : g = other := hGroup.2.2.1
  subst other
  obtain ⟨pc, ha⟩ := ha
  obtain ⟨qc, hb⟩ := hb
  obtain ⟨hLo, hHi, hPa⟩ := actualCopyAtInLoader hX ha
  obtain ⟨site, hFirst, hBefore⟩ := loaderCopyPcInPacket hLo hHi hPa
  obtain ⟨hOrder, hLast⟩ := packetCopyPcOrderAndWindow hX site ha hb ⟨hFirst, hBefore⟩ hGroup
  have hPb := (actualCopyAtInLoader hX hb).2.2
  have hStrict : qc < copyCommitPc site := by
    by_contra! he
    have hQ : qc = copyCommitPc site := by omega
    rw [hQ, packetCopyAt, (copyCommitCode site).1] at hPb
    cases hPb
  obtain ⟨pa, ua, hpA⟩ := packetCopyCoordinates site hFirst hBefore hPa
  obtain ⟨pb, ub, hpB⟩ := packetCopyCoordinates site (hFirst.trans hOrder.le) hStrict hPb
  rw [hpA] at ha
  rw [hpB] at hb
  obtain ⟨sa, hA⟩ := actualCopyPrefixDestination hp hX site pa ua ha
  obtain ⟨sb, hB⟩ := actualCopyPrefixDestination hp hX site pb ub hb
  have hDiff : pa.val ≠ pb.val ∨ ua ≠ ub := by
    by_contra! h
    obtain ⟨hPair, hUpper⟩ := h
    have hh : pa = pb := Fin.ext hPair
    rw [hpA, hpB, hh, hUpper] at hOrder
    exact (Nat.lt_irrefl _ hOrder)
  let x := kvCopyAddress l.sharedBase sa (g % l.block) pa ua
  let y := kvCopyAddress l.sharedBase sb (g % l.block) pb ub
  have hApart : x + 16 ≤ y ∨ y + 16 ≤ x :=
    kvCopyVectorsApart hp.shared.1 pa.isLt pb.isLt (Or.inr (Or.inr hDiff))
  rw [hA, hB]
  rintro ⟨loc, ⟨_, _, hxa, hxb⟩, ⟨_, _, hya, hyb⟩⟩
  change x ≤ loc.addr at hxa
  change loc.addr < x + 16 at hxb
  change y ≤ loc.addr at hya
  change loc.addr < y + 16 at hyb
  omega

/-- No consistent TML FA4 execution prefix has a same-group ordinary-copy overlap. -/
theorem noCpAsyncOverlap (hX : Consistent l kernel Assumptions.all m X) :
    ¬ CpAsyncOverlap X := by
  rintro ⟨i, j, a, b, hGroup, ha, hb, hOverlap⟩
  exact sameGroupCopyDestinationsApart hp hX hGroup ha hb hOverlap

end
end PTX.Kernels.TmlFa4Fwd.Loader
