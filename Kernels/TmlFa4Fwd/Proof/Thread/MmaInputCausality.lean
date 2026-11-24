-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.AllocationBarrierGeneration
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryInputOrder
public import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Kernels.TmlFa4Fwd.Proof.StaticSafety
public import Lemmas.Flow.NotArrive
public import Lemmas.Flow.NotWarpBar
public import Lemmas.Order.GuardSnoc
import Lemmas.Order.GuardObserver
public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Lemmas.Cluster.ClusterBarrierExecution

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue

private inductive Cut where
  | mmaEntry | query | scoresEntry | correctionEntry

private def Cut.floor : Cut → Nat
  | .mmaEntry => 1911
  | .query => 2141
  | .scoresEntry => 3104
  | .correctionEntry => 7748

private def respectsFloor (cut : Cut) (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
  match i.op with
  | .bra dst _ => decide (cut.floor ≤ dst)
  | .brx .. => false
  | _ => true

private theorem respectsFloorCode (cut : Cut) {pc : Nat} {i : Instr}
    (hPc : cut.floor ≤ pc) (hCode : kernel.code[pc]? = some i) :
    respectsFloor cut i = true := by
  have hAll : (kernel.code.drop cut.floor).all (respectsFloor cut) = true := by
    cases cut <;> set_option maxRecDepth 100000 in kernel_rfl
  have hAt : (kernel.code.drop cut.floor)[pc - cut.floor]? = some i := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hPc, hCode]
  exact List.all_eq_true.mp hAll i (List.mem_of_getElem? hAt)

private theorem segmentRespectsFloor (cut : Cut) {s u : TState} {se : SegMatch CuteSlot}
    (hPc : cut.floor ≤ s.pc) (hSite : s.pc ∈ Assumptions.swExp2Sites)
    (hm : cuteExp2.matchAt kernel s.pc = some se) (hu : Assumptions.execSwExp2 se s = .ok u) :
    cut.floor ≤ u.pc := by
  have hAll : Assumptions.swExp2Sites.all (fun pc =>
      if cut.floor ≤ pc then
        match cuteExp2.matchAt kernel pc with
        | none => false
        | some se => decide (cut.floor ≤ se.stop)
      else true) = true := by
    cases cut <;> set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll s.pc hSite
  rw [ite_eq_left hPc, hm] at h
  exact (Softmax.scoreSegmentFrame hu).1.symm ▸ of_decide_eq_true h

private theorem tauRespectsFloor (cut : Cut) {l : Launch} {g : Nat} {s u : TState}
    (hPc : cut.floor ≤ s.pc) (ht : Tau kernel Assumptions.all l g s u) :
    cut.floor ≤ u.pc := by
  obtain ⟨i, hc, _, hSource⟩ := Softmax.tauScoreSource ht
  rcases hSource with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
  · change cut.floor ≤ s.pc + 1
    omega
  · rcases Softmax.scoreExecLocal hLocal with hCore | ⟨se, hSite, hm, hu⟩
    · have hSafe := respectsFloorCode cut hPc hc
      simp only [respectsFloor, Bool.and_eq_true] at hSafe
      have hTarget := hSafe.2
      have he := hCore.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at he
      case bra dst uni =>
        rw [he]
        exact of_decide_eq_true (by simpa only [ho] using hTarget)
      case brx => simp [ho] at hTarget
      all_goals omega
    · exact segmentRespectsFloor cut hPc hSite hm hu

private theorem eventRespectsFloor (cut : Cut) {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (hPc : cut.floor ≤ s.pc)
    (he : EStep kernel Assumptions.all l g s e (some u)) : cut.floor ≤ u.pc := by
  obtain ⟨i, hCode, hl, hf⟩ := estep_event_source he
  have hSafe := respectsFloorCode cut hPc hCode
  simp only [respectsFloor, Bool.and_eq_true, hl, Bool.false_or] at hSafe
  have ho := hSafe.1
  rcases callbackFrame_fires (Epilogue.ordinaryEventFrame ho) hf with hn | hn <;> omega

private theorem runRespectsFloor (cut : Cut) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {o : Option TState} (hr : Run kernel Assumptions.all l g s es o)
    (hPc : cut.floor ≤ s.pc) :
    ∀ e ∈ es, cut.floor ≤ e.pc := by
  have localSteps {t u : TState} (hp : cut.floor ≤ t.pc)
      (ht : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) : cut.floor ≤ u.pc := by
    induction ht with
    | refl => exact hp
    | tail _ ht ih => exact tauRespectsFloor cut ih ht
  induction hr with
  | nil => simp
  | step ht he _ ih =>
    intro e hm
    have hs := localSteps hPc ht
    rcases List.mem_cons.mp hm with rfl | hTail
    · exact (estep_source_pc he).symm ▸ hs
    · exact ih (eventRespectsFloor cut hs he) e hTail
  | last ht he =>
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    exact (estep_source_pc he).symm ▸ localSteps hPc ht

private theorem laterEvents {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j : Nat} {e q : Event}
    (he : X.get (g, i) = some e) (hq : X.get (g, j) = some q) (hLt : i < j) :
    ∃ s u o, EStep kernel Assumptions.all l g s e (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) o ∧
      q ∈ (X.tr g).drop (i + 1) := by
  have hj := (List.getElem?_eq_some_iff.mp (show (X.tr g)[j]? = _ from hq)).1
  obtain ⟨o, hr⟩ := hX.thr _ (event_thread_lt hX he)
  have hi : i + 1 < (X.tr g).length := by omega
  obtain ⟨s, u, he, hRun⟩ := hr.after_event (show (X.tr g)[i]? = _ from he) hi
  refine ⟨s, u, o, he, hRun, List.mem_of_getElem? (i := j - (i + 1)) ?_⟩
  rw [List.getElem?_drop, Nat.add_sub_of_le (by omega : i + 1 ≤ j)]
  exact hq

private theorem laterQueryFloor {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j : Nat} {e q : Event}
    (he : X.get (g, i) = some e) (hq : X.get (g, j) = some q)
    (hPc : Cut.query.floor ≤ e.pc) (hLt : i < j) : Cut.query.floor ≤ q.pc := by
  obtain ⟨s, u, _, hStep, hRun, hMem⟩ := laterEvents hX he hq hLt
  have hs : Cut.query.floor ≤ s.pc := estep_source_pc hStep ▸ hPc
  exact runRespectsFloor .query hRun (eventRespectsFloor .query hs hStep) _ hMem

private theorem allocationSiteNotRepeated {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j pc : Nat}
    (hSite : pc ∈ PTX.Kernels.TmlFa4Fwd.Mma.allocationEntrySites)
    (he : X.IsBarrier (g, i) 2 (some 416) pc) (hq : X.IsBarrier (g, j) 2 (some 416) pc)
    (hLt : i < j) : False := by
  obtain ⟨s, u, _, hStep, hRun, hMem⟩ := laterEvents hX he hq hLt
  have hs : s.pc = pc := (estep_source_pc hStep).symm
  obtain ⟨ins, hc, _, hFire⟩ := estep_event_source hStep
  simp only [PTX.Kernels.TmlFa4Fwd.Mma.allocationEntrySites, List.mem_cons, List.not_mem_nil,
    or_false] at hSite
  have hSuffix (cut : Cut) (hPc : cut.floor = pc + 1) (hStep : u.pc = pc + 1) : False := by
    have hBound := runRespectsFloor cut hRun (hPc.trans hStep.symm).le _ hMem
    change cut.floor ≤ pc at hBound
    omega
  rcases hSite with rfl | rfl | rfl
  · rw [hs, Flow.code_1910] at hc
    obtain rfl := Option.some.inj hc
    exact hSuffix .mmaEntry rfl ((congrArg TState.pc (Option.some.inj hFire.2)).trans
      (by simp only [next, hs]))
  · rw [hs, Flow.code_3103] at hc
    obtain rfl := Option.some.inj hc
    exact hSuffix .scoresEntry rfl ((congrArg TState.pc (Option.some.inj hFire.2)).trans
      (by simp only [next, hs]))
  · rw [hs, Flow.code_7747] at hc
    obtain rfl := Option.some.inj hc
    exact hSuffix .correctionEntry rfl ((congrArg TState.pc (Option.some.inj hFire.2)).trans
      (by simp only [next, hs]))


variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem initialBarrierKey {g j pc key : Nat} (he : X.IsBarrier (g, j) 2 (some 416) pc)
    (hSite : pc ∈ PTX.Kernels.TmlFa4Fwd.Mma.allocationEntrySites) (hKey : CtaBarK l X (g, j) key)
    (hLength : j + 1 < (X.tr g).length) : key = 2 := by
  have hDone := CtaBarrier.first_generation_released_of_returned hX (by decide) he hLength
  have hRole := PTX.Kernels.TmlFa4Fwd.Mma.allocationEntryRole hp hX hSite he
  have hWarp : warpIndex l g < 13 := by
    rcases hRole with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> omega
  obtain ⟨k, pc', hSite', he', hKey'⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.allocationGenerationZeroMember hp hX (g := g) hKey.1 hWarp hDone
  have hRole' := PTX.Kernels.TmlFa4Fwd.Mma.allocationEntryRole hp hX hSite' he'
  have hPc : pc = pc' := by
    rcases hRole with ⟨hP, hW⟩ | ⟨hP, hW⟩ | ⟨hP, hLo, hHi⟩ <;>
      rcases hRole' with ⟨hP', hW'⟩ | ⟨hP', hW'⟩ | ⟨hP', hLo', hHi'⟩ <;> omega
  subst pc'
  have hEq : k = j := by
    rcases Nat.lt_trichotomy k j with h | h | h
    · exact (allocationSiteNotRepeated hX hSite he' he h).elim
    · exact h
    · exact (allocationSiteNotRepeated hX hSite he he' h).elim
  subst k
  exact CtaBarK.key_unique hX.ctaBar hKey hKey'

private theorem queryBarrierSender {e : EvId} {j key : Nat} (hBefore : e.2 < j)
    (he : Thread.Output.MmaAfterInput l X e) (hBar : CtaBarArrivalK l X (e.1, j) key) :
    key % 16 = 2 ∧ key ≠ 2 := by
  obtain ⟨hWarp, ev, hGet, hFloor⟩ := he
  obtain ⟨count, pc, mode, hArrival⟩ := hBar.2.1
  have hP := laterQueryFloor hX hGet hArrival hFloor hBefore
  change 2141 ≤ pc at hP
  have hLate : 173 < pc := by omega
  have hSites := actualNamedBarrier hp hX hArrival
  have hHint : pc ∉ registerHintSites := by
    have hDisjoint : namedBarrierSites.all (fun n => !registerHintSites.contains n) = true := by
      decide
    exact fun h => by
      have hNot := List.all_eq_true.mp hDisjoint _ hSites.1
      simp [h] at hNot
  have hRole : roleBodyPc (warpIndex l e.1) pc := roleBodyPcOfEvent hp hX hArrival hLate hHint
  rw [hWarp] at hRole
  have hPc : pc = 2764 := by
    simp [roleBodyPc] at hRole
    have hs := hSites.1
    simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hs
    omega
  have hCount : count = some 416 := by simpa [hPc, namedBarrierCount] using hSites.2.1
  refine ⟨hSites.2.2.2.2.2.2 hCount, ?_⟩
  intro hKey
  subst key
  obtain ⟨n, hN, entry, _, hEntry⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.allocationEntryBeforeBarrier hp hX hArrival (by simp [hPc,
      PTX.Kernels.TmlFa4Fwd.Mma.allocationEntrySites])
  exact CtaBarrier.not_generationZero_after_sync hX (by decide) hN hEntry (by simpa using hBar.2.2)

/-- A returned noninitial rendezvous of allocation barrier 2 leaves only the MMA warp. -/
theorem afterNoninitialAllocationBarrier {f : EvId} {j key : Nat} (hId : key % 16 = 2)
    (hKey : key ≠ 2) (hBar : CtaBarK l X (f.1, j) key) (hBefore : j < f.2)
    (hLen : f.2 < (X.tr f.1).length) : Thread.Output.MmaAfterInput l X f := by
  obtain ⟨count, pc, hs⟩ := hBar.2.1
  have hSync : X.get (f.1, j) = some ⟨pc, .bar 2 count .sync⟩ := by
    simpa only [Execution.IsBarrier, hId] using hs
  have hCount := actualNamedBarrierCountById hp hX hSync
  have hCount' : count = some 416 := by simpa [countOfBarrierId] using hCount
  have hNamed := actualNamedBarrier hp hX hSync
  have hSite : pc ∈ PTX.Kernels.TmlFa4Fwd.Mma.allocationEntrySites ∨ pc = 2764 := by
    have hTable : namedBarrierSites.all (fun n =>
        if namedBarrierCount n = some 416 ∧ namedBarrierMode n = .sync then
          PTX.Kernels.TmlFa4Fwd.Mma.allocationEntrySites.contains n || n == 2764 else true) =
        true := by decide
    have h := List.all_eq_true.mp hTable _ hNamed.1
    simpa [← hNamed.2.1, ← hNamed.2.2.1, hCount'] using h
  rcases hSite with he | rfl
  · exact (hKey (initialBarrierKey hp hX (hCount' ▸ hSync) he hBar (by omega))).elim
  have hWarp := roleBodyPcOfEvent hp hX hSync (show 173 < 2764 by decide)
    (show 2764 ∉ registerHintSites by decide)
  change roleBodyPc (warpIndex l f.1) 2764 at hWarp
  have hMma : warpIndex l f.1 = 12 := by
    rcases hWarp with ht | ht
    · omega
    · split_ifs at ht <;> omega
  have hq : X.get f = some (X.tr f.1)[f.2] := List.getElem?_eq_getElem hLen
  exact ⟨hMma, _, hq, laterQueryFloor hX hSync hq (show Cut.query.floor ≤ 2764 by decide) hBefore⟩

private theorem noMmaArrive {i : EvId} (hWarp : warpIndex l i.1 = 12) {target : Loc}
    {tx count : Nat} {scope : MbarScope} (hArrive : X.Arrive i target tx count true scope)
    : False := by
  obtain ⟨pc, he⟩ := hArrive
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hCode, hFire⟩
  · cases hBad
  obtain ⟨_, _, _, _, _, _, _, hOp, _⟩ := fires_arrive_flags hFire rfl
  let sites := [686, 711, 737, 763, 1153, 1182, 1368, 1900, 2983, 2985,
    3590, 4847, 4867, 5278, 6532, 6552, 7437, 7457, 7752, 7754, 7987, 8223, 8224,
    8442, 8443, 8464, 8468, 8759, 8760, 8764, 9055, 9056]
  have hSites : OpPcsFast kernel.code arriveOp sites = true := by decide +kernel
  have hSite := OpPcsFast.mem hSites hCode (show arriveOp ins.op = true by rw [hOp]; rfl)
  simp only [sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hRole : roleBodyPc (warpIndex l i.1) pc :=
    roleBodyPcOfEvent hp hX he (show 173 < pc by omega) (by
      change pc ∉ registerHintSites
      simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
      omega)
  rw [hWarp] at hRole
  simp [roleBodyPc] at hRole
  omega

omit hp hX in
private def warpBarrierOp : Op → Bool
  | .warp w =>
    match w.kind with
    | .barWarp => true
    | _ => false
  | _ => false

private theorem noMmaWarpBar {i : EvId} (hWarp : warpIndex l i.1 = 12) {mask inst : Nat}
    (hBar : X.WarpBar i mask inst) : False := by
  obtain ⟨pc, he⟩ := hBar
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hCode, hFire⟩
  · cases hBad
  have hop : warpBarrierOp ins.op = true := by
    cases h : warpBarrierOp ins.op
    · have hNot (w : WarpInstr) (he : ins.op = .warp w) (hk : w.kind = .barWarp) : False := by
        simp [he, warpBarrierOp, hk] at h
      exact (fires_notWarpBar_op hNot hFire mask inst rfl).elim
    · rfl
  let sites := [4858, 6543, 7448]
  have hSites : OpPcsFast kernel.code warpBarrierOp sites = true := by decide +kernel
  have hSite := OpPcsFast.mem hSites hCode hop
  simp only [sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hRole : roleBodyPc (warpIndex l i.1) pc :=
    roleBodyPcOfEvent hp hX he (show 173 < pc by omega) (by
      change pc ∉ registerHintSites
      simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
      omega)
  rw [hWarp] at hRole
  simp [roleBodyPc] at hRole
  omega

/-- After the query acquire, ordinary base-causality edges stay within the MMA warp. -/
theorem staysInMmaAfterQuery {i f : EvId} (hInit : Thread.Output.MmaAfterInput l X i)
    (hCause : baseCausality l X i f) : warpIndex l f.1 = 12 := by
  have close {a b : EvId} (ha : Thread.Output.MmaAfterInput l X a)
      (hb : po X a b ∨ CtaBarSync l X a b ∨ MSync l X a b ∨ ClusterSync l X a b ∨
        WarpBarSync l X a b ∨ synchronizesWith l X a b ∨ FenceSync l X a b) :
      Thread.Output.MmaAfterInput l X b := by
    rcases hb with h | h | h | h | h | h | h
    · obtain ⟨hTh, hLt, hLen, _⟩ := h
      obtain ⟨hw, e, he, hPc⟩ := ha
      have hGet : X.get b = some (X.tr b.1)[b.2] := List.getElem?_eq_getElem hLen
      refine ⟨hTh ▸ hw, _, hGet, ?_⟩
      have hq : X.get (a.1, b.2) = some (X.tr b.1)[b.2] := hTh.symm ▸ hGet
      exact laterQueryFloor hX he hq hPc hLt
    · obtain ⟨_, key, u, v, hA, hB, hU, hV, hLen⟩ := h
      obtain ⟨hId, hKey⟩ := queryBarrierSender hp hX hU ha hA
      exact afterNoninitialAllocationBarrier hp hX hId hKey hB hV hLen
    · obtain ⟨x, _, _, _, _, hRel, _, _, _, _, _, hx, _⟩ := h
      obtain ⟨tx, count, hArr⟩ := hRel
      exact (noMmaArrive hp hX (hx.symm ▸ ha.1) hArr).elim
    · obtain ⟨_, _, _, hSync, _⟩ := h
      obtain ⟨_, hArrival, _⟩ := hSync
      obtain ⟨pc, aligned, hGet⟩ := hX.cluster.arrival_present hArrival
      exact (noClusterEvent hX hGet).elim
    · obtain ⟨j, _, hPair, _⟩ := h
      obtain ⟨_, mask, inst, hEvent, _⟩ := hPair
      exact (noMmaWarpBar hp hX (i := (a.1, j)) ha.1 hEvent).elim
    · exact (noSynchronizesWith_of (fun _ _ _ _ he => noReleasingStore hX he)
        (fun _ _ _ _ _ he => (noAtomicEvent hX he).elim) _ _ h).elim
    · exact (not_fenceSync_of_noFence (fun _ _ _ => noThreadFence hX) _ _ h).elim
  have hEnd : Thread.Output.MmaAfterInput l X f := by
    induction hCause with
    | single h => exact close hInit h
    | tail _ h ih => exact close ih h
  exact hEnd.1

end PTX.Kernels.TmlFa4Fwd.Thread.Mma


namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX

/-- A write performed by a different role cannot acquire the query DMA bytes through
ordinary model causality. -/
theorem queryLoadNotBeforeNonMma {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load writer : EvId} {addr cta x y k : Nat} {spec : TensorCopy.Spec} {stage : Fin 2}
    {loc : Loc} (hIssue : X.TensorIssue load addr spec)
    (hObject : spec.mbar = queryObject l cta stage)
    (hWriter : Prologue.warpIndex l writer.1 ≠ 12) :
    ¬ modelCausality l X loc (.async load (.write (.load x y k))) (.thread writer) := by
  rintro ⟨_, _, hFinished, hBefore⟩
  exact hWriter (Thread.Mma.staysInMmaAfterQuery hp hX
    (queryLoadFinishedMmaAfterInput hp hX hIssue hObject hFinished)
    (observedCompletionBefore_baseCausality hBefore))

end PTX.Kernels.TmlFa4Fwd.Thread.Output
