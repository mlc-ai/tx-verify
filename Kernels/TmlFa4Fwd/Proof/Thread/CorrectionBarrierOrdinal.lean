-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BarrierOrdinals
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsRank
import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierTerminal
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierExit
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Prologue

private theorem correctionBarrierSuffix {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {o : Option TState}
    (hs : 7755 ≤ s.pc) (hr : Run kernel Assumptions.all l g s events o) :
    ∀ e ∈ events, 7755 ≤ e.pc := by
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
  apply eventTailEventsOfSegmentFloor (floor := 7755) (by decide +kernel) _ hWalk hs
  intro site hLo hSite seg hMatch
  simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
  omega

private theorem countBarPartition {a b : Nat} (hNe : a ≠ b) {events : List Event}
    (hBars : ∀ e ∈ events, Execution.isBar e = true →
      Execution.isBarId a e = true ∨ Execution.isBarId b e = true) :
    events.countP Execution.isBar =
      events.countP (Execution.isBarId a) + events.countP (Execution.isBarId b) := by
  induction events with
  | nil => rfl
  | cons e es ih =>
    have hTail := ih (fun q h => hBars q (List.mem_cons_of_mem _ h))
    rw [List.countP_cons, List.countP_cons, List.countP_cons, hTail]
    obtain ⟨site, kind⟩ := e
    cases kind <;> simp only [Execution.isBar, Execution.isBarId, Bool.false_eq_true,
      ite_false, Nat.add_zero]
    case bar id count mode =>
      have hEither := hBars ⟨site, .bar id count mode⟩ (List.mem_cons_self) rfl
      simp only [Execution.isBarId, beq_iff_eq] at hEither
      rcases hEither with rfl | rfl
      · simp [hNe, Nat.add_right_comm]
      · simp [Ne.symm hNe, Nat.add_assoc]

private theorem takeBarrierEvent {X : Execution} {g pos : Nat} {e : Event}
    (he : X.get (g,pos) = some e) :
    (X.tr g).take (pos + 1) = (X.tr g).take pos ++ [e] := by
  obtain ⟨hlen, hGet⟩ := List.getElem?_eq_some_iff.mp he
  rw [List.take_succ_eq_append_getElem hlen, hGet]

section
variable {l : Launch} {m : Mem0} {X : Execution} {p : Params} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) {inst : Nat}
    (h3 : X.get (g,3) = some ⟨172,.fenceMbarInit⟩) (h4 : X.get (g,4) = some ⟨173,.bar 0 none .sync⟩)
    (h5 : X.get (g,5) = some ⟨7746,.setMaxReg false 64 inst⟩)
include hp hX hg h3 h4 h5

private theorem correctionStartupBarrierCounts :
    ((X.tr g).take 6).countP Execution.isBar = 1 ∧
      ∀ stage : Fin 2,
        ((X.tr g).take 6).countP (Execution.isBarId (Correction.statsBarrierId l g stage)) = 0 := by
  have hLen : 5 < (X.tr g).length := len_of_get h5
  let e₀ := (X.tr g)[0]'(by omega)
  let e₁ := (X.tr g)[1]'(by omega)
  let e₂ := (X.tr g)[2]'(by omega)
  have h0 : X.get (g,0) = some e₀ :=
    List.getElem?_eq_getElem (show 0 < (X.tr g).length by omega)
  have h1 : X.get (g,1) = some e₁ :=
    List.getElem?_eq_getElem (show 1 < (X.tr g).length by omega)
  have h2 : X.get (g,2) = some e₂ :=
    List.getElem?_eq_getElem (show 2 < (X.tr g).length by omega)
  rw [takeBarrierEvent h5, takeBarrierEvent h4, takeBarrierEvent h3, takeBarrierEvent h2,
    takeBarrierEvent h1, takeBarrierEvent h0,
    firstSharedValue hp hX g hg h0, secondWarpValue hp hX g hg h1, thirdWarpValue hp hX g hg h2]
  refine ⟨rfl, ?_⟩
  intro stage
  have hZero : 0 ≠ Correction.statsBarrierId l g stage := by unfold Correction.statsBarrierId; omega
  simp [Execution.isBarId, hZero]

private theorem correctionEntryBarrierCounts
    (h6 : X.get (g,6) = some ⟨7747,.bar 2 (some 416) .sync⟩)
    (h7 : X.get (g,7) = some ⟨7752,.arrive (Correction.creditLoc l g 0) 0 1 true .cta⟩)
    (h8 : X.get (g,8) = some ⟨7754,.arrive (Correction.creditLoc l g 1) 0 1 true .cta⟩) :
    ((X.tr g).take 9).countP Execution.isBar = 2 ∧
      ∀ stage : Fin 2,
        ((X.tr g).take 9).countP (Execution.isBarId (Correction.statsBarrierId l g stage)) = 0 := by
  obtain ⟨hStartup, hStage⟩ := correctionStartupBarrierCounts hp hX hg h3 h4 h5
  rw [takeBarrierEvent h8, takeBarrierEvent h7, takeBarrierEvent h6]
  refine ⟨?_, ?_⟩
  · rw [List.countP_append, List.countP_append, List.countP_append, hStartup]
    rfl
  · intro stage
    have hAlloc : 2 ≠ Correction.statsBarrierId l g stage := by
      unfold Correction.statsBarrierId
      omega
    rw [List.countP_append, List.countP_append, List.countP_append, hStage]
    simp [Execution.isBarId, hAlloc]
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- At a correction statistics wait, the CTA barrier ordinal counts startup,
allocation and the completed waits of both stages. -/
theorem correctionStatsBarrierCount {i : EvId} {round : CorrectionRound} {stage : Fin 2}
    (hWait : CorrectionWaits X i round stage) :
    barrierOrdinal X i = 2 +
      2 * (correctionBefore X i).barrier (Correction.statsBarrierId l i.1 stage) + stage.val := by
  obtain ⟨g,j⟩ := i
  have hStage := correctionStatsStageBalance hp hX hWait
  obtain ⟨target, hGet, hAct⟩ := hWait
  have hg := event_thread_lt hX hGet
  have hRange := correctionStatsWaitSiteBounds hAct
  have hLate : 7754 < target.pc := by omega
  obtain ⟨t,o,inst,ht,h3,h4,h5,h6,h7,h8,hr,hj⟩ :=
    Correction.correctionEntryBeforeEvent hp hX hg hStage.1.1 hStage.1.2 hGet (.inl hLate)
  obtain ⟨hEarly, hEarlyStage⟩ := correctionEntryBarrierCounts hp hX hg h3 h4 h5 h6 h7 h8
  let history := (X.tr g).take j
  let rest := history.drop 9
  let a := Correction.statsBarrierId l g 0
  let b := Correction.statsBarrierId l g 1
  have hSplit : ((X.tr g).take 9) ++ rest = history := by
    have ht : history.take 9 = (X.tr g).take 9 := by
      dsimp [history]
      rw [List.take_take, Nat.min_eq_left hj]
    rw [← ht, List.take_append_drop]
  have hNe : a ≠ b := by dsimp [a, b, Correction.statsBarrierId]; omega
  have hTail : ∀ e ∈ rest, Execution.isBar e = true →
      Execution.isBarId a e = true ∨ Execution.isBarId b e = true := by
    intro e hm hBar
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    have hBound := (List.getElem?_eq_some_iff.mp hk).1
    have hPos : k + 9 < j := by
      simp only [rest, history, List.length_drop, List.length_take] at hBound
      omega
    have he : X.get (g,k + 9) = some e := by
      dsimp only [rest, history] at hk
      rw [List.getElem?_drop, List.getElem?_take_of_lt (by omega : 9 + k < j)] at hk
      simpa only [Nat.add_comm, Execution.get] using hk
    have hRest : ((X.tr g).drop 9)[k]? = some e := by
      rw [List.getElem?_drop, Nat.add_comm]
      exact he
    have hLo := correctionBarrierSuffix ht.1.ge hr _ (List.mem_of_getElem? hRest)
    obtain ⟨site, kind⟩ := e
    cases kind <;> simp only [Execution.isBar, Bool.false_eq_true] at hBar
    case bar id count mode =>
      obtain ⟨hSite, hCount, hMode, _, _, _, hTwo⟩ := actualNamedBarrier hp hX he
      have hAudit : namedBarrierSites.all (fun s => decide (7755 ≤ s →
          s ∈ Correction.correctionStatsSites 0 ∨ s ∈ Correction.correctionStatsSites 1 ∨
          s = 9204)) = true := by decide +kernel
      have hWhich := (of_decide_eq_true (List.all_eq_true.mp hAudit site hSite))
        (show 7755 ≤ site from hLo)
      rcases hWhich with h0 | h1 | rfl
      · have hId := Correction.actualCorrectionStatsBarrierId hp hX 0 h0 he
        exact .inl (by simpa [Execution.isBarId, a] using hId)
      · have hId := Correction.actualCorrectionStatsBarrierId hp hX 1 h1 he
        exact .inr (by simpa [Execution.isBarId, b] using hId)
      · have hi : id = 2 := hTwo hCount
        subst id
        have hM : mode = .arrive := hMode
        subst mode
        rcases finalArrivalTerminates hp hX ⟨_, he, rfl⟩ hPos hGet with hExit | ⟨_, hFault⟩
        · rw [correctionStatsWait hp hX hGet hAct] at hExit
          cases hExit
        · rw [correctionStatsWait hp hX hGet hAct] at hFault
          cases hFault
  have hPartition := countBarPartition hNe hTail
  have h0 := hEarlyStage 0
  have h1 := hEarlyStage 1
  change ((X.tr g).take 9).countP (Execution.isBarId a) = 0 at h0
  change ((X.tr g).take 9).countP (Execution.isBarId b) = 0 at h1
  have hCount (tag : Fin 2) :
      (correctionBefore X (g,j)).barrier (Correction.statsBarrierId l g tag) =
        rest.countP (Execution.isBarId (Correction.statsBarrierId l g tag)) := by
    rw [correctionBarrierOrdinal]
    change history.countP _ = _
    rw [← hSplit, List.countP_append, hEarlyStage tag, Nat.zero_add]
  change history.countP Execution.isBar = _
  rw [← hSplit, List.countP_append, hEarly, hPartition]
  rw [← hCount (tag := 0), ← hCount (tag := 1)]
  have hh : (correctionBefore X (g,j)).barrier (Correction.statsBarrierId l g 0) =
      (correctionBefore X (g,j)).barrier (Correction.statsBarrierId l g 1) + stage.val := hStage.2
  have hVal : stage.val = 0 ∨ stage.val = 1 := by have := stage.isLt; omega
  rcases hVal with h | h
  · obtain rfl : stage = 0 := Fin.ext h
    simp only [Fin.val_zero, Nat.add_zero] at hh ⊢
    omega
  · obtain rfl : stage = 1 := Fin.ext h
    simp only [Fin.val_one] at hh ⊢
    omega

/-- The ordinal of any correction statistics wait determines its stage. -/
theorem correctionStatsBarrierOrdinal {i : EvId} {round : CorrectionRound} {stage : Fin 2}
    (hWait : CorrectionWaits X i round stage) : barrierOrdinal X i % 2 = stage.val := by
  rw [correctionStatsBarrierCount hp hX hWait]
  have := stage.isLt
  omega

omit hp hX in
private theorem afterCorrectionAllocation {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {o : Option TState}
    (hs : 7748 ≤ s.pc) (hr : Run kernel Assumptions.all l g s events o) :
    ∀ e ∈ events, 7748 ≤ e.pc := by
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
  apply eventTailEventsOfSegmentFloor (floor := 7748) (by decide +kernel) _ hWalk hs
  intro site hLo hSite seg hMatch
  simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
  omega

/-- The correction allocation handshake has ordinal one. The other named arrival on
the same allocation barrier is the terminal observation. -/
theorem BarrierArrival.correctionAllocation {g j : Nat} {count : Option Nat} {mode : BarMode}
    (hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (h : BarrierArrival X (g,j) 2 count mode) :
    (mode = .sync ∧ barrierOrdinal X (g,j) = 1) ∨
      (mode = .arrive ∧ FinalAllocationArrival X (g,j) .arrive ∧ 1 < barrierOrdinal X (g,j)) := by
  obtain ⟨⟨site, _⟩, he, rfl⟩ := h
  obtain ⟨hSites, _, hMode, _, _, hZero, _⟩ := actualNamedBarrier hp hX he
  have hCount : count = some 416 := actualNamedBarrierCountById hp hX he
  obtain rfl := hCount
  have hCommon : site ≠ 173 := fun h => (by decide : (2 : Nat) ≠ 0) (hZero h)
  have hLate : 173 < site := by
    simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSites
    omega
  have hNotHint : site ∉ registerHintSites := by
    have audit : namedBarrierSites.all (fun s => !(registerHintSites.contains s)) = true := by
      decide +kernel
    simpa using List.all_eq_true.mp audit site hSites
  have hRole := roleBodyPcOfEvent hp hX he hLate hNotHint
  have hRegion : 7747 ≤ site := by
    change roleBodyPc (warpIndex l g) site at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  have hCnt := (actualNamedBarrier hp hX he).2.1
  have hCheck : namedBarrierSites.all (fun s => decide (7747 ≤ s →
      namedBarrierCount s = some 416 → s = 7747 ∨ s = 9204)) = true := by decide +kernel
  have hClass := (of_decide_eq_true (List.all_eq_true.mp hCheck site hSites)) hRegion hCnt.symm
  obtain ⟨t, o, inst, hj, ht, h3, h4, h5, h6, hr⟩ :=
    Correction.correctionEntryRendezvous hp hX hWarp.1 hWarp.2 he hLate
  have hFirst := (correctionStartupBarrierCounts hp hX (event_thread_lt hX he) h3 h4 h5).1
  rcases hClass with rfl | rfl
  · have hExact : j = 6 := by
      by_contra! h
      have hIdx : ((X.tr g).drop 7)[j - 7]? = some ⟨7747, .bar 2 (some 416) mode⟩ := by
        rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
        exact he
      have hFloor := afterCorrectionAllocation ht.ge hr _ (List.mem_of_getElem? hIdx)
      change 7748 ≤ 7747 at hFloor
      omega
    exact .inl ⟨hMode, hExact.symm ▸ hFirst⟩
  · have hDiff : j ≠ 6 := by
      rintro rfl
      rw [he] at h6
      cases h6
    have hAfter : 7 ≤ j := by omega
    have hStep := countP_take_succ (p := Execution.isBar) h6 rfl
    have hMono := countP_take_mono Execution.isBar (X.tr g) hAfter
    rw [hStep, hFirst] at hMono
    have hM : mode = .arrive := hMode
    have hFinal : X.get (g,j) = some ⟨9204,.bar 2 (some 416) .arrive⟩ := hM ▸ he
    exact .inr ⟨hM, FinalAllocationArrival.of_decoded (by decide) hFinal, hMono⟩

/-- A correction lane's nonallocation named barrier is a synchronous statistics wait. -/
theorem BarrierArrival.correctionStatistics {i : EvId} {id : Nat} {count : Option Nat}
    {mode : BarMode} (he : BarrierArrival X i id count mode)
    (hWarp : 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12) (hNamed : id ≠ 0) (hAlloc : id ≠ 2) :
    ∃ stage round, CorrectionWaits X i round stage ∧
      id = Correction.statsBarrierId l i.1 stage ∧ mode = .sync := by
  obtain ⟨⟨site, _⟩, hGet, rfl⟩ := he
  obtain ⟨hSite, hCount, hMode, _, _, hZero, hTwo⟩ := actualNamedBarrier hp hX hGet
  have hCommon : site ≠ 173 := fun h => hNamed (hZero h)
  have hLate : 173 < site := by
    simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
    omega
  have hNotHint : site ∉ registerHintSites := by
    have tab : namedBarrierSites.all (fun site => !(registerHintSites.contains site)) = true := by
      decide +kernel
    simpa using List.all_eq_true.mp tab site hSite
  have hRole := roleBodyPcOfEvent hp hX hGet hLate hNotHint
  have hRegion : 7747 ≤ site := by
    change roleBodyPc (warpIndex l i.1) site at hRole
    unfold roleBodyPc at hRole
    rcases hRole with hEq | hRole
    · omega
    · split_ifs at hRole <;> omega
  have hNoAlloc : namedBarrierCount site ≠ some 416 :=
    fun h => hAlloc (hTwo (hCount.trans h))
  have tab : namedBarrierSites.all (fun site => decide (7747 ≤ site →
      namedBarrierCount site ≠ some 416 → namedBarrierMode site = .sync ∧
      (site ∈ Correction.correctionStatsSites 0 ∨ site ∈ Correction.correctionStatsSites 1))) =
      true := by decide +kernel
  have hInfo := (of_decide_eq_true (List.all_eq_true.mp tab site hSite)) hRegion hNoAlloc
  have hM : mode = .sync := hMode.trans hInfo.1
  have hGetSync : X.get i = some ⟨site, .bar id count .sync⟩ := hM ▸ hGet
  have hId : ∃ stage, id = Correction.statsBarrierId l i.1 stage := by
    obtain ⟨g, j⟩ := i
    rcases hInfo.2 with h | h
    · exact ⟨0, Correction.actualCorrectionStatsBarrierId hp hX 0 h hGetSync⟩
    · exact ⟨1, Correction.actualCorrectionStatsBarrierId hp hX 1 h hGetSync⟩
  obtain ⟨st, hId⟩ := hId
  have hRange : 3 ≤ id ∧ id < 11 := by
    rw [hId]
    unfold Correction.statsBarrierId
    have := st.isLt
    omega
  obtain ⟨stage, round, hWait, hId'⟩ :=
    correctionWaitOfStatisticsSync hp hX hRange ⟨_, hGetSync, rfl⟩
  exact ⟨stage, round, hWait, hId', hM⟩

/-- Two correction statistics waits in one warp at the same CTA barrier ordinal
have identical rendezvous identities. -/
theorem correctionStatisticsAgree {i j : EvId} {ri rj : CorrectionRound} {st ti : Fin 2}
    (hi : CorrectionWaits X i ri st) (hj : CorrectionWaits X j rj ti) (hWarp : SameWarp l i.1 j.1)
    (hOrdinal : barrierOrdinal X i = barrierOrdinal X j) :
    Correction.statsBarrierId l i.1 st = Correction.statsBarrierId l j.1 ti := by
  have hSt := correctionStatsBarrierOrdinal hp hX hi
  have hTi := correctionStatsBarrierOrdinal hp hX hj
  have hEq : st = ti := Fin.ext (hSt.symm.trans (hOrdinal ▸ hTi))
  subst ti
  unfold Correction.statsBarrierId warpIndex
  rw [hWarp.2]

end PTX.Kernels.TmlFa4Fwd.Thread
