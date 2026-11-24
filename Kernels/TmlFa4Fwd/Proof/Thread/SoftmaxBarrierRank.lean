-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRendezvous
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank
import Kernels.TmlFa4Fwd.Proof.SoftmaxExitPublications
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxMetadataReads
import Kernels.TmlFa4Fwd.Proof.Termination
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence
import all Kernels.TmlFa4Fwd.Proof.Thread.AlignedBarrierCases
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import all Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierOrder
import Lemmas.Flow.EventCont
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue Softmax Epilogue

private def softmaxBarrierSites : List Nat :=
  [173, 3103, 3583, 4397, 5271, 5683, 6891, 7616, 7741]

private theorem countBarrierSites (events : List Event) {sites : List Nat}
    (hDistinct : sites.Nodup) :
    events.countP (fun e => sites.contains e.pc) =
      (sites.map (fun site => events.countP (barrierMark site))).sum := by
  induction sites with
  | nil => simp
  | cons site rest ih =>
    obtain ⟨hNot, hTail⟩ := List.nodup_cons.mp hDistinct
    have hOr : (fun (e : Event) => (site :: rest).contains e.pc) =
        fun e => barrierMark site e || rest.contains e.pc := by
      funext e
      by_cases h : e.pc = site <;> simp [barrierMark, h]
    rw [hOr, countP_or_disj, ih hTail, List.map_cons, List.sum_cons]
    intro e _ hBoth
    have hSite : e.pc = site := beq_iff_eq.mp hBoth.1
    exact hNot (hSite ▸ List.contains_iff_mem.mp hBoth.2)

private theorem softmaxBarrierMarker {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} {e : Event} (hw : warpIndex l g < 8)
    (he : X.get (g,pos) = some e) (hNext : pos + 1 < (X.tr g).length) :
    Execution.isBar e = softmaxBarrierSites.contains e.pc := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨site, kind⟩ := e
    cases kind <;> try cases h
    rename_i id count mode
    have hSites := softmaxBarrierStation hp hX hw he
    change softmaxBarrierSites.contains site = true
    simpa [softmaxBarrierSites, softmaxStatsSites, List.contains_iff_mem, or_assoc,
      or_left_comm, or_comm] using hSites
  · intro h
    obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
    obtain ⟨s,u,hEv,hTail⟩ := hr.after_event he hNext
    have hTable : softmaxBarrierSites.all (fun site =>
        (kernel.code[site]?).any (fun i => barOp i.op)) = true := by decide +kernel
    have hOp := List.all_eq_true.mp hTable e.pc (List.contains_iff_mem.mp h)
    cases hc : kernel.code[e.pc]? with
    | none => simp [hc] at hOp
    | some ins =>
      simp only [hc, Option.any_some] at hOp
      obtain ⟨_, id, count, mode, hKind⟩ :=
        markedBarrierContinues (estep_source_pc hEv).symm hc hOp hEv
      obtain ⟨site, kind⟩ := e
      change kind = _ at hKind
      subst kind
      rfl

/-- The lane's work rendezvous ordinal counts precisely the occurrences of the decoded
named barrier stations in its earlier trace. -/
theorem softmaxBarrierOrdinalOfStations {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (hw : warpIndex l g < 8) (he : X.get (g,j) = some e) :
    let trace := (X.tr g).take j
    barrierOrdinal X (g,j) =
      trace.countP (barrierMark 173) + trace.countP (barrierMark 3103) +
      trace.countP (barrierMark 3583) + trace.countP (barrierMark 4397) +
      trace.countP (barrierMark 5271) + trace.countP (barrierMark 5683) +
      trace.countP (barrierMark 6891) + trace.countP (barrierMark 7616) +
      trace.countP (barrierMark 7741) := by
  let trace := (X.tr g).take j
  have hCount : trace.countP Execution.isBar =
      trace.countP (fun e => softmaxBarrierSites.contains e.pc) := by
    apply List.countP_congr
    intro prior hPrior
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hPrior
    have hBound := (List.getElem?_eq_some_iff.mp hi).1
    change i < ((X.tr g).take j).length at hBound
    have hij : i < j := hBound.trans_le (List.length_take_le ..)
    rw [show trace = (X.tr g).take j from rfl, List.getElem?_take_of_lt hij] at hi
    have hLen : j < (X.tr g).length := len_of_get he
    exact Bool.eq_iff_iff.mp (softmaxBarrierMarker hp hX hw hi (by omega))
  have ha := countBarrierSites trace (sites := softmaxBarrierSites) (by decide)
  change trace.countP Execution.isBar = _
  rw [hCount,ha]
  simp only [trace, softmaxBarrierSites, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private def softmaxBarrierFloors : List Nat :=
  [174, 3104, 3584, 4398, 5006, 6654, 7605, 7617, 7741, 7742]

private theorem softmaxBarrierBranchFloor {floor : Nat} (hFloor : floor ∈ softmaxBarrierFloors) :
    (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true := by
  have hTable : softmaxBarrierFloors.all (fun n =>
      (kernel.code.drop n).all (fun i => staysPastEvent n i.op)) = true := by decide +kernel
  exact List.all_eq_true.mp hTable floor hFloor

private theorem softmaxBarrierSegmentFloor {floor : Nat} (hFloor : floor ∈ softmaxBarrierFloors)
    (site : Nat) (hSite : floor ≤ site) (hMem : site ∈ Assumptions.swExp2Sites)
    (seg : SegMatch CuteSlot) (hMatch : cuteExp2.matchAt kernel site = some seg) :
    floor ≤ seg.stop := by
  have hTable : softmaxBarrierFloors.all (fun floor =>
      Assumptions.swExp2Sites.all (fun site => if floor ≤ site then
        (cuteExp2.matchAt kernel site).any (fun seg => decide (floor ≤ seg.stop))
      else true)) = true := by decide +kernel
  have h := List.all_eq_true.mp (List.all_eq_true.mp hTable _ hFloor) _ hMem
  simpa only [ite_eq_left hSite, hMatch, Option.any_some, decide_eq_true_eq] using h

section
variable {l : Launch} {m : Mem0} {X : Execution}

private theorem barrierRankBeforeFloor (hX : Consistent l kernel Assumptions.all m X)
    {g j floor site : Nat} {e : Event} (hFloor : floor ∈ softmaxBarrierFloors)
    (he : X.get (g,j) = some e) (hBelow : e.pc < floor) (hAbove : floor ≤ site) :
    ((X.tr g).take j).countP (barrierMark site) = 0 := by
  apply List.countP_eq_zero.mpr
  intro before hm hMark
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hij := (List.getElem?_eq_some_iff.mp hi).1.trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hij] at hi
  have hSite : before.pc = site := beq_iff_eq.mp hMark
  have hOrder := traceOrderOfSegmentFloor hX (softmaxBarrierBranchFloor hFloor)
    (softmaxBarrierSegmentFloor hFloor) he hi hBelow (hSite.symm ▸ hAbove)
  omega

private theorem barrierRankAfterFloor (hX : Consistent l kernel Assumptions.all m X)
    {g j floor site : Nat} {e : Event} (hFloor : floor ∈ softmaxBarrierFloors)
    (he : X.get (g,j) = some e) (hBelow : site < floor) (hAbove : floor ≤ e.pc) :
    ((X.tr g).take j).countP (barrierMark site) = (X.tr g).countP (barrierMark site) := by
  have hNone : ((X.tr g).drop j).countP (barrierMark site) = 0 := by
    apply List.countP_eq_zero.mpr
    intro after hm hMark
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    rw [List.getElem?_drop] at hi
    have hSite : after.pc = site := beq_iff_eq.mp hMark
    have hOrder := traceOrderOfSegmentFloor hX (softmaxBarrierBranchFloor hFloor)
      (softmaxBarrierSegmentFloor hFloor) hi he (hSite.symm ▸ hBelow) hAbove
    omega
  have hSplit := congrArg (List.countP (barrierMark site))
    (List.take_append_drop j (X.tr g))
  simpa only [List.countP_append, hNone, Nat.add_zero] using hSplit

private theorem earlierBarrierMarkUnique (hX : Consistent l kernel Assumptions.all m X)
    {g i j site : Nat} {first last : Event} (hi : X.get (g,i) = some first)
    (hj : X.get (g,j) = some last) (hFirst : first.pc = site) (hLast : last.pc = site)
    (hSite : site ∈ softmaxBarrierSites) (hFloor : site + 1 ∈ softmaxBarrierFloors) : i = j := by
  have noLater {a b : Nat} {f e : Event} (hEarly : X.get (g,a) = some f)
      (hLate : X.get (g,b) = some e) (hFrom : f.pc = site) (hTo : e.pc = site)
      (hLt : a < b) : False := by
    have hLen : b < (X.tr g).length := len_of_get hLate
    obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX hEarly)
    obtain ⟨s,u,hE,hRun⟩ := hr.after_event hEarly (by omega : a + 1 < (X.tr g).length)
    have hTable : softmaxBarrierSites.all (fun site =>
        (kernel.code[site]?).any (fun i => barOp i.op)) = true := by decide +kernel
    have hOp := List.all_eq_true.mp hTable site hSite
    cases hc : kernel.code[site]? with
    | none => simp [hc] at hOp
    | some ins =>
      simp only [hc, Option.any_some] at hOp
      have hSource := (estep_source_pc hE).symm.trans hFrom
      have hu := (markedBarrierContinues hSource hc hOp hE).1
      have hUp : site + 1 ≤ u.pc := by omega
      obtain ⟨_, hw⟩ := Mma.walkFromRun hRun
      have hLater : e ∈ (X.tr g).drop (a + 1) := by
        apply List.mem_of_getElem? (i := b - (a + 1))
        rw [List.getElem?_drop, Nat.add_sub_of_le (show a + 1 ≤ b by omega)]
        exact hLate
      have hAbove := eventTailEventsOfSegmentFloor (softmaxBarrierBranchFloor hFloor)
        (softmaxBarrierSegmentFloor hFloor) hw hUp _ hLater
      omega
  by_contra hNe
  rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
  · exact noLater hi hj hFirst hLast hLt
  · exact noLater hj hi hLast hFirst hGt

private theorem earlierBarrierMarkCount (hX : Consistent l kernel Assumptions.all m X)
    {g i j site : Nat} {e : Event} (he : X.get (g,i) = some e) (hPc : e.pc = site) (hBefore : i < j)
    (hSite : site ∈ softmaxBarrierSites) (hFloor : site + 1 ∈ softmaxBarrierFloors) :
    ((X.tr g).take j).countP (barrierMark site) = 1 := by
  have hRead : ((X.tr g).take j)[i]? = some e := by
    rwa [List.getElem?_take_of_lt hBefore]
  apply countP_eq_one_at (barrierMark site) hRead (beq_iff_eq.mpr hPc)
  intro k f hk hMark
  have hLt := (List.getElem?_eq_some_iff.mp hk).1.trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hLt] at hk
  exact earlierBarrierMarkUnique hX hk he (beq_iff_eq.mp hMark) hPc hSite hFloor

private theorem statsSiteOfNotice {e : Event} (hNotice : (Scores.notice e).isSome = true) :
    e.pc ∈ softmaxStatsSites := by
  obtain ⟨site, kind⟩ := e
  cases kind <;> try cases hNotice
  rename_i id size mode
  cases mode <;> try cases hNotice
  simp only [Scores.notice, Scores.noticeRound] at hNotice
  repeat' split at hNotice
  all_goals simp_all [softmaxStatsSites]

private theorem statsNoticeOfSite {site id : Nat} {count : Option Nat}
    (hs : site ∈ softmaxStatsSites) :
    (Scores.notice ⟨site, .bar id count .arrive⟩).isSome = true := by
  simp only [softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> rfl

private theorem fullStatisticsCountOfExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j pc : Nat} (hWarp : warpIndex l g < 8) (he : X.get (g,j) = some ⟨pc,.exit⟩) :
    (X.tr g).countP Scores.publishesStats =
      (X.tr g).countP (barrierMark 4397) + (X.tr g).countP (barrierMark 5683) +
      (X.tr g).countP (barrierMark 6891) + (X.tr g).countP (barrierMark 7616) := by
  have hLast := Execution.exit_last hX (event_thread_lt hX he) he
  change j + 1 = (X.tr g).length at hLast
  have hEquiv : (X.tr g).countP Scores.publishesStats =
      (X.tr g).countP (fun e => softmaxStatsSites.contains e.pc) := by
    apply List.countP_congr
    intro e hMem
    refine ⟨fun hn => List.contains_iff_mem.mpr (statsSiteOfNotice hn), ?_⟩
    intro hm
    have hs : e.pc ∈ softmaxStatsSites := List.contains_iff_mem.mp hm
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hMem
    have hLen : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hi).1
    have hBefore : i + 1 < (X.tr g).length := by
      by_contra! hs'
      have hEq : i = j := by omega
      subst i
      obtain rfl := Option.some.inj (hi.symm.trans he)
      have hSite := actualExitPc hX he
      rw [hSite] at hs
      exact (by decide : 9205 ∉ softmaxStatsSites) hs
    have hSubset : ∀ site ∈ softmaxStatsSites, site ∈ softmaxBarrierSites := by decide
    have hS := hSubset e.pc hs
    have hB := (softmaxBarrierMarker hp hX hWarp hi hBefore).trans
      (List.contains_iff_mem.mpr hS)
    obtain ⟨site,kind⟩ := e
    cases kind <;> try cases hB
    rename_i id count mode
    have hTable : softmaxStatsSites.all (fun site =>
        decide (namedBarrierMode site = .arrive)) = true := by decide +kernel
    have he' : X.get (g,i) = some ⟨site,.bar id count mode⟩ := hi
    have hMode := (actualNamedBarrier hp hX he').2.2.1.trans
      (of_decide_eq_true (List.all_eq_true.mp hTable _ hs))
    subst mode
    exact statsNoticeOfSite hs
  rw [hEquiv, countBarrierSites _ (by decide)]
  simp only [softmaxStatsSites, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private theorem countBeforeCurrentUnique (hX : Consistent l kernel Assumptions.all m X)
    {g j site : Nat} {e : Event} (he : X.get (g,j) = some e) (hPc : e.pc = site)
    (hSite : site ∈ softmaxBarrierSites) (hFloor : site + 1 ∈ softmaxBarrierFloors) :
    ((X.tr g).take j).countP (barrierMark site) = 0 := by
  apply List.countP_eq_zero.mpr
  intro f hMem hMark
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hMem
  have hLt := (List.getElem?_eq_some_iff.mp hi).1.trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hLt] at hi
  exact (Nat.ne_of_lt hLt) (earlierBarrierMarkUnique hX hi he
    (beq_iff_eq.mp hMark) hPc hSite hFloor)
end

private theorem countBeforeCurrentStrict {X : Execution} {g j site : Nat} {e : Event}
    (he : X.get (g,j) = some e) (hPc : e.pc = site) :
    ((X.tr g).take j).countP (barrierMark site) < (X.tr g).countP (barrierMark site) := by
  have hStep := countP_take_succ (p := barrierMark site) he (beq_iff_eq.mpr hPc)
  have hAll := (List.take_sublist (l := X.tr g) (i := j+1)).countP_le (p := barrierMark site)
  omega

private def softmaxWorkStation (biased blocks rank : Nat) : Nat :=
  if rank = 2 then 3583 else
  if rank = 3 then 4397 else
  if rank < 4 + 2 * biased then (if rank % 2 = 0 then 5271 else 5683) else
  if rank < 3 + biased + blocks then 6891 else
  if rank = 3 + biased + blocks then 7616 else 7741

private theorem workStationOfExitedLane {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {g j site id : Nat} {count : Option Nat} {mode : BarMode}
    (hw : warpIndex l g < 8) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hExit : Exited X g) (he : X.get (g,j) = some ⟨site, .bar id count mode⟩)
    (hPast : 1 < barrierOrdinal X (g,j)) :
    ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      let blocks := Mma.trips p batch tile
      let stage := stageOf ⟨warpIndex l g,hw⟩
      let biased := firstBiasedRepeats blocks (blocks - stageGeometryBlocks p batch tile stage + 10)
      site = softmaxWorkStation biased blocks (barrierOrdinal X (g,j)) := by
  let rank := barrierOrdinal X (g,j)
  let past := fun site => ((X.tr g).take j).countP (barrierMark site)
  let full := fun site => (X.tr g).countP (barrierMark site)
  obtain ⟨hZero,hOne⟩ := ordinalOfEarlyBarrier hp hX he
  have hStartup : site ≠ 173 := fun hs => by have := hZero.mpr hs; omega
  have hAllocation : site ∉ Mma.allocationEntrySites := fun hs => by have := hOne.mpr hs; omega
  have hStations := softmaxBarrierStation hp hX hw he
  have hBody := hStations.resolve_left hStartup
  have hLow : 173 < site := by
    simp only [softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hBody
    omega
  obtain ⟨i,hi,hInitial⟩ := commonBeforeRoleEvent hp hX he hLow
  have hCommon : past 173 = 1 := earlierBarrierMarkCount hX hInitial rfl hi (by decide) (by decide)
  obtain ⟨n,hn,start,hStart,hAt⟩ :=
    Mma.allocationEntryBeforeNamedBarrier hp hX he hStartup hAllocation
  have hAlloc : past 3103 = 1 := by
    have hSite : start = 3103 := by
      rcases Mma.allocationEntryRole hp hX hStart hAt with h | h | h
      all_goals omega
    subst start
    exact earlierBarrierMarkCount hX hAt rfl hn (by decide) (by decide)
  obtain ⟨batch,hBatch,hLo,hHi,⟨first, f, hf, hFirst⟩,⟨last, v, hv, hFinal⟩,
    hNotice,hCredit⟩ := exitedActiveBarrierExtent hp hX (event_thread_lt hX he) hw
      hWork hCuQ hUsedK hExit
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let blocks := Mma.trips p batch tile
  let stage := stageOf ⟨warpIndex l g,hw⟩
  let biased := firstBiasedRepeats blocks (blocks - stageGeometryBlocks p batch tile stage + 10)
  have hFPc : f.pc = 4397 := Scores.publicationSiteOfNotice hFirst
  have hVPc : v.pc = 7616 := Scores.publicationSiteOfNotice hFinal
  have hFullFirst : full 4397 = 1 := by
    have h := earlierBarrierMarkCount hX hf hFPc (len_of_get hf) (by decide) (by decide)
    simpa only [List.take_length] using h
  have hFullFinal : full 7616 = 1 := by
    have h := earlierBarrierMarkCount hX hv hVPc (len_of_get hv) (by decide) (by decide)
    simpa only [List.take_length] using h
  obtain ⟨stop, ⟨pc,kind⟩, hStop, hExitKind⟩ := hExit
  change kind = .exit at hExitKind
  subst kind
  have hFullBias : full 3583 = 1 := (biasRendezvousCountsAtExit hX hStop false).1.trans hFullFirst
  have hPair := biasRendezvousCountsAtExit hX hStop true
  have hFullBiased : full 5683 = biased := hPair.1.symm.trans (hPair.2.trans hCredit)
  have hFullBiasAgain : full 5271 = biased := hPair.2.trans hCredit
  have hFullPlain : full 6891 + biased + 1 = blocks := by
    rw [Scores.beforeNotices, List.take_length, fullStatisticsCountOfExit hp hX hw hStop] at hNotice
    change full 4397 + full 5683 + full 6891 + full 7616 = blocks + 1 at hNotice
    omega
  have hOrd := softmaxBarrierOrdinalOfStations hp hX hw he
  change rank = past 173 + past 3103 + past 3583 + past 4397 + past 5271 + past 5683 +
    past 6891 + past 7616 + past 7741 at hOrd
  have debtFirst := biasStatisticsCountAtEvent hX he false
  have debtRepeat := biasStatisticsCountAtEvent hX he true
  change past 4397 + (if 3583 < site ∧ site ≤ 4397 then 1 else 0) = past 3583 at debtFirst
  change past 5683 + (if 5271 < site ∧ site ≤ 5683 then 1 else 0) = past 5271 at debtRepeat
  have before {floor site' : Nat} (hFloor : floor ∈ softmaxBarrierFloors)
      (hs : site < floor) (hl : floor ≤ site') : past site' = 0 :=
    barrierRankBeforeFloor hX hFloor he hs hl
  have after {floor site' : Nat} (hFloor : floor ∈ softmaxBarrierFloors)
      (hl : site' < floor) (hs : floor ≤ site) : past site' = full site' :=
    barrierRankAfterFloor hX hFloor he hl hs
  refine ⟨batch,hBatch,hLo,hHi,?_⟩
  change site = softmaxWorkStation biased blocks rank
  have hRelease : past 7741 = 0 := by
    have hLe : site ≤ 7741 := by
      simp only [softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hBody
      omega
    rcases Nat.eq_or_lt_of_le hLe with rfl | hLt
    · exact countBeforeCurrentUnique hX he rfl (by decide) (by decide)
    · exact before (floor := 7741) (by decide) hLt (by decide)
  have hOpeningFull (hs : 5006 ≤ site) : past 3583 = 1 ∧ past 4397 = 1 :=
    ⟨(after (floor := 5006) (by decide) (by decide) hs).trans hFullBias,
      (after (floor := 5006) (by decide) (by decide) hs).trans hFullFirst⟩
  have hBiasedFull (hs : 6654 ≤ site) : past 5271 = biased ∧ past 5683 = biased :=
    ⟨(after (floor := 6654) (by decide) (by decide) hs).trans hFullBiasAgain,
      (after (floor := 6654) (by decide) (by decide) hs).trans hFullBiased⟩
  have hBeforeLoops (hs : site < 5006) :
      past 5271 = 0 ∧ past 5683 = 0 ∧ past 6891 = 0 ∧ past 7616 = 0 :=
    ⟨before (floor := 5006) (by decide) hs (by decide),
      before (floor := 5006) (by decide) hs (by decide),
      before (floor := 5006) (by decide) hs (by decide),
      before (floor := 5006) (by decide) hs (by decide)⟩
  have hBeforePlain (hs : site < 6654) : past 6891 = 0 ∧ past 7616 = 0 :=
    ⟨before (floor := 6654) (by decide) hs (by decide),
      before (floor := 6654) (by decide) hs (by decide)⟩
  simp only [softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hBody
  rcases hBody with hInit | hFinal | hBias | hRepeat | hOpening | hStats | hPlain | hTerm
  · exact (hAllocation (hInit.symm ▸ (by decide : 3103 ∈ Mma.allocationEntrySites))).elim
  · obtain ⟨h₁,h₂⟩ := hOpeningFull (by omega)
    obtain ⟨h₃,h₄⟩ := hBiasedFull (by omega)
    have hPlainDone := after (floor := 7605) (site' := 6891) (by decide) (by decide) (by omega)
    have hFinalDone : past 7616 = 1 :=
      (after (floor := 7617) (by decide) (by decide) (by omega)).trans hFullFinal
    have hR : rank = 4 + biased + blocks := by omega
    have hNoBias : ¬ rank < 4 + 2 * biased := by omega
    have hNoPlain : ¬ rank < 3 + biased + blocks := by omega
    have hNoFinal : rank ≠ 3 + biased + blocks := by omega
    simp [softmaxWorkStation, hFinal, show rank ≠ 2 by omega, show rank ≠ 3 by omega,
      hNoBias, hNoPlain, hNoFinal]
  · have hBiasZero : past 3583 = 0 := countBeforeCurrentUnique hX he hBias (by decide) (by decide)
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hBeforeLoops (by omega)
    have hR : rank = 2 := by omega
    simp [softmaxWorkStation, hBias, hR]
  · obtain ⟨h₁,h₂⟩ := hOpeningFull (by omega)
    obtain ⟨h₃,h₄⟩ := hBeforePlain (by omega)
    have hLt : past 5271 < biased := (countBeforeCurrentStrict he hRepeat).trans_eq hFullBiasAgain
    simp [hRepeat] at debtRepeat
    have hR : rank = 4 + 2 * past 5271 := by omega
    simp [softmaxWorkStation, hRepeat, show rank ≠ 2 by omega, show rank ≠ 3 by omega,
      show rank < 4 + 2 * biased by omega, show rank % 2 = 0 by omega]
  · have hFirstZero : past 4397 = 0 :=
      countBeforeCurrentUnique hX he hOpening (by decide) (by decide)
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hBeforeLoops (by omega)
    simp [hOpening] at debtFirst
    have hR : rank = 3 := by omega
    simp [softmaxWorkStation, hOpening, hR]
  · obtain ⟨h₁,h₂⟩ := hOpeningFull (by omega)
    obtain ⟨h₃,h₄⟩ := hBeforePlain (by omega)
    have hLt : past 5683 < biased := (countBeforeCurrentStrict he hStats).trans_eq hFullBiased
    simp [hStats] at debtRepeat
    have hR : rank = 5 + 2 * past 5683 := by omega
    simp [softmaxWorkStation, hStats, show rank ≠ 2 by omega, show rank ≠ 3 by omega,
      show rank < 4 + 2 * biased by omega, show rank % 2 ≠ 0 by omega]
  · obtain ⟨h₁,h₂⟩ := hOpeningFull (by omega)
    obtain ⟨h₃,h₄⟩ := hBiasedFull (by omega)
    have hFinalZero := before (floor := 7605) (site' := 7616) (by decide) (by omega) (by decide)
    have hLt : past 6891 < full 6891 := countBeforeCurrentStrict he hPlain
    simp [softmaxWorkStation, hPlain, show rank ≠ 2 by omega, show rank ≠ 3 by omega,
      show ¬ rank < 4 + 2 * biased by omega, show rank < 3 + biased + blocks by omega]
  · obtain ⟨h₁,h₂⟩ := hOpeningFull (by omega)
    obtain ⟨h₃,h₄⟩ := hBiasedFull (by omega)
    have hPlainDone := after (floor := 7605) (site' := 6891) (by decide) (by decide) (by omega)
    have hFinalZero : past 7616 = 0 :=
      countBeforeCurrentUnique hX he hTerm (by decide) (by decide)
    have hR : rank = 3 + biased + blocks := by omega
    rw [softmaxWorkStation, ite_eq_right (show rank ≠ 2 by omega),
      ite_eq_right (show rank ≠ 3 by omega),
      ite_eq_right (show ¬ rank < 4 + 2 * biased by omega),
      ite_eq_right (show ¬ rank < 3 + biased + blocks by omega), ite_eq_left hR]
    exact hTerm

private theorem workOfSoftmaxBarrier {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g j site id : Nat} {count : Option Nat} {mode : BarMode}
    (hw : warpIndex l g < 8) (he : X.get (g,j) = some ⟨site,.bar id count mode⟩)
    (hPast : 1 < barrierOrdinal X (g,j)) (hWork : site ≠ 7741) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  obtain ⟨hZero,hOne⟩ := ordinalOfEarlyBarrier hp hX he
  have hNotCommon : site ≠ 173 := fun h => by have := hZero.mpr h; omega
  have hNotEntry : site ≠ 3103 := fun h => by
    have := hOne.mpr (h.symm ▸ (by decide : 3103 ∈ Mma.allocationEntrySites))
    omega
  have hs := (softmaxBarrierStation hp hX hw he).resolve_left hNotCommon
  simp only [softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hs
  let lane := laneOf l g
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hGet : X.get (warpLane l g lane,j) = some ⟨site,.bar id count mode⟩ := hLane.symm ▸ he
  exact softmaxWorkOfActiveEvent hp hX (event_thread_lt hX he) hw
    (Nat.mod_lt _ (by decide)) hCuQ hGet (show 3207 < site by omega) (show site < 7738 by omega)

private theorem barrierOrdinalInExtension {X Y : Execution} (hXY : X.le Y)
    {i : EvId} {e : Event} (he : X.get i = some e) : barrierOrdinal Y i = barrierOrdinal X i := by
  obtain ⟨rest,hTrace⟩ := hXY.1 i.1
  unfold barrierOrdinal
  rw [← hTrace, List.take_append_of_le_length (len_of_get he).le]

/-- Every softmax work rendezvous follows the selected tile's common barrier schedule.
An unfinished prefix keeps its observed ordinals in a maximal extension. -/
theorem noAlignedSoftmaxWorkMismatchOfExits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrames : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hExit : ∀ Y, Maximal l kernel Assumptions.all m Y →
      ∀ g < l.threads, g / l.block < tilePrefix p p.batch * p.heads → Exited Y g) :
    ¬ AlignedWorkBarrierMismatch l X 8 := by
  rintro ⟨⟨g,i⟩,⟨h,j⟩,site,site',id,id',count,count',mode,mode',
    hw,hRole,hi,hj,hPast,hRank,_,hNe⟩
  obtain ⟨Y,hXY,hMax⟩ := maximalExtension hp hX
  have hi' := Execution.le_get hXY hi
  have hj' := Execution.le_get hXY hj
  have hGe : 1 < barrierOrdinal Y (g,i) := (barrierOrdinalInExtension hXY hi).symm ▸ hPast
  have hEq : barrierOrdinal Y (g,i) = barrierOrdinal Y (h,j) := by
    rw [barrierOrdinalInExtension hXY hi, barrierOrdinalInExtension hXY hj]
    exact hRank
  have hWarp : warpIndex l g = warpIndex l h := hw.2
  have hRole' : warpIndex l h < 8 := hWarp ▸ hRole
  have hCta : g / l.block = h / l.block := hw.1.2.2
  obtain ⟨hCuQ,hUsedK⟩ := (hFrames Y hMax.1).metadataProtected hp
  have hWork : g / l.block < tilePrefix p p.batch * p.heads := by
    by_cases hGate : site = 7741
    · have hOther : site' ≠ 7741 := fun h => hNe (hGate.trans h.symm)
      exact hCta.symm ▸ workOfSoftmaxBarrier hp hMax.1 hCuQ hRole' hj' (hEq ▸ hGe) hOther
    · exact workOfSoftmaxBarrier hp hMax.1 hCuQ hRole hi' hGe hGate
  obtain ⟨b,hb,hLo,hHi,hs⟩ := workStationOfExitedLane hp hMax.1 hCuQ hUsedK hRole hWork
    (hExit Y hMax g hw.1.1 hWork) hi' hGe
  obtain ⟨b',hb',hLo',hHi',hs'⟩ := workStationOfExitedLane hp hMax.1 hCuQ hUsedK hRole'
    (hCta ▸ hWork) (hExit Y hMax h hw.1.2.1 (hCta ▸ hWork)) hj' (hEq ▸ hGe)
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hBatch : b = b' := (hUnique b ⟨hb,hLo,hHi⟩).trans
    (hUnique b' ⟨hb',hCta.symm ▸ hLo',hCta.symm ▸ hHi'⟩).symm
  subst b'
  have hStage : stageOf ⟨warpIndex l g,hRole⟩ = stageOf ⟨warpIndex l h,hRole'⟩ :=
    Fin.ext (congrArg (· / 4) hw.2)
  dsimp only at hs hs'
  rw [← hCta, ← hStage, ← hEq] at hs'
  exact hNe (hs.trans hs'.symm)

end PTX.Kernels.TmlFa4Fwd.Thread
