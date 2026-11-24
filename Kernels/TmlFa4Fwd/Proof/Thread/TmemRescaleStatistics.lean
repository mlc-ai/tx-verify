-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreCompletion
public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsRead
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityIssuers
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
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
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Lemmas.Flow.ContinuingEvent
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionProbabilityGate
import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry
import Kernels.TmlFa4Fwd.Proof.CorrectionStatsSync

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

private def rescaleEntry (stage : Fin 2) : Nat := Correction.statsBarrierPc stage true

private def statisticsWindow (stage : Fin 2) (rescale : Bool) (site : Nat) : Prop :=
  Correction.statsBarrierPc stage rescale < site ∧ site ≤
    if rescale then Correction.rescaleStorePc stage 7
    else TmlFa4Fwd.Correction.statsPc stage .maximum

private instance (stage : Fin 2) (rescale : Bool) (site : Nat) :
    Decidable (statisticsWindow stage rescale site) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def entersStatistics (stage : Fin 2) (rescale : Bool) (src dst : Nat) : Bool :=
  !decide (statisticsWindow stage rescale dst) || decide (statisticsWindow stage rescale src)

private def statisticsEntryCode (stage : Fin 2) (rescale : Bool) (pos : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
    (pos == Correction.statsBarrierPc stage rescale ||
      entersStatistics stage rescale pos (pos + 1)) &&
    match i.op with
    | .bra dst _ => entersStatistics stage rescale pos dst
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem statisticsEntryAudit (stage : Fin 2) (rescale : Bool) :
    (kernel.code.zipIdx.all fun (i,pos) => statisticsEntryCode stage rescale pos i) = true := by
  cases rescale <;> fin_cases stage <;> kernel_rfl

private theorem statisticsEntryAt {stage : Fin 2} {rescale : Bool} {site : Nat} {i : Instr}
    (hCode : kernel.code[site]? = some i) : statisticsEntryCode stage rescale site i = true := by
  apply List.all_eq_true.mp (statisticsEntryAudit stage rescale) (i,site)
  apply List.mem_of_getElem? (i := site)
  simp [List.getElem?_zipIdx,hCode]

private theorem statisticsEntryInstr (stage : Fin 2) (rescale : Bool) :
    kernel.code[Correction.statsBarrierPc stage rescale]? = some
      ⟨none,.barSyncN (.reg (if stage.val = 0 then 1625 else 1626)) (.imm 64) true⟩ := by
  have hReg : Correction.statsBarrierReg stage = if stage.val = 0 then 1625 else 1626 := by
    fin_cases stage <;> rfl
  rw [← hReg]
  exact Correction.statsBarrierCode stage rescale

private theorem tauInStatistics {l : Launch} {g : Nat} {s u : TState}
    (stage : Fin 2) (rescale : Bool) (ht : Tau kernel Assumptions.all l g s u)
    (hu : statisticsWindow stage rescale u.pc) : statisticsWindow stage rescale s.pc := by
  obtain ⟨ins,hCode,_,hExec⟩ := Softmax.tauScoreSource ht
  have hOther : s.pc ≠ Correction.statsBarrierPc stage rescale := by
    intro he
    rw [he,statisticsEntryInstr stage rescale] at hCode
    obtain rfl := Option.some.inj hCode
    rcases hExec with ⟨_,hGuard⟩ | ⟨_,hLocal,_⟩
    · cases hGuard
    · cases hLocal
  have hAudit := statisticsEntryAt (stage := stage) (rescale := rescale) hCode
  simp only [statisticsEntryCode,beq_eq_false_iff_ne.mpr hOther,Bool.false_or,
    Bool.and_eq_true] at hAudit
  have hStep (huPc : u.pc = s.pc+1) : statisticsWindow stage rescale s.pc := by
    have hs := hAudit.1.2
    rw [← huPc] at hs
    simpa [entersStatistics,hu] using hs
  rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hr⟩
  · exact hStep rfl
  rcases Softmax.scoreExecLocal hr with hFrame | ⟨seg,hSite,hMatch,hSeg⟩
  · have hPc := hFrame.pc
    cases hop : ins.op <;> simp only [hop,nextPc,BrxTarget,or_false] at hPc
    case bra dst uni =>
      have hEdge := hAudit.2
      simp only [hop,← hPc] at hEdge
      simpa [entersStatistics,hu] using hEdge
    case brx => simp [hop] at hAudit
    all_goals exact hStep hPc
  · have hs : seg.stop ≤ 7745 := by
      have audit : Assumptions.swExp2Sites.all (fun site =>
          match cuteExp2.matchAt kernel site with
          | some seg => decide (seg.stop ≤ 7745)
          | none => false) = true := by decide +kernel
      have h := List.all_eq_true.mp audit _ hSite
      rw [hMatch] at h
      exact of_decide_eq_true h
    have hv := (Softmax.scoreSegmentFrame hSeg).1
    have hEntry : 7745 < Correction.statsBarrierPc stage rescale := by
      cases rescale <;> fin_cases stage <;> decide
    exact False.elim (by have := hu.1; omega)

private theorem returningStatisticsEntry {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (rescale : Bool) (hAt : s.pc = Correction.statsBarrierPc stage rescale)
    (hp : l.block = 512) (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ id, e = ⟨Correction.statsBarrierPc stage rescale,.bar id (some 64) .sync⟩ := by
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  rw [hAt,statisticsEntryInstr stage rescale] at hCode
  obtain rfl := Option.some.inj hCode
  let reg := if stage.val = 0 then 1625 else 1626
  change Fires s.pc (barTmpl l g s (.reg reg) (some (.imm 64))) e (some u) at hFire
  have hLiteral : readBits l g s 32 (.imm 64) = .ok (BitVec.ofNat 64 64) := rfl
  have hNat : (BitVec.ofNat 64 64).toNat = 64 := rfl
  cases hReg : readBits l g s 32 (.reg reg) with
  | error f => simp [barTmpl,hReg,Fires] at hFire
  | ok id =>
    by_cases hid : 16 ≤ id.toNat
    · simp [barTmpl,hReg,hid,Fires] at hFire
    · have hTemplate : barTmpl l g s (.reg reg) (some (.imm 64)) =
          .bar id.toNat (next s) (some 64) .sync := by
        simp [barTmpl,hReg,hid,hLiteral,hNat,hp]
      rw [hTemplate] at hFire
      exact ⟨id.toNat,hAt ▸ hFire.1⟩

private theorem eventInStatistics {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (rescale : Bool) (hp : l.block = 512)
    (he : EStep kernel Assumptions.all l g s e (some u))
    (hu : statisticsWindow stage rescale u.pc) :
    statisticsWindow stage rescale s.pc ∨
      ∃ id, e = ⟨Correction.statsBarrierPc stage rescale, .bar id (some 64) .sync⟩ := by
  by_cases hAt : s.pc = Correction.statsBarrierPc stage rescale
  · exact .inr (returningStatisticsEntry stage rescale hAt hp he)
  obtain ⟨ins,hCode,hLocal,hFire⟩ := estep_event_source he
  have h := statisticsEntryAt (stage := stage) (rescale := rescale) hCode
  simp only [statisticsEntryCode,beq_eq_false_iff_ne.mpr hAt,Bool.false_or,
    Bool.and_eq_true,hLocal] at h
  have hF := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g)
    (s := s) h.1.1
  rcases callbackFrame_fires hF hFire with hPc | hPc
  · exact .inl (hPc ▸ hu)
  · have hEdge := h.1.2
    rw [← hPc] at hEdge
    exact .inl (by simpa [entersStatistics,hu] using hEdge)

private def statisticsWaitMark (stage : Fin 2) (rescale : Bool) (e : Event) : Bool :=
  e.pc == Correction.statsBarrierPc stage rescale

private theorem statisticsOwnerTrace {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} (stage : Fin 2) (rescale : Bool) (hp : l.block = 512)
    (hr : TraceReach kernel Assumptions.all l g s events u)
    (hu : statisticsWindow stage rescale u.pc) :
    (statisticsWindow stage rescale s.pc ∧ ∀ e ∈ events, statisticsWindow stage rescale e.pc) ∨
    ∃ pre id post,
      events = pre ++ ⟨Correction.statsBarrierPc stage rescale, .bar id (some 64) .sync⟩ :: post ∧
      ∀ e ∈ post, statisticsWindow stage rescale e.pc := by
  induction hr with
  | refl => exact .inl ⟨hu,by simp⟩
  | tau ht _ ih =>
    rcases ih hu with ⟨hs,hPost⟩ | hMem
    · exact .inl ⟨tauInStatistics stage rescale ht hs,hPost⟩
    · exact .inr hMem
  | event he _ ih =>
    rcases ih hu with ⟨hLive,hPost⟩ | ⟨pre,id,post,hSplit,hPost⟩
    · rcases eventInStatistics stage rescale hp he hLive with hs | ⟨id,rfl⟩
      · refine .inl ⟨hs,fun e hMem => ?_⟩
        rcases List.mem_cons.mp hMem with rfl | hRest
        · simpa only [estep_source_pc he] using hs
        · exact hPost e hRest
      · exact .inr ⟨[],id,_,rfl,hPost⟩
    · exact .inr ⟨_::pre,id,post,by rw [List.cons_append,← hSplit],hPost⟩

private def rescaleWindow (stage : Fin 2) (site : Nat) : Prop :=
  statisticsWindow stage true site

private instance (stage : Fin 2) (site : Nat) : Decidable (rescaleWindow stage site) :=
  inferInstanceAs (Decidable (statisticsWindow stage true site))

private def rescaleWindowBranch (stage : Fin 2) (pc : Nat) (i : Instr) : Bool :=
  match i.op with
  | .bra dst _ => decide (rescaleWindow stage pc → rescaleWindow stage dst → pc ≤ dst)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem rescaleWindowBranches (stage : Fin 2) :
    (kernel.code.zipIdx.all (fun (i,pc) => rescaleWindowBranch stage pc i)) = true := by
  fin_cases stage <;> kernel_rfl

private theorem rescaleWindowTauPc {l : Launch} {g : Nat} {s u : TState}
    (stage : Fin 2) (ht : Tau kernel Assumptions.all l g s u)
    (hs : rescaleWindow stage s.pc) (hu : rescaleWindow stage u.pc) : s.pc ≤ u.pc := by
  obtain ⟨ins,hCode,_,hExec⟩ := Softmax.tauScoreSource ht
  rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hr⟩
  · exact Nat.le_succ _
  rcases Softmax.scoreExecLocal hr with hFrame | ⟨seg,hSite,hMatch,hSeg⟩
  · have hAudit := List.all_eq_true.mp (rescaleWindowBranches stage) (ins,s.pc)
      (List.mem_of_getElem? (i := s.pc) (by simp [List.getElem?_zipIdx,hCode]))
    have hPc := hFrame.pc
    cases hop : ins.op <;> simp only [hop,nextPc,BrxTarget,or_false] at hPc
    case bra dst uni =>
      simp only [rescaleWindowBranch,hop,decide_eq_true_eq] at hAudit
      rw [hPc] at hu ⊢
      exact hAudit hs hu
    case brx => simp [rescaleWindowBranch,hop] at hAudit
    all_goals omega
  · have hLo : 7745 < rescaleEntry stage := by fin_cases stage <;> decide
    have hEnd : seg.stop ≤ 7745 := by
      have audit : Assumptions.swExp2Sites.all (fun site =>
          match cuteExp2.matchAt kernel site with
          | some seg => decide (seg.stop ≤ 7745)
          | none => false) = true := by decide +kernel
      have h := List.all_eq_true.mp audit _ hSite
      rw [hMatch] at h
      exact of_decide_eq_true h
    have hPc := (Softmax.scoreSegmentFrame hSeg).1
    have hAfter : rescaleEntry stage < u.pc := hu.1
    omega

private theorem rescaleWindowEventPc {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (he : EStep kernel Assumptions.all l g s e (some u)) : s.pc ≤ u.pc := by
  obtain ⟨ins,hCode,hLocal,hFire⟩ := estep_event_source he
  have hAudit := statisticsEntryAt (stage := stage) (rescale := true) hCode
  simp only [statisticsEntryCode,Bool.and_eq_true,hLocal,Bool.false_or] at hAudit
  have hFrame := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g)
    (s := s) hAudit.1.1
  rcases callbackFrame_fires hFrame hFire with hPc | hPc <;> omega

private theorem rescaleWindowMonotoneOrNewWait {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} (stage : Fin 2) (hp : l.block = 512)
    (hr : TraceReach kernel Assumptions.all l g s events u) (hu : rescaleWindow stage u.pc) :
    (rescaleWindow stage s.pc ∧ s.pc ≤ u.pc) ∨ ∃ e ∈ events,
      e.pc = rescaleEntry stage := by
  induction hr with
  | refl => exact .inl ⟨hu,le_rfl⟩
  | tau ht _ ih =>
    rcases ih hu with ⟨hMid,hPc⟩ | hMarker
    · have hs := tauInStatistics stage true ht hMid
      exact .inl ⟨hs,(rescaleWindowTauPc stage ht hs hMid).trans hPc⟩
    · exact .inr hMarker
  | event he _ ih =>
    rcases ih hu with ⟨hMid,hPc⟩ | ⟨e,hMem,hSite⟩
    · rcases eventInStatistics stage true hp he hMid with hs | ⟨_,rfl⟩
      · exact .inl ⟨hs,(rescaleWindowEventPc stage he).trans hPc⟩
      · exact .inr ⟨_,List.mem_cons_self,rfl⟩
    · exact .inr ⟨e,List.mem_cons_of_mem _ hMem,hSite⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Returning to load the same output chunk again crosses another named
statistics wait on the actual correction lane. -/
theorem previousRescaleStoreBeforeLoadAdvancesStatistics (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g store load : Nat} (stage : Fin 2)
    (chunk : Fin 8) {a b : Nat} {xs ys : List Value} {sh th : TcShape}
    (hStore : X.get (g,store) = some ⟨Correction.rescaleStorePc stage chunk,.tc (.st a xs sh)⟩)
    (hLoad : X.get (g,load) = some ⟨Correction.rescaleLoadPc stage chunk,.tc (.ld b ys th)⟩)
    (hBefore : store < load) :
    let id := Correction.statsBarrierId l g stage
    (correctionBefore X (g,store)).barrier id < (correctionBefore X (g,load)).barrier id := by
  let start : Event := ⟨Correction.rescaleStorePc stage chunk,.tc (.st a xs sh)⟩
  let middle := ((X.tr g).drop (store+1)).take (load-(store+1))
  have hLen : load < (X.tr g).length := PTX.len_of_get hLoad
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hStore)
  obtain ⟨s,u,hStep,hTail⟩ := hRun.after_event hStore (by omega)
  have hGet : ((X.tr g).drop (store+1))[load-(store+1)]? =
      some ⟨Correction.rescaleLoadPc stage chunk,.tc (.ld b ys th)⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le (by omega : store+1 ≤ load)]
    exact hLoad
  obtain ⟨t,_,hMiddle,hLoadStep⟩ := hTail.before_event hGet
  have hTrace : TraceReach kernel Assumptions.all l g s (start::middle) t :=
    .event hStep hMiddle
  have hs : s.pc = Correction.rescaleStorePc stage chunk := (estep_source_pc hStep).symm
  have ht : t.pc = Correction.rescaleLoadPc stage chunk := (estep_source_pc hLoadStep).symm
  have hLoadLive : rescaleWindow stage t.pc := by
    rw [ht]
    fin_cases stage <;> fin_cases chunk <;> decide
  obtain ⟨e,hMem,hSite⟩ := (rescaleWindowMonotoneOrNewWait stage hp.block hTrace hLoadLive)
    |>.resolve_left (fun h => by
      have hBack : Correction.rescaleLoadPc stage chunk < Correction.rescaleStorePc stage chunk :=
        by fin_cases stage <;> fin_cases chunk <;> decide
      omega)
  have hTag : Correction.correctionStatsWaitMark stage e = true := by
    apply (Correction.correctionStatsWaitMark_iff stage e).mpr
    rw [hSite]
    fin_cases stage <;> decide
  have hPositive : 0 < (start::middle).countP (Correction.correctionStatsWaitMark stage) :=
    List.countP_pos_iff.mpr ⟨e,hMem,hTag⟩
  have hSplit : (X.tr g).take load = (X.tr g).take store ++ start::middle := by
    have hStore' : (X.tr g)[store]? = some start := hStore
    calc
      (X.tr g).take load = (X.tr g).take (store+1) ++ middle := by
        simp only [middle,← List.take_add]
        congr 1
        omega
      _ = (X.tr g).take store ++ start::middle := by
        rw [List.take_add_one,hStore',Option.toList_some,List.append_assoc]
        rfl
  have hGroup := correctionStoreWarpGroup hp hX stage chunk hStore
  have hWarp : 8 ≤ Prologue.warpIndex l g ∧ Prologue.warpIndex l g < 12 := by
    change g%l.block/128 = 2 at hGroup
    unfold Prologue.warpIndex
    omega
  dsimp only
  rw [correctionBarrierOrdinal,correctionBarrierOrdinal,
    ← Correction.correctionWaitPrefixCount hp hX stage (PTX.len_of_get hStore) hWarp,
    ← Correction.correctionWaitPrefixCount hp hX stage hLen hWarp,hSplit,List.countP_append]
  let mark := Correction.correctionStatsWaitMark stage
  let past := ((X.tr g).take store).countP mark
  change past < past+(start::middle).countP mark
  exact Nat.lt_add_of_pos_right hPositive

/-- The number of prior rescale statistics waits at this event boundary. -/
@[no_expose] def rescaleStatisticsCount (X : Execution) (i : EvId) (stage : Fin 2) : Nat :=
  ((X.tr i.1).take i.2).countP (statisticsWaitMark stage true)

private theorem statisticsPrior (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} {stage : Fin 2} (rescale : Bool) (he : X.get (g, index) = some e)
    (hWindow : statisticsWindow stage rescale e.pc)
    (hWarp : 8 ≤ Prologue.warpIndex l g ∧ Prologue.warpIndex l g < 12) :
    let id := Correction.statsBarrierId l g stage
    ∃ wait, CorrectionWaits X wait (if rescale then .rescale else .terminal) stage ∧
      Resumes kernel X wait (g, index) ∧
      ((X.tr g).take index).countP (statisticsWaitMark stage rescale) =
        ((X.tr g).take wait.2).countP (statisticsWaitMark stage rescale) + 1 ∧
      (correctionBefore X (g, index)).barrier id = (correctionBefore X wait).barrier id + 1 := by
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t,_,hTrace,hFire⟩ := hr.before_event he
  have hLimit : statisticsWindow stage rescale t.pc := estep_source_pc hFire ▸ hWindow
  rcases statisticsOwnerTrace stage rescale hp.block hTrace hLimit with ⟨hEntry,_⟩ |
      ⟨pre,id,post,hSplit,hInside⟩
  · have hEntryLo : 0 < Correction.statsBarrierPc stage rescale := by
      cases rescale <;> fin_cases stage <;> decide
    have hBad : Correction.statsBarrierPc stage rescale < 0 := hEntry.1
    omega
  · let k := pre.length
    let waitEvent : Event := ⟨Correction.statsBarrierPc stage rescale,.bar id (some 64) .sync⟩
    change (X.tr g).take index = pre ++ waitEvent :: post at hSplit
    have hK : k < index := by
      have hLen := congrArg List.length hSplit
      simp only [List.length_take,List.length_append,List.length_cons] at hLen
      dsimp only [k]
      omega
    have hRaw : X.get (g,k) = some waitEvent := by
      change (X.tr g)[k]? = _
      rw [← List.getElem?_take_of_lt hK,hSplit,
        List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero]
    have hId := Correction.actualCorrectionStatsBarrierId hp hX stage
      (by cases rescale <;> fin_cases stage <;> decide) hRaw
    subst id
    have hPre : (X.tr g).take k = pre := by
      rw [← show min k index = k from Nat.min_eq_left hK.le,← List.take_take,hSplit]
      exact List.take_append_length
    have hMarker : ∀ e ∈ post, ¬ statisticsWaitMark stage rescale e = true := by
      intro e he hm
      exact (ne_of_gt (hInside e he).1) (beq_iff_eq.mp hm)
    have hCount := List.countP_eq_zero.mpr hMarker
    refine ⟨(g,k), ?_, ⟨⟨rfl,hK,PTX.len_of_get he⟩,?_⟩,?_,?_⟩
    · cases rescale
      · exact terminalWaitObservation stage hRaw
      · exact rescaleWaitObservation stage hRaw
    · rw [hRaw]
      trivial
    · change ((X.tr g).take index).countP (statisticsWaitMark stage rescale) =
        ((X.tr g).take k).countP (statisticsWaitMark stage rescale)+1
      rw [hSplit,hPre,List.countP_append,List.countP_cons,hCount]
      simp [waitEvent,statisticsWaitMark]
    · have hN : ∀ e ∈ post, ¬ Correction.correctionStatsWaitMark stage e = true := by
        intro e he hh
        have hm := (Correction.correctionStatsWaitMark_iff stage e).mp hh
        have audit : (Correction.correctionStatsSites stage).all
            (fun site => !(decide (statisticsWindow stage rescale site))) = true := by
          cases rescale <;> fin_cases stage <;> decide
        have hOutside := List.all_eq_true.mp audit e.pc hm
        rw [decide_eq_true (hInside e he)] at hOutside
        cases hOutside
      have hEntry : Correction.correctionStatsWaitMark stage waitEvent = true := by
        apply (Correction.correctionStatsWaitMark_iff stage waitEvent).mpr
        change Correction.statsBarrierPc stage rescale ∈ Correction.correctionStatsSites stage
        cases rescale <;> fin_cases stage <;> decide
      rw [correctionBarrierOrdinal,correctionBarrierOrdinal,
        ← Correction.correctionWaitPrefixCount hp hX stage (PTX.len_of_get he) hWarp,
        ← Correction.correctionWaitPrefixCount hp hX stage (hK.trans (PTX.len_of_get he)) hWarp]
      change ((X.tr g).take index).countP (Correction.correctionStatsWaitMark stage) =
        ((X.tr g).take k).countP (Correction.correctionStatsWaitMark stage)+1
      rw [hSplit,hPre,List.countP_append,List.countP_cons,List.countP_eq_zero.mpr hN,hEntry]
      simp [Nat.add_comm]

/-- Every actual rescale store follows its stage's statistics rendezvous on the issuing lane. -/
theorem statisticsBeforeOutputRescaleWithOrdinal (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {store : EvId} {stage : Fin 2}
    (hStore : OutputRescaleStore X store stage) :
    let id := Correction.statsBarrierId l store.1 stage
    ∃ wait, CorrectionWaits X wait .rescale stage ∧ Resumes kernel X wait store ∧
      rescaleStatisticsCount X store stage = rescaleStatisticsCount X wait stage + 1 ∧
      (correctionBefore X store).barrier id = (correctionBefore X wait).barrier id + 1 := by
  obtain ⟨g, index⟩ := store
  obtain ⟨chunk, address, values, shape, he⟩ := hStore.decoded
  have hChunk := chunk.isLt
  have hWindow : rescaleWindow stage (Correction.rescaleStorePc stage chunk) := by
    refine ⟨?_, ?_⟩
    · fin_cases stage <;> fin_cases chunk <;> decide
    · change Correction.rescaleStorePc stage chunk ≤ Correction.rescaleStorePc stage 7
      unfold Correction.rescaleStorePc
      omega
  have hGroup := correctionStoreWarpGroup hp hX stage chunk he
  change (g % l.block) / 128 = 2 at hGroup
  obtain ⟨wait, hWait, hResume, hCount, hOrdinal⟩ :=
    statisticsPrior hp hX true he hWindow (by unfold Prologue.warpIndex; omega)
  have hLane : wait.1 = g := hResume.1.1
  exact ⟨wait, hWait, hResume, by simpa [rescaleStatisticsCount, hLane] using hCount, hOrdinal⟩

/-- The correction's statistics reads use the rescale rendezvous for alpha,
and the terminal rendezvous for sum and maximum. -/
def statisticsReadRound : TmlFa4Fwd.Correction.StatsKind → CorrectionRound
  | .alpha => .rescale
  | .sum | .maximum => .terminal

private def statisticsReadRescales : TmlFa4Fwd.Correction.StatsKind → Bool
  | .alpha => true
  | .sum | .maximum => false

/-- Every statistics load follows the matching named-barrier return for its stage and round. -/
theorem statisticsBeforeRead (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {reader : EvId} {stage : Fin 2} {kind : TmlFa4Fwd.Correction.StatsKind} {a : Acc}
    {bytes : List (Option Byte)} (hRead : Correction.StatisticsRead X reader stage kind a bytes) :
    let id := Correction.statsBarrierId l reader.1 stage
    ∃ wait, CorrectionWaits X wait (statisticsReadRound kind) stage ∧
      Resumes kernel X wait reader ∧
      (correctionBefore X reader).barrier id = (correctionBefore X wait).barrier id + 1 := by
  obtain ⟨g, index⟩ := reader
  change X.get (g, index) =
    some ⟨TmlFa4Fwd.Correction.statsPc stage kind, .rd a bytes⟩ at hRead
  have hWindow : statisticsWindow stage (statisticsReadRescales kind)
      (TmlFa4Fwd.Correction.statsPc stage kind) := by
    cases kind <;> fin_cases stage <;> decide
  have hWarp := Correction.StatisticsRead.warp hp hX hRead
  obtain ⟨wait, hWait, hResume, _, hOrdinal⟩ :=
    statisticsPrior hp hX (statisticsReadRescales kind) hRead hWindow hWarp
  have hRound : (if statisticsReadRescales kind then CorrectionRound.rescale else .terminal) =
      statisticsReadRound kind := by cases kind <;> rfl
  rw [hRound] at hWait
  exact ⟨wait, hWait, hResume, hOrdinal⟩

private theorem alphaCannotSkip {l : Launch} {g : Nat} {s u : TState}
    (stage : Fin 2) (hs : s.pc = rescaleEntry stage+1)
    (ht : Tau kernel Assumptions.all l g s u) : False := by
  have hDecode : ∃ ins, kernel.code[rescaleEntry stage+1]? = some ins ∧
      ins.guard = none ∧ ins.op.isLocal = false := by
    fin_cases stage
    · exact ⟨_,Flow.code_8007,rfl,rfl⟩
    · exact ⟨_,Flow.code_8226,rfl,rfl⟩
  obtain ⟨ins,he,hGuard,hIsLocal⟩ := hDecode
  obtain ⟨actual,hCode,_,hStep⟩ := Softmax.tauScoreSource ht
  rw [hs,he] at hCode
  obtain rfl := Option.some.inj hCode
  rcases hStep with ⟨_,hSkip⟩ | ⟨_,hLocal,_⟩
  · rw [hGuard] at hSkip
    cases hSkip
  · rw [hIsLocal] at hLocal
    cases hLocal

private theorem rescaleDataAfterNamedWait {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {g j k id : Nat} (stage : Fin 2) {e : Event}
    (hWait : X.get (g,k) = some ⟨rescaleEntry stage,.bar id (some 64) .sync⟩)
    (hEvent : X.get (g,j) = some e) (hSite : e.pc ≠ rescaleEntry stage+1)
    (hBefore : k < j) : k+1 < j := by
  by_contra! hAdjacent
  have hJ : j = k+1 := by omega
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hWait)
  have hMore : k+1 < (X.tr g).length := by rw [← hJ]; exact len_of_get hEvent
  obtain ⟨s,u,hStep,hRest⟩ := hRun.after_event hWait hMore
  have hs : s.pc = rescaleEntry stage := (estep_source_pc hStep).symm
  have hu := followsMarkedBarrier hs (statisticsEntryInstr stage true) rfl hStep
  have hTarget : ((X.tr g).drop (k+1))[0]? = some e := by
    rw [List.getElem?_drop,Nat.add_zero,← hJ]
    exact hEvent
  obtain ⟨v,_,hr,hFire⟩ := hRest.before_event hTarget
  have hNoSteps : TraceReach kernel Assumptions.all l g u [] v := by simpa using hr
  have hEq : u = v := by
    cases hNoSteps with
    | refl => rfl
    | tau ht => exact (alphaCannotSkip stage (hs ▸ hu) ht).elim
  have hAt := (estep_source_pc hFire).symm
  rw [← hEq,hu,hs] at hAt
  exact hSite hAt.symm

/-- A real rescale store shows that its named statistics barrier returned and was
followed by a separate memory event before the store. -/
theorem statisticsPassedBeforeOutputRescale (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {store : EvId} {stage : Fin 2}
    (hStore : OutputRescaleStore X store stage) :
    let id := Correction.statsBarrierId l store.1 stage
    ∃ wait, CorrectionWaits X wait .rescale stage ∧ Resumes kernel X wait store ∧
      wait.2+1 < store.2 ∧
      (correctionBefore X store).barrier id = (correctionBefore X wait).barrier id+1 := by
  obtain ⟨wait,hWait,hResume,_,hOrdinal⟩ := statisticsBeforeOutputRescaleWithOrdinal hp hX hStore
  refine ⟨wait,hWait,hResume,?_,hOrdinal⟩
  obtain ⟨g,j⟩ := store
  obtain ⟨h,k⟩ := wait
  have hLane : h = g := hResume.1.1
  subst h
  obtain ⟨e,he,hAction⟩ := hWait
  have hPc := correctionRescaleWaitSite hAction
  have hKind := correctionStatsWait hp hX he hAction
  obtain ⟨src,kind⟩ := e
  change src = rescaleEntry stage at hPc
  change kind = _ at hKind
  subst src
  subst kind
  obtain ⟨chunk,_,_,_,hPut⟩ := hStore.decoded
  apply rescaleDataAfterNamedWait hX stage he hPut _ hResume.1.2.1
  change Correction.rescaleStorePc stage chunk ≠ rescaleEntry stage+1
  fin_cases stage <;> fin_cases chunk <;> decide

/-- The ordinary load of a correction output rescale chunk. -/
@[no_expose] def OutputRescaleLoad (X : Execution) (load : EvId) (stage : Fin 2) : Prop :=
  ∃ (chunk : Fin 8) (address : Nat) (values : List Value) (shape : TcShape),
    X.get load = some ⟨Correction.rescaleLoadPc stage chunk,.tc (.ld address values shape)⟩

/-- Classify a decoded rescale load inside the thread proof. -/
theorem OutputRescaleLoad.ofDecoded {X : Execution} {load : EvId} {stage : Fin 2}
    (chunk : Fin 8) {address : Nat} {values : List Value} {shape : TcShape}
    (he : X.get load = some ⟨Correction.rescaleLoadPc stage chunk,.tc (.ld address values shape)⟩) :
    OutputRescaleLoad X load stage :=
  ⟨chunk,address,values,shape,he⟩

/-- Expose the actual event within Thread. -/
theorem OutputRescaleLoad.decoded {X : Execution} {load : EvId} {stage : Fin 2}
    (h : OutputRescaleLoad X load stage) :
    ∃ (chunk : Fin 8) (address : Nat) (values : List Value) (shape : TcShape),
      X.get load = some ⟨Correction.rescaleLoadPc stage chunk,.tc (.ld address values shape)⟩ :=
  h

/-- A rescale load is issued by a correction warp. -/
theorem OutputRescaleLoad.correctionRole (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {load : EvId} {stage : Fin 2}
    (hLoad : OutputRescaleLoad X load stage) :
    8 ≤ Prologue.warpIndex l load.1 ∧ Prologue.warpIndex l load.1 < 12 := by
  obtain ⟨g,j⟩ := load
  obtain ⟨chunk,address,values,shape,he⟩ := hLoad
  have hBounds : 8006 ≤ Correction.rescaleLoadPc stage chunk ∧
      Correction.rescaleLoadPc stage chunk < 9057 ∧
      Correction.rescaleLoadPc stage chunk ∉ registerHintSites := by
    fin_cases stage <;> fin_cases chunk <;> decide
  have hRole := roleBodyPcOfEvent hp hX he
    (show 173 < Correction.rescaleLoadPc stage chunk by omega) hBounds.2.2
  change roleBodyPc (Prologue.warpIndex l g) (Correction.rescaleLoadPc stage chunk) at hRole
  have hWarp : 8 ≤ Prologue.warpIndex l g ∧ Prologue.warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with hExit | hBody
    · omega
    · split_ifs at hBody <;> omega
  exact hWarp

/-- The load itself witnesses passage through the rescale statistics barrier.
The following rescale store can still be absent in this prefix. -/
theorem statisticsPassedBeforeOutputRescaleLoad (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {load : EvId} {stage : Fin 2}
    (hLoad : OutputRescaleLoad X load stage) :
    ∃ wait, CorrectionWaits X wait .rescale stage ∧ Resumes kernel X wait load ∧
      wait.2+1 < load.2 ∧ (correctionBefore X load).barrier
        (Correction.statsBarrierId l load.1 stage) =
        (correctionBefore X wait).barrier (Correction.statsBarrierId l load.1 stage)+1 := by
  obtain ⟨g,j⟩ := load
  obtain ⟨chunk,address,values,shape,he⟩ := hLoad
  have hWindow : rescaleWindow stage (Correction.rescaleLoadPc stage chunk) := by
    fin_cases stage <;> fin_cases chunk <;> decide
  have hWarp := OutputRescaleLoad.correctionRole hp hX ⟨chunk,address,values,shape,he⟩
  obtain ⟨wait,hWait,hResume,_,hOrdinal⟩ := statisticsPrior hp hX true he hWindow hWarp
  refine ⟨wait,hWait,hResume,?_,hOrdinal⟩
  obtain ⟨h,k⟩ := wait
  have hLane : h = g := hResume.1.1
  subst h
  obtain ⟨e,hw,hAction⟩ := hWait
  have hPc := correctionRescaleWaitSite hAction
  have hKind := correctionStatsWait hp hX hw hAction
  obtain ⟨src,kind⟩ := e
  change src = rescaleEntry stage at hPc
  change kind = _ at hKind
  subst src
  subst kind
  apply rescaleDataAfterNamedWait hX stage hw he _ hResume.1.2.1
  change Correction.rescaleLoadPc stage chunk ≠ rescaleEntry stage+1
  fin_cases stage <;> fin_cases chunk <;> decide

/-- A rescale store is issued by a correction warp. -/
theorem OutputRescaleStore.correctionRole (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {store : EvId} {stage : Fin 2}
    (hStore : OutputRescaleStore X store stage) :
    8 ≤ Prologue.warpIndex l store.1 ∧ Prologue.warpIndex l store.1 < 12 := by
  obtain ⟨chunk,address,values,shape,he⟩ := hStore.decoded
  have hGroup := correctionStoreWarpGroup hp hX stage chunk he
  unfold Prologue.warpIndex
  omega

private theorem rescaleDataCreditUses (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {stage : Fin 2} {e : Event}
    (he : X.get (g,j) = some e) (hWarp : 8 ≤ Prologue.warpIndex l g ∧ Prologue.warpIndex l g < 12)
    (hWindow : if stage.val = 0 then 8007 ≤ e.pc ∧ e.pc ≤ 8223 else 8226 ≤ e.pc ∧ e.pc ≤ 8442) :
    Scores.probabilityOrdinal l X (g/l.block) stage 0 (g,j) + 1 ≤
      (correctionBefore X (g,j)).barrier (Correction.statsBarrierId l g stage) := by
  have hBudget := Correction.correctionProbabilityWaitBudgetInsideRescale hX stage he hWindow
  have hCredits := correctionProbabilityOrdinalLeMarks hp hX stage
    (cta := g/l.block) (j := j) hWarp.1
  rw [correctionBarrierOrdinal,
    ← Correction.correctionWaitPrefixCount hp hX stage (PTX.len_of_get he) hWarp]
  exact (Nat.add_le_add_right hCredits 1).trans hBudget

/-- A rescale store is inside a statistics generation beyond its earlier joint credits. -/
theorem OutputRescaleStore.creditUses (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {store : EvId} {stage : Fin 2}
    (hStore : OutputRescaleStore X store stage) :
    Scores.probabilityOrdinal l X (store.1/l.block) stage 0 store + 1 ≤
      (correctionBefore X store).barrier (Correction.statsBarrierId l store.1 stage) := by
  obtain ⟨g,j⟩ := store
  obtain ⟨chunk,address,values,shape,he⟩ := hStore.decoded
  have hWarp := hStore.correctionRole hp hX
  have hWindow : if stage.val = 0 then
      8007 ≤ Correction.rescaleStorePc stage chunk ∧ Correction.rescaleStorePc stage chunk ≤ 8223
      else 8226 ≤ Correction.rescaleStorePc stage chunk ∧
        Correction.rescaleStorePc stage chunk ≤ 8442 := by
    fin_cases stage <;> fin_cases chunk <;> decide
  exact rescaleDataCreditUses hp hX he hWarp hWindow

/-- A rescale load is inside a statistics generation beyond its earlier joint credits. -/
theorem OutputRescaleLoad.creditUses (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load : EvId} {stage : Fin 2} (hLoad : OutputRescaleLoad X load stage) :
    Scores.probabilityOrdinal l X (load.1/l.block) stage 0 load + 1 ≤
      (correctionBefore X load).barrier (Correction.statsBarrierId l load.1 stage) := by
  obtain ⟨g,j⟩ := load
  obtain ⟨chunk,address,values,shape,he⟩ := hLoad
  have hWarp := OutputRescaleLoad.correctionRole hp hX ⟨chunk,address,values,shape,he⟩
  have hWindow : if stage.val = 0 then
      8007 ≤ Correction.rescaleLoadPc stage chunk ∧ Correction.rescaleLoadPc stage chunk ≤ 8223
      else 8226 ≤ Correction.rescaleLoadPc stage chunk ∧
        Correction.rescaleLoadPc stage chunk ≤ 8442 := by
    fin_cases stage <;> fin_cases chunk <;> decide
  exact rescaleDataCreditUses hp hX he hWarp hWindow

end PTX.Kernels.TmlFa4Fwd.Thread
