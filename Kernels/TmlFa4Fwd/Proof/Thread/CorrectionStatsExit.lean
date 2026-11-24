-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierTerminal
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierOrder
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters
import Kernels.TmlFa4Fwd.Proof.CorrectionTileGeometry
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.NotTcData
import Lemmas.Flow.TcLdTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue

private def statsExitSite (terminal : Bool) (stage : Fin 2) : Nat :=
  if terminal then Correction.statsBarrierPc stage false
  else if stage.val = 0 then 7985 else 7988

private def beforeStats (site : Nat) (i : Instr) (atPc : Nat) : Bool :=
  (i.guard.isNone || decide (atPc < site)) &&
    (!i.op.isLocal || match i.op with
      | .bra target _ => decide (7955 ≤ target ∧ target ≤ site)
      | .brx .. => false
      | _ => decide (atPc < site))

set_option maxRecDepth 100000 in
private def beforeSiteChecked (site : Nat) : Prop :=
  (((kernel.code.drop 7955).take (site + 1 - 7955)).zipIdx 7955).all
    (fun (i, atPc) => beforeStats site i atPc) = true

private theorem beforeStatsTable (terminal : Bool) (stage : Fin 2) :
    beforeSiteChecked (statsExitSite terminal stage) := by
  unfold beforeSiteChecked
  cases terminal <;> fin_cases stage <;> kernel_rfl

private theorem beforeStatsLookup {site atPc : Nat} {i : Instr}
    (hAudit : beforeSiteChecked site) (hLo : 7955 ≤ atPc) (hHi : atPc ≤ site)
    (hCode : kernel.code[atPc]? = some i) : beforeStats site i atPc = true := by
  apply List.all_eq_true.mp hAudit (i, atPc)
  apply List.mem_of_getElem? (i := atPc-7955)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hCode]
  rfl

private theorem beforeStatsTau {l : Launch} {g : Nat} {s u : TState} {site : Nat}
    (hChecked : beforeSiteChecked site) (hLo : 7955 ≤ s.pc) (hHi : s.pc ≤ site)
    (hTau : Tau kernel Assumptions.all l g s u) :
    7955 ≤ u.pc ∧ u.pc ≤ site := by
  obtain ⟨ins, hCode, _, hExec⟩ := Softmax.tauScoreSource hTau
  have hAudit := beforeStatsLookup hChecked hLo hHi hCode
  simp only [beforeStats, Bool.and_eq_true] at hAudit
  rcases hExec with ⟨rfl, hSkip⟩ | ⟨_, hLocal, hExec⟩
  · have hSkipAudit := hAudit.1
    simp only [Bool.or_eq_true] at hSkipAudit
    rcases hSkipAudit with hNone | hLess
    · rw [Option.isNone_iff_eq_none.mp hNone] at hSkip
      cases hSkip
    · have := of_decide_eq_true hLess
      change 7955 ≤ s.pc + 1 ∧ s.pc + 1 ≤ site
      omega
  · rcases Softmax.scoreExecLocal hExec with hCore | ⟨_, hSite, _, _⟩
    · have hLocalAudit := hAudit.2
      simp only [hLocal, Bool.not_true, Bool.false_or] at hLocalAudit
      have hPc := hCore.pc
      cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc hLocalAudit
      case bra target uniform =>
        simpa only [decide_eq_true_eq, hPc] using hLocalAudit
      case brx => cases hLocalAudit
      all_goals have hLess := of_decide_eq_true hLocalAudit; omega
    · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
      omega

private theorem ordinaryCode :
    kernel.code.all (fun ins => ins.op.isLocal || ordinaryEvent ins.op) = true := by
  decide +kernel

private theorem beforeStatsEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {site : Nat} (hLo : 7955 ≤ s.pc) (hHi : s.pc < site)
    (he : EStep kernel Assumptions.all l g s e (some u)) : 7955 ≤ u.pc ∧ u.pc ≤ site := by
  obtain ⟨ins, hCode, hNoLocal, hFire⟩ := estep_event_source he
  have hOp := List.all_eq_true.mp ordinaryCode _ (List.mem_of_getElem? hCode)
  have hFrame := ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
    (by simpa only [hNoLocal, Bool.false_or] using hOp)
  rcases callbackFrame_fires hFrame hFire with hNext | hSame <;> omega

private theorem statsBeforeLaterEvent {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {target : Event} {site : Nat}
    (hChecked : beforeSiteChecked site) (hLo : 7955 ≤ s.pc) (hHi : s.pc ≤ site)
    (hWalk : Walk kernel Assumptions.all l g s events visits)
    (hTarget : target ∈ events) (hLate : site < target.pc) :
    ∃ e ∈ events, ∃ source returned, source.pc = site ∧
      EStep kernel Assumptions.all l g source e (some returned) := by
  induction hWalk with
  | stop => simp at hTarget
  | tau hTau _ ih =>
    have hNext := beforeStatsTau hChecked hLo hHi hTau
    exact ih hNext.1 hNext.2 hTarget
  | @ev source _ _ _ _ he _ ih =>
    rcases List.mem_cons.mp hTarget with rfl | hRest
    · have := estep_source_pc he
      omega
    · by_cases hAt : source.pc = site
      · exact ⟨_, List.mem_cons_self, _, _, hAt, he⟩
      · have hNext := beforeStatsEvent hLo (Nat.lt_of_le_of_ne hHi hAt) he
        obtain ⟨e, hMem, source, returned, hSite, hStep⟩ := ih hNext.1 hNext.2 hRest
        exact ⟨e, List.mem_cons_of_mem _ hMem, source, returned, hSite, hStep⟩
  | last he =>
    obtain rfl := List.mem_singleton.mp hTarget
    have := estep_source_pc he
    omega

private theorem statsExitCode (terminal : Bool) (stage : Fin 2) :
    kernel.code[statsExitSite terminal stage]? =
      some ⟨none, .barSyncN (.reg (if stage.val = 0 then 1625 else 1626)) (.imm 64) true⟩ := by
  cases terminal <;> fin_cases stage
  · exact Flow.code_7985
  · exact Flow.code_7988
  · exact Flow.code_8465
  · exact Flow.code_8761

private theorem statsExitEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hBlock : l.block = 512) {terminal : Bool} {stage : Fin 2}
    (hSite : s.pc = statsExitSite terminal stage)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ id, e = ⟨statsExitSite terminal stage, .bar id (some 64) .sync⟩ := by
  obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source he
  rw [hSite, statsExitCode] at hCode
  obtain rfl := Option.some.inj hCode
  change Fires s.pc (barTmpl l g s (.reg (if stage.val = 0 then 1625 else 1626))
    (some (.imm 64)) .sync) e (some u) at hFire
  have hCount : readBits l g s 32 (.imm 64) = .ok 64#64 := rfl
  cases hId : readBits l g s 32 (.reg (if stage.val = 0 then 1625 else 1626)) with
  | error f =>
    simp only [barTmpl, hId] at hFire
    cases hFire.2
  | ok id =>
    by_cases hTooLarge : 16 ≤ id.toNat
    · simp only [barTmpl, hId, hTooLarge, ↓reduceIte] at hFire
      cases hFire.2
    · have hTmpl : barTmpl l g s (.reg (if stage.val = 0 then 1625 else 1626))
          (some (.imm 64)) .sync = .bar id.toNat (next s) (some 64) .sync := by
        simp only [barTmpl, hId, hTooLarge, ↓reduceIte, hCount]
        simp [hBlock]
      rw [hTmpl] at hFire
      exact ⟨_, hFire.1.trans (by rw [hSite])⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem requiredCorrectionEventOfActiveTail {g : Nat} (hWarpLo : 8 ≤ warpIndex l g)
    (hWarpHi : warpIndex l g < 12) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    {site j : Nat} {target : Event} (hChecked : beforeSiteChecked site) (hLo : 7955 ≤ site)
    (hGet : X.get (g,j) = some target) (hLate : site < target.pc) :
    ∃ e ∈ X.tr g, ∃ source returned, source.pc = site ∧
      EStep kernel Assumptions.all l g source e (some returned) := by
  have hg := event_thread_lt hX hGet
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hGet' : X.get (warpLane l g lane,j) = some target := hLane.symm ▸ hGet
  obtain ⟨batch, hb, _, _, _, _, _, active, hActive⟩ :=
    Correction.correctionActiveTileOfEvent hp hX hg hWarpLo hWarpHi hl hWork
      (by omega) hGet'
  have hInput := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨t, hLocal, ht⟩ := Correction.correctionInputRun hp hb (active.checkpoint lane hl)
  have hRun := hInput.after_local_nonempty (run_rtg hLocal) hActive.nonempty
  rw [hLane] at hRun ht
  have hTarget : target ∈ (X.tr g).drop (active.pos lane) := by
    apply List.mem_of_getElem? (i := j - active.pos lane)
    rw [List.getElem?_drop, Nat.add_sub_of_le hActive.before]
    exact hGet
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hRun
  obtain ⟨e, hMem, source, returned, hSource, he⟩ :=
    statsBeforeLaterEvent hChecked ht.1.ge (ht.1.symm ▸ hLo) hWalk hTarget hLate
  exact ⟨e, List.mem_of_mem_drop hMem, source, returned, hSource, he⟩

/-- An active correction lane passes both its initial and terminal statistics waits
before it can exit. This uses only its actual trace and protected scheduling metadata. -/
theorem correctionStatsWaitOfActiveExit {g : Nat} (hWarpLo : 8 ≤ warpIndex l g)
    (hWarpHi : warpIndex l g < 12) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hExit : Exited X g) (terminal : Bool) (stage : Fin 2) :
    ∃ pos, CorrectionWaits X (g,pos) (if terminal then .terminal else .initial) stage := by
  obtain ⟨j, ⟨site,kind⟩, hGet, hKind⟩ := hExit
  change kind = .exit at hKind
  subst kind
  have hSite := actualExitPc hX hGet
  subst site
  obtain ⟨e, hMem, source, returned, hSource, he⟩ :=
    requiredCorrectionEventOfActiveTail hp hX hWarpLo hWarpHi hWork
      (beforeStatsTable terminal stage)
      (by cases terminal <;> fin_cases stage <;> decide) hGet
      (by cases terminal <;> fin_cases stage <;> decide)
  obtain ⟨id, rfl⟩ := statsExitEvent hp.block hSource he
  have he : (⟨statsExitSite terminal stage, .bar id (some 64) .sync⟩ : Event) ∈ X.tr g :=
    hMem
  obtain ⟨pos, hPos⟩ := List.mem_iff_getElem?.mp he
  refine ⟨pos, ?_⟩
  cases terminal
  · exact initialWaitObservation stage hPos
  · exact terminalWaitObservation stage hPos

/-- Before its final allocation arrival, an active correction lane has made both
terminal statistics waits. -/
theorem correctionTerminalStatisticsBeforeFinalArrival {g j : Nat} (hWarpLo : 8 ≤ warpIndex l g)
    (hWarpHi : warpIndex l g < 12) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hArrival : FinalAllocationArrival X (g,j) .arrive) (stage : Fin 2) :
    ∃ i < j, CorrectionWaits X (g,i) .terminal stage := by
  have hGet := hArrival.correctionDecoded hp hX hWarpLo hWarpHi
  obtain ⟨e, hMem, source, returned, hSource, he⟩ :=
    requiredCorrectionEventOfActiveTail hp hX hWarpLo hWarpHi hWork
      (beforeStatsTable true stage) (by fin_cases stage <;> decide) hGet
      (by fin_cases stage <;> decide)
  obtain ⟨id, rfl⟩ := statsExitEvent hp.block hSource he
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hMem
  have hWait : CorrectionWaits X (g,i) .terminal stage := terminalWaitObservation stage hi
  have hBefore : i < j := by
    rcases lt_trichotomy i j with h | rfl | h
    · exact h
    · have hDiff := congrArg Event.kind (Option.some.inj (hGet.symm.trans hi))
      cases hDiff
    · rcases finalArrivalTerminates hp hX hArrival.arrival h hi with hExit | ⟨_, hFault⟩
      · cases hExit
      · cases hFault
  exact ⟨i, hBefore, hWait⟩

/-- An active correction lane's terminal allocation arrival requires an observed output load. -/
theorem correctionFinalOutputLoadOfActiveTail {g j : Nat} (hWarpLo : 8 ≤ warpIndex l g)
    (hWarpHi : warpIndex l g < 12) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    {mode : BarMode} (hGet : X.get (g,j) = some ⟨9204,.bar 2 (some 416) mode⟩) :
    ∃ i address values, X.get (g,i) = some
      ⟨Correction.finalizeLoadPc 1 0, .tc (.ld address values .s32x32b)⟩ := by
  have hAudit : beforeSiteChecked 8776 := by
    unfold beforeSiteChecked
    set_option maxRecDepth 100000 in decide +kernel
  obtain ⟨e, hMem, source, _, hSource, hStep⟩ :=
    requiredCorrectionEventOfActiveTail hp hX hWarpLo hWarpHi hWork
      hAudit (by decide) hGet (by change 8776 < 9204; decide)
  obtain ⟨ins, hc, _, hFire⟩ := estep_event_source hStep
  rw [hSource, Flow.code_8776] at hc
  obtain rfl := Option.some.inj hc.symm
  have hHook : Assumptions.all.any (·.tcLdWait source.pc) = false := by rw [hSource]; decide +kernel
  obtain ⟨addr, values, _, rfl, _⟩ := fires_tcLd (by intro _ h; cases h) hFire hHook
  obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp hMem
  rw [hSource] at he
  exact ⟨i, addr, values, he⟩
end

private def finalizationTensorSite (stage : Fin 2) (chunk : Fin 16) (wait : Bool) : Nat :=
  Correction.finalizeLoadPc stage chunk + if wait then 5 else 0

private def finalizationTensorSites : List Nat :=
  (List.finRange 2).flatMap fun stage =>
    (List.finRange 16).flatMap fun chunk =>
      [finalizationTensorSite stage chunk false, finalizationTensorSite stage chunk true]

private def preservesFinalizationSites (i : Instr) (pc : Nat) : Bool :=
  (i.guard.isNone && !i.op.isLocal || !(finalizationTensorSites.contains pc)) &&
    match i.op with
    | .bra target _ => decide (7955 ≤ target) &&
        !(finalizationTensorSites.any (fun site => decide (pc ≤ site ∧ site < target)))
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem finalizationTensorSitesAudit :
    (((kernel.code.drop 7955).take (9057 - 7955)).zipIdx 7955).all
      (fun (i, atPc) => preservesFinalizationSites i atPc) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem checkedBeforeFinalizationTensor {site : Nat}
    (hSite : site ∈ finalizationTensorSites)
    (hBelow : site < 9057) : beforeSiteChecked site := by
  apply List.all_eq_true.mpr
  rintro ⟨i,atPc⟩ hMem
  obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp hMem
  have hk : k < site+1-7955 := by
    have hLen := (List.getElem?_eq_some_iff.mp hGet).1
    simpa only [List.length_zipIdx] using hLen.trans_le
      (show (((kernel.code.drop 7955).take (site + 1 - 7955)).zipIdx 7955).length ≤
        site + 1 - 7955 by rw [List.length_zipIdx]; exact List.length_take_le ..)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt hk, List.getElem?_drop] at hGet
  have hP : 7955+k = atPc := by
    cases hs : kernel.code[7955+k]? <;> simp_all
  have hI : kernel.code[7955+k]? = some i := by
    cases hs : kernel.code[7955+k]? <;> simp_all
  have hGet' : (((kernel.code.drop 7955).take (9057 - 7955)).zipIdx 7955)[k]? =
      some (i,atPc) := by
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop, hI]
    simp [hP]
  have hAudit := List.all_eq_true.mp finalizationTensorSitesAudit (i,atPc)
    (List.mem_of_getElem? hGet')
  simp only [preservesFinalizationSites, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hAudit
  have hAt : atPc ≤ site := by omega
  have hProtected : atPc = site → i.guard.isNone = true ∧ i.op.isLocal = false := by
    intro he
    rcases hAudit.1 with hGood | hNone
    · exact hGood
    · exact (hNone (he.symm ▸ hSite)).elim
  unfold beforeStats
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.or_eq_true]
    rcases lt_or_eq_of_le hAt with h | h
    · exact .inr (decide_eq_true h)
    · exact .inl (hProtected h).1
  · rw [Bool.or_eq_true]
    by_cases hi : i.op.isLocal = false
    · simp [hi]
    · right
      have hLt : atPc < site := by
        rcases lt_or_eq_of_le hAt with h | h
        · exact h
        · exact (hi (hProtected h).2).elim
      cases hOp : i.op <;> try exact decide_eq_true hLt
      case bra target aligned =>
        rw [hOp] at hAudit
        have hDest := Bool.and_eq_true_iff.mp hAudit.2
        have hLower : 7955 ≤ target := of_decide_eq_true hDest.1
        have hUpper : target ≤ site := by
          simp at hDest
          exact hDest.2 site hSite hAt
        exact decide_eq_true ⟨hLower,hUpper⟩
      case brx => simp [hOp] at hAudit

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j pc : Nat} (hWarpLo : 8 ≤ warpIndex l g)
    (hWarpHi : warpIndex l g < 12) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
include hp hX hWarpLo hWarpHi hWork

/-- A correction lane exits an assigned tile only after returning from its final Tensor Memory
load wait. -/
theorem correctionFinalTensorWaitBeforeExit (hGet : X.get (g,j) = some ⟨pc,.exit⟩) :
    ∃ i < j, X.get (g,i) = some ⟨9043,.tc .waitLd⟩ := by
  obtain rfl := actualExitPc hX hGet
  have hChecked : beforeSiteChecked 9043 := checkedBeforeFinalizationTensor
    (by decide : 9043 ∈ finalizationTensorSites) (by decide)
  obtain ⟨e,hMem,s,u,hSrc,he⟩ := requiredCorrectionEventOfActiveTail hp hX hWarpLo hWarpHi
    hWork hChecked (by decide) hGet (show 9043 < 9205 by decide)
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  rw [hSrc,Flow.code_9043] at hCode
  obtain rfl := Option.some.inj hCode
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hE := fires_tcWaitLd hBlock hFire
  rw [hSrc] at hE
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp (hE ▸ hMem)
  have hLen : j+1 = (X.tr g).length := Execution.exit_last hX (event_thread_lt hX hGet) hGet
  have hILt := (List.getElem?_eq_some_iff.mp hi).1
  have hNe : i ≠ j := by
    intro h
    rw [h,show (X.tr g)[j]? = _ from hGet] at hi
    cases hi
  exact ⟨i,by omega,hi⟩

end PTX.Kernels.TmlFa4Fwd.Thread
