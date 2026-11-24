-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
public import Kernels.TmlFa4Fwd.Proof.Thread.Correction

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Prologue Epilogue

private def stageOneNext (site : Nat) : Bool :=
  decide (7986 ≤ site ∧ site ≤ 7988 ∨ 8007 ≤ site ∧ site ≤ 8225 ∨
    8466 ≤ site ∧ site ≤ 8761)

private def stageMark (stage : Fin 2) (site : Nat) : Bool :=
  (Correction.correctionStatsSites stage).contains site

private theorem stageSequential (site : Nat) :
    (stageOneNext (site + 1)).toNat + (stageMark 1 site).toNat =
      (stageOneNext site).toNat + (stageMark 0 site).toNat := by
  have asIf (b : Bool) : b.toNat = if b then 1 else 0 := by cases b <;> rfl
  have hZero : stageMark 0 site = true ↔ site = 7985 ∨ site = 8006 ∨ site = 8465 := by
    simp [stageMark, Correction.correctionStatsSites]
  have hOne : stageMark 1 site = true ↔ site = 7988 ∨ site = 8225 ∨ site = 8761 := by
    simp [stageMark, Correction.correctionStatsSites]
  simp only [stageOneNext, asIf, decide_eq_true_eq, hZero, hOne]
  split_ifs <;> omega

private def stageControl (i : Instr) (site : Nat) : Bool :=
  (i.op.isLocal || ordinaryEvent i.op) &&
  (!(stageMark 0 site || stageMark 1 site) || i.guard.isNone && barOp i.op) &&
  match i.op with
  | .bra dst _ => stageOneNext dst == stageOneNext site
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem stageTable :
    kernel.code.zipIdx.all (fun (i, site) => stageControl i site) = true := by kernel_rfl

private theorem stageLookup {i : Instr} {site : Nat} (hCode : kernel.code[site]? = some i) :
    stageControl i site = true :=
  List.all_eq_true.mp stageTable _ (List.mk_mem_zipIdx_iff_getElem?.mpr hCode)

set_option maxRecDepth 100000 in
private theorem stagesKeepAcrossSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => stageOneNext seg.stop == stageOneNext site
      | none => false) = true := by kernel_rfl

private theorem stageVisitTau {l : Launch} {g : Nat} {s u : TState}
    (ht : Tau kernel Assumptions.all l g s u) : stageOneNext u.pc = stageOneNext s.pc := by
  obtain ⟨ins, hc, _, hExec⟩ := Softmax.tauScoreSource ht
  have hAudit := stageLookup hc
  simp only [stageControl, Bool.and_eq_true] at hAudit
  have hMark : (stageMark 0 s.pc || stageMark 1 s.pc) = false := by
    by_contra h
    simp only [Bool.not_eq_false] at h
    have hc := hAudit.1.2
    simp only [h, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hc
    rcases hExec with ⟨_, hs⟩ | ⟨_, hl, _⟩
    · rw [Option.isNone_iff_eq_none.mp hc.1] at hs
      cases hs
    · have hNonlocal : ins.op.isLocal = false := by
        have hBar := hc.2
        cases hOp : ins.op <;> simp only [hOp, barOp, Bool.false_eq_true] at hBar
        all_goals rfl
      rw [hNonlocal] at hl
      cases hl
  have hMarks := Bool.or_eq_false_iff.mp hMark
  have hNext : stageOneNext (s.pc + 1) = stageOneNext s.pc := by
    have h := stageSequential s.pc
    rw [hMarks.1, hMarks.2] at h
    cases hs : stageOneNext s.pc <;> cases ht : stageOneNext (s.pc+1) <;> simp_all
  rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
  · exact hNext
  · rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨seg, hSite, hMatch, hSeg⟩
    · have hCode := hAudit.2
      have hPc := hFrame.pc
      cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc hCode
      case bra dst uni => exact hPc.symm ▸ eq_of_beq hCode
      case brx => contradiction
      all_goals exact hPc.symm ▸ hNext
    · have h := List.all_eq_true.mp stagesKeepAcrossSegments _ hSite
      rw [hMatch] at h
      exact (Softmax.scoreSegmentFrame hSeg).1.symm ▸ eq_of_beq h

private theorem stageVisitEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    (stageOneNext u.pc).toNat + (stageMark 1 e.pc).toNat =
      (stageOneNext s.pc).toNat + (stageMark 0 e.pc).toNat := by
  rw [estep_source_pc he]
  obtain ⟨ins, hc, hNonlocal, hFires⟩ := estep_event_source he
  have hAudit := stageLookup hc
  simp only [stageControl, Bool.and_eq_true] at hAudit
  by_cases hMarked : (stageMark 0 s.pc || stageMark 1 s.pc) = true
  · have hOp := hAudit.1.2
    simp only [hMarked, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hOp
    rw [followsMarkedBarrier rfl hc hOp.2 he]
    exact stageSequential s.pc
  · have hMarks := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hMarked)
    have hFrame := ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
      (by simpa only [hNonlocal, Bool.false_or] using hAudit.1.1)
    rcases callbackFrame_fires hFrame hFires with hPc | hPc
    · rw [hPc, hMarks.1, hMarks.2]
    · rw [hPc]
      exact stageSequential s.pc

private theorem stageReach {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events u) :
    (stageOneNext u.pc).toNat + events.countP (Correction.correctionStatsWaitMark 1) =
      (stageOneNext s.pc).toNat + events.countP (Correction.correctionStatsWaitMark 0) := by
  induction h with
  | refl => simp
  | tau hTau _ ih => simpa only [stageVisitTau hTau] using ih
  | @event s v u rest e he _ ih =>
    have hEvent := stageVisitEvent he
    have asIf (b : Bool) : b.toNat = if b then 1 else 0 := by cases b <;> rfl
    have hMark (stage : Fin 2) :
        Correction.correctionStatsWaitMark stage e = stageMark stage e.pc :=
      Bool.eq_iff_iff.mpr ((Correction.correctionStatsWaitMark_iff stage e).trans
        List.contains_iff_mem.symm)
    rw [List.countP_cons, List.countP_cons, ← asIf, ← asIf, hMark 0, hMark 1]
    omega

private theorem statsWaitSite {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} {round : CorrectionRound} {stage : Fin 2}
    (he : X.get i = some e) (ha : correctionAction e = some (.statsWait round stage)) :
    e.pc ∈ Correction.correctionStatsSites stage := by
  have hk := correctionStatsWait hp hX he ha
  obtain ⟨site, kind⟩ := e
  change kind = _ at hk
  subst kind
  obtain ⟨hSite, hCount, hMode, _, _⟩ := actualNamedBarrier hp hX he
  rcases count64StatsSites hSite hCount.symm with hScore | ⟨other, hStats⟩
  · simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hScore
    rcases hScore with rfl | rfl | rfl | rfl <;> cases hMode
  · have hId := Correction.actualCorrectionStatsBarrierId hp hX other hStats he
    have hEq : stage = other := Fin.ext (by unfold Correction.statsBarrierId at hId; omega)
    exact hEq.symm ▸ hStats

/-- The two statistics stages alternate in a correction lane's actual prefix. At its wait for
stage 1 it has made exactly one more stage-0 arrival; at stage 0 the cursors agree. -/
theorem correctionStatsStageBalance {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {round : CorrectionRound} {stage : Fin 2}
    (hWait : CorrectionWaits X i round stage) :
    (8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12) ∧
      (correctionBefore X i).barrier (Correction.statsBarrierId l i.1 0) =
        (correctionBefore X i).barrier (Correction.statsBarrierId l i.1 1) + stage.val := by
  obtain ⟨e, he, ha⟩ := hWait
  have hSite := statsWaitSite hp hX he ha
  have hRange := correctionStatsWaitSiteBounds ha
  have hNoHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hNoHint
  have hWarp : 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  refine ⟨hWarp, ?_⟩
  obtain ⟨_, hRun⟩ := hX.thr i.1 (event_thread_lt hX he)
  obtain ⟨u, _, hReach, hStep⟩ := hRun.before_event he
  have hPhase : (stageOneNext u.pc).toNat = stage.val := by
    rw [← estep_source_pc hStep]
    fin_cases stage <;> simp [Correction.correctionStatsSites] at hSite
    all_goals rcases hSite with h | h | h <;> rw [h] <;> decide
  have hInitial : stageOneNext ({} : TState).pc = false := rfl
  have hBalance := stageReach hReach
  rw [hPhase, hInitial] at hBalance
  have hLen := (List.getElem?_eq_some_iff.mp he).1
  rw [Correction.correctionWaitPrefixCount hp hX 0 hLen hWarp,
    Correction.correctionWaitPrefixCount hp hX 1 hLen hWarp] at hBalance
  rw [correctionBarrierOrdinal, correctionBarrierOrdinal]
  simpa [Nat.add_comm] using hBalance.symm

end PTX.Kernels.TmlFa4Fwd.Thread
