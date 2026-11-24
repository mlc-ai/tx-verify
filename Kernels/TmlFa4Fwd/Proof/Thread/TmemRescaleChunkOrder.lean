-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleLoadSources
import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleCode
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
import Lemmas.Flow.TcLdTmpl
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsRead

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Correction

private def inChunk (stage : Fin 2) (chunk : Fin 8) (site : Nat) : Prop :=
  rescaleLoadPc stage chunk < site ∧ site ≤ rescaleStorePc stage chunk

private instance (stage : Fin 2) (chunk : Fin 8) (site : Nat) :
    Decidable (inChunk stage chunk site) := inferInstanceAs (Decidable (_ ∧ _))

private def chunkBranchCode (o : Op) : Bool :=
  match o with
  | .bra target _ => !decide ((8012 < target ∧ target ≤ 8220) ∨ (8231 < target ∧ target ≤ 8439))
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem chunkBranchAudit : kernel.code.all (fun i =>
      (i.op.isLocal || Epilogue.ordinaryEvent i.op) && chunkBranchCode i.op) = true := by
  kernel_rfl

private theorem cannotJumpToChunk (stage : Fin 2) (chunk : Fin 8) {site : Nat}
    (h : inChunk stage chunk site) :
    (8012 < site ∧ site ≤ 8220) ∨ (8231 < site ∧ site ≤ 8439) := by
  unfold inChunk rescaleLoadPc rescaleStorePc at h
  have hChunk := chunk.isLt
  fin_cases stage <;> omega

private theorem chunkStraightAt (stage : Fin 2) (chunk : Fin 8)
    {site : Nat} {i : Instr} (hInside : inChunk stage chunk site)
    (hHigh : site < rescaleStorePc stage chunk) (hCode : kernel.code[site]? = some i) :
    i.op.isLocal = true := by
  let start := rescaleLoadPc stage chunk+1
  let code := (kernel.code.drop start).take (rescaleStorePc stage chunk-start)
  have hAll : code.all (·.op.isLocal) = true := by
    fin_cases stage <;> fin_cases chunk <;> set_option maxRecDepth 100000 in kernel_rfl
  have hL : start ≤ site := by have := hInside.1; omega
  apply List.all_eq_true.mp hAll i
  apply List.mem_of_getElem? (i := site - start)
  rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hL,hCode]

private theorem chunkTauInside {l : Launch} {g : Nat} {s u : TState}
    (stage : Fin 2) (chunk : Fin 8)
    (ht : Tau kernel Assumptions.all l g s u) (hu : inChunk stage chunk u.pc) :
    inChunk stage chunk s.pc := by
  obtain ⟨i,hCode,_,hLocal⟩ := Softmax.tauScoreSource ht
  have hNoLoad : s.pc ≠ rescaleLoadPc stage chunk := by
    intro hSite
    rw [hSite,rescaleRegisterCode] at hCode
    obtain rfl := Option.some.inj hCode
    rcases hLocal with ⟨_,hSkip⟩ | ⟨_,hL,_⟩
    · cases hSkip
    · cases hL
  have hInNext (hNext : u.pc = s.pc + 1) : inChunk stage chunk s.pc := by
    unfold inChunk at hu ⊢
    omega
  rcases hLocal with ⟨rfl,_⟩ | ⟨_,_,hr⟩
  · exact hInNext rfl
  rcases Softmax.scoreExecLocal hr with hFrame | ⟨seg,hMatch,hM,hSeg⟩
  · have hPc := hFrame.pc
    have ha := (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp chunkBranchAudit i (List.mem_of_getElem? hCode))).2
    cases ho : i.op <;> simp only [ho,nextPc,BrxTarget,or_false] at hPc
    case bra target uni =>
      have hInside := cannotJumpToChunk stage chunk (hPc ▸ hu)
      simp [ho,chunkBranchCode,hInside] at ha
    case brx => simp [ho,chunkBranchCode] at ha
    all_goals exact hInNext hPc
  · have hStop : seg.stop ≤ 7745 := by
      have hAudit : Assumptions.swExp2Sites.all (fun site =>
          match cuteExp2.matchAt kernel site with
          | some seg => decide (seg.stop ≤ 7745)
          | none => false) = true := by decide +kernel
      have h := List.all_eq_true.mp hAudit _ hMatch
      rw [hM] at h
      exact of_decide_eq_true h
    have hPc := (Softmax.scoreSegmentFrame hSeg).1
    unfold inChunk rescaleLoadPc at hu
    omega

private theorem enteringChunkWait {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (chunk : Fin 8)
    (he : EStep kernel Assumptions.all l g s e (some u))
    (hu : inChunk stage chunk u.pc) : e = ⟨rescaleLoadPc stage chunk,.tc .waitLd⟩ := by
  obtain ⟨i,hCode,hNonlocal,hFire⟩ := estep_event_source he
  have hOrdinary : Epilogue.ordinaryEvent i.op = true := by
    have ha := (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp chunkBranchAudit i (List.mem_of_getElem? hCode))).1
    simpa only [hNonlocal,Bool.false_or] using ha
  have hFrame := Epilogue.ordinaryEventFrame
    (A := Assumptions.all) (l := l) (g := g) (s := s) hOrdinary
  let lo := rescaleLoadPc stage chunk
  let hi := rescaleStorePc stage chunk
  have hS : s.pc = lo ∨ s.pc = hi := by
    have hp := callbackFrame_fires hFrame hFire
    have hExcluded : ¬ (inChunk stage chunk s.pc ∧ s.pc < hi) := by
      intro ⟨hL,hH⟩
      rw [chunkStraightAt stage chunk hL hH hCode] at hNonlocal
      cases hNonlocal
    change lo < u.pc ∧ u.pc ≤ hi at hu
    unfold inChunk at hExcluded
    change ¬ ((lo < s.pc ∧ s.pc ≤ hi) ∧ s.pc < hi) at hExcluded
    rcases hp with h | h <;> omega
  rcases hS with hs | hs
  · rw [hs,rescaleRegisterCode] at hCode
    obtain rfl := Option.some.inj hCode
    have hHook : Assumptions.all.any (·.tcLdWait s.pc) = true :=
      hs.symm ▸ rescaleWaitHook stage chunk
    by_cases hz : s.sub = 0
    · have hSame : u.pc = s.pc := by
        simp only [eventTmpl,tcLdTmpl,hHook,hz,ite_true] at hFire
        apply callbackFrame_fires (P := fun (t : TState) => t.pc = s.pc) _ hFire
        have lift {r : Exec Tmpl}
            (h : AllOk (fun tm => CallbackFrame (fun t => t.pc = s.pc) (tm.thenWaitLd s.pc)) r) :
            CallbackFrame (fun t => t.pc = s.pc) ((ofExec r).thenWaitLd s.pc) := by
          cases r <;> exact h
        simp only [tcTmpl,ldResult]
        apply lift
        repeat' first | trivial | (apply allOk_bind; intro v) | split
        intro vals
        rfl
      have hBound : lo < u.pc := hu.1
      omega
    · have hWait := (fires_tcLd_wait hHook hz hFire).1
      rw [hs] at hWait
      exact hWait
  · obtain ⟨ops,hC⟩ := rescaleStoreOpcode stage chunk
    rw [hs,hC] at hCode
    obtain rfl := Option.some.inj hCode
    have hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = false :=
      hs.symm ▸ rescaleStoreHook stage chunk
    rw [eventTmpl_tcSt_noWait hHook] at hFire
    have hNext : u.pc = s.pc + 1 := by
      apply callbackFrame_fires (P := fun (t : TState) => t.pc = s.pc + 1) _ hFire
      simp only [tcTmpl]
      apply ofExec_frame
      repeat' first | exact rfl | trivial | (apply allOk_bind; intro v) | split
    have hBound : u.pc ≤ hi := hu.2
    omega

private theorem chunkWaitTrace {l : Launch} {g : Nat} {s t : TState} {events : List Event}
    (stage : Fin 2) (chunk : Fin 8)
    (hr : TraceReach kernel Assumptions.all l g s events t)
    (hInside : inChunk stage chunk t.pc) :
    (inChunk stage chunk s.pc ∧ events = []) ∨
    ∃ pre, events = pre ++ [⟨rescaleLoadPc stage chunk,.tc .waitLd⟩] := by
  induction hr with
  | refl => exact .inl ⟨hInside,rfl⟩
  | tau ht _ ih =>
    rcases ih hInside with ⟨hs,hNil⟩ | hPast
    · exact .inl ⟨chunkTauInside stage chunk ht hs,hNil⟩
    · exact .inr hPast
  | event he _ ih =>
    rcases ih hInside with ⟨hs,rfl⟩ | ⟨pre,hPast⟩
    · exact .inr ⟨[],by rw [enteringChunkWait stage chunk he hs]; rfl⟩
    · exact .inr ⟨_ :: pre,by rw [List.cons_append,← hPast]⟩

/-- The stage's actual rescale store follows the implicit wait of its own chunk
with no intervening trace event, including in a prefix ending at the store. -/
theorem previousRescaleChunkWait {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {stage : Fin 2} (hStore : OutputRescaleStore X writer stage) :
    ∃ wait, wait.1 = writer.1 ∧ wait.2 + 1 = writer.2 ∧
      ∃ chunk address words shape,
        X.get writer = some ⟨rescaleStorePc stage chunk,.tc (.st address words shape)⟩ ∧
        X.get wait = some ⟨rescaleLoadPc stage chunk,.tc .waitLd⟩ := by
  obtain ⟨g,j⟩ := writer
  obtain ⟨chunk,address,words,shape,he⟩ := hStore.decoded
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s,_,hTrace,hStep⟩ := hr.before_event he
  have hPc : s.pc = rescaleStorePc stage chunk := (estep_source_pc hStep).symm
  have hCut : inChunk stage chunk s.pc := by
    rw [hPc]
    exact ⟨by unfold rescaleLoadPc rescaleStorePc; split <;> omega,le_rfl⟩
  rcases chunkWaitTrace stage chunk hTrace hCut with ⟨hs,_⟩ | ⟨pre,hTrace'⟩
  · have hBad : rescaleLoadPc stage chunk < 0 := hs.1
    omega
  · have hIndex : pre.length + 1 = j := by
      have hl := congrArg List.length hTrace'
      have hj := len_of_get he
      simpa only [List.length_take,List.length_append,List.length_singleton,Nat.min_eq_left hj.le]
        using hl.symm
    have hAt : X.get (g,pre.length) = some ⟨rescaleLoadPc stage chunk,.tc .waitLd⟩ := by
      change (X.tr g)[pre.length]? = _
      rw [← List.getElem?_take_of_lt (show pre.length < j by omega),hTrace',
        List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero]
    exact ⟨(g,pre.length),rfl,hIndex,chunk,address,words,shape,he,hAt⟩

private theorem rescaleZeroIssuesLoad {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (chunk : Fin 8) (hAt : s.pc = rescaleLoadPc stage chunk)
    (he : EStep kernel Assumptions.all l g s e (some u))  (hs : s.sub = 0) :
    ∃ address words, e = ⟨rescaleLoadPc stage chunk,.tc (.ld address words .s32x32b)⟩ := by
  obtain ⟨i,hCode,_,hFire⟩ := estep_event_source he
  rw [hAt,rescaleRegisterCode] at hCode
  obtain rfl := Option.some.inj hCode
  have hHook : Assumptions.all.any (·.tcLdWait s.pc) = true :=
    hAt.symm ▸ rescaleWaitHook stage chunk
  simp only [eventTmpl,tcLdTmpl,hHook,hs,ite_true] at hFire
  rw [tcTmpl_tcLd_none (by intro sh h; cases h)] at hFire
  cases hRead : readBits l g s 32 (.reg (rescaleAddressReg stage chunk)) with
  | error f =>
    simp [ofExec,hRead,bind,Except.bind,throw,throwThe,MonadExceptOf.throw,
      Tmpl.thenWaitLd,Fires] at hFire
    split_ifs at hFire <;> cases hFire.2
  | ok bits =>
    simp [ofExec,hRead,bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw,
      Tmpl.thenWaitLd,Fires] at hFire
    split_ifs at hFire
    all_goals first
      | (obtain ⟨words,_,rfl,_⟩ := hFire; exact ⟨_,words,by rw [hAt]⟩)
      | cases hFire.2

private theorem rescaleLoadSubstep {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (chunk : Fin 8) (hAt : s.pc = rescaleLoadPc stage chunk)
    (he : EStep kernel Assumptions.all l g s e (some u)) (hSub : u.sub ≠ 0) :
    ∃ address words, e = ⟨rescaleLoadPc stage chunk,.tc (.ld address words .s32x32b)⟩ := by
  obtain ⟨i,hCode,_,hFire⟩ := estep_event_source he
  rw [hAt,rescaleRegisterCode] at hCode
  obtain rfl := Option.some.inj hCode
  have hHook : Assumptions.all.any (·.tcLdWait s.pc) = true :=
    hAt.symm ▸ rescaleWaitHook stage chunk
  by_cases hs : s.sub = 0
  · exact rescaleZeroIssuesLoad stage chunk hAt he hs
  · have hNext := (fires_tcLd_wait hHook hs hFire).2
    exact (hSub (by rw [hNext])).elim

private theorem previousLoadOfChunkWait {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) (chunk : Fin 8) {g j : Nat}
    (hWarpLo : 8 ≤ Prologue.warpIndex l g) (hWarpHi : Prologue.warpIndex l g < 12)
    (hWait : X.get (g,j) = some ⟨rescaleLoadPc stage chunk,.tc .waitLd⟩) :
    ∃ k address words, k + 1 = j ∧
      X.get (g,k) = some ⟨rescaleLoadPc stage chunk,.tc (.ld address words .s32x32b)⟩ := by
  let load := rescaleLoadPc stage chunk
  let mark (pos : Nat) (s : TState) :=
    SetupScratch s ∧ (s.pc = load → s.sub ≠ 0 →
      ∃ k address words, k+1 = pos ∧
        X.get (g,k) = some ⟨load,.tc (.ld address words .s32x32b)⟩)
  have hLo : 173 < load := by dsimp [load,rescaleLoadPc]; omega
  have hHi : load < 9205 := by
    change rescaleLoadPc stage chunk < 9205
    fin_cases stage <;> fin_cases chunk <;> decide
  obtain ⟨s,result,_,hs,_,hMark,hFire,_⟩ :=
    correctionRoleEventAt hp hX hWarpLo hWarpHi hWait hLo hHi
    (Q := mark)
    (by intro s hs; exact ⟨SetupScratch.clear hs.2.1 hs.2.2.1,fun _ h => (h hs.2.1).elim⟩)
    (by
      intro s u ev pos hLo hHi hSub hBefore hStep hActual
      have hScratch := correctionScratchStep hLo hHi hSub hBefore.1 hStep
      refine ⟨hScratch.1, fun hPc hPartial => ?_⟩
      have hSame : u.pc = s.pc := by
        by_contra hDiff
        exact hPartial (hScratch.2 (.inr hDiff))
      rcases hStep with ⟨rfl,_⟩ | ⟨event,rfl,he⟩
      · exact (hPartial (hScratch.2 (.inl rfl))).elim
      obtain ⟨address,words,hEvent⟩ := rescaleLoadSubstep stage chunk (hSame.symm.trans hPc) he
        hPartial
      exact ⟨pos,address,words,rfl,hEvent ▸ hActual event (by simp)⟩)
  apply hMark.2 hs
  intro hSub
  cases result with
  | none =>
    obtain ⟨_,_,hf⟩ := hFire
    have hEnds := fires_none_ends hf
    simp [Ends] at hEnds
  | some u =>
    obtain ⟨_,_,hEq⟩ := rescaleZeroIssuesLoad stage chunk hs hFire hSub
    cases congrArg Event.kind hEq

theorem previousRescaleChunkLoadDecoded {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {stage : Fin 2} (hStore : OutputRescaleStore X writer stage) :
    ∃ (load : EvId) (chunk : Fin 8) (address : Nat) (words : List Value),
      load.1 = writer.1 ∧ load.2 + 2 = writer.2 ∧
      X.get load = some ⟨rescaleLoadPc stage chunk,.tc (.ld address words .s32x32b)⟩ := by
  have hWarp := hStore.correctionRole hp hX
  obtain ⟨⟨g,j⟩,hLane,hIndex,chunk,_,_,_,_,hWait⟩ := previousRescaleChunkWait hX hStore
  obtain ⟨k,address,words,hIndex',hLoad⟩ :=
    previousLoadOfChunkWait hp hX stage chunk (by rw [show g = writer.1 from hLane]; exact hWarp.1)
      (by rw [show g = writer.1 from hLane]; exact hWarp.2) hWait
  exact ⟨(g,k),chunk,address,words,hLane,by omega,hLoad⟩

/-- The two actual events between the chunk's read boundary and its store
cannot advance the correction statistics ordinal. -/
theorem OutputRescaleStore.previousChunkLoadWithStatistics {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {stage : Fin 2} (hStore : OutputRescaleStore X writer stage) :
    ∃ load, load.1 = writer.1 ∧ load.2 + 2 = writer.2 ∧ OutputRescaleLoad X load stage ∧
      (correctionBefore X load).barrier (statsBarrierId l load.1 stage) =
        (correctionBefore X writer).barrier (statsBarrierId l writer.1 stage) := by
  obtain ⟨g,index⟩ := writer
  obtain ⟨⟨g₁,pos⟩,chunk,address,words,hLane,hPos,hLoad⟩ :=
    previousRescaleChunkLoadDecoded hp hX hStore
  obtain ⟨⟨g₂,wait⟩,hLane',hWait,k,_,_,_,hOut,hWaitGet⟩ := previousRescaleChunkWait hX hStore
  change g₁ = g at hLane
  change g₂ = g at hLane'
  subst g₁ g₂
  change wait+1 = index at hWait
  change pos+2 = index at hPos
  have hAdj : pos+1 = wait := by omega
  rw [← hAdj] at hWaitGet
  have hQuiet (c : Fin 8) (kind : Kind) :
      correctionStatsWaitMark stage ⟨rescaleLoadPc stage c,kind⟩ = false := by
    by_cases hMarked : correctionStatsWaitMark stage ⟨rescaleLoadPc stage c,kind⟩ = true
    · have hSite := (correctionStatsWaitMark_iff stage _).mp hMarked
      exact ((by fin_cases stage <;> fin_cases c <;> decide :
        rescaleLoadPc stage c ∉ correctionStatsSites stage) hSite).elim
    · exact Bool.eq_false_of_not_eq_true hMarked
  have hRead := countP_take_succ_false hLoad (hQuiet chunk _)
  have hAwait := countP_take_succ_false hWaitGet (hQuiet k _)
  have hRole := hStore.correctionRole hp hX
  refine ⟨(g,pos),rfl,hPos,OutputRescaleLoad.ofDecoded chunk hLoad,?_⟩
  rw [correctionBarrierOrdinal,correctionBarrierOrdinal,
    ← correctionWaitPrefixCount hp hX stage (len_of_get hLoad) hRole,
    ← correctionWaitPrefixCount hp hX stage (len_of_get hOut) hRole]
  rw [← hPos,hAwait,hRead]

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
