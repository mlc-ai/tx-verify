-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleChunkInputs
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsRead
import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleNumerics
import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents
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
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.MemTmpl
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Correction
open Softmax (scoreEventWrites)

private def alphaPackPc (stage : Fin 2) : Nat := 8021 + 219 * stage.val

private def alphaPack (stage : Fin 2) : Op :=
  .move ⟨.pack,.int .b 64,[some (rescaleAlphaPair stage)],
    [.reg (statsReg stage .alpha),.reg (statsReg stage .alpha)]⟩

private theorem alphaPackCode (stage : Fin 2) :
    kernel.code[alphaPackPc stage]? = some ⟨none,alphaPack stage⟩ := by
  fin_cases stage
  · exact Flow.code_8021
  · exact Flow.code_8240

private def alphaScope (stage : Fin 2) (site : Nat) : Prop :=
  statsPc stage .alpha < site ∧ site ≤ rescaleStorePc stage 7

private instance (stage : Fin 2) (site : Nat) : Decidable (alphaScope stage site) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def priorAlphaRead (X : Execution) (g : Nat) (stage : Fin 2)
    (pos : Nat) (word : Value) : Prop :=
  ∃ j < pos, ∃ acc bytes, StatisticsRead X (g,j) stage .alpha acc bytes ∧
    rebuild 3 bytes = .ok word ∧
    ((X.tr g).take j).countP (correctionStatsWaitMark stage) =
      ((X.tr g).take pos).countP (correctionStatsWaitMark stage)

private def alphaFrame (X : Execution) (g : Nat) (stage : Fin 2) (pos : Nat)
    (s : TState) : Prop :=
  alphaScope stage s.pc → ∃ word alpha,
    RescaleFactorWord word alpha ∧ s.regs (statsReg stage .alpha) = some word ∧
    (alphaPackPc stage < s.pc → s.regs (rescaleAlphaPair stage) =
      some (joinValue word word)) ∧
    priorAlphaRead X g stage pos word

private theorem alphaScopeNotStatistics (stage : Fin 2) (e : Event)
    (hLo : statsPc stage .alpha ≤ e.pc) (hHi : e.pc ≤ rescaleStorePc stage 7) :
    correctionStatsWaitMark stage e = false := by
  by_cases h : correctionStatsWaitMark stage e = true
  · have hSite := (correctionStatsWaitMark_iff stage e).mp h
    have audit : (correctionStatsSites stage).all
        (fun n => !decide (statsPc stage .alpha ≤ n ∧ n ≤ rescaleStorePc stage 7)) = true := by
      fin_cases stage <;> decide
    have ha := List.all_eq_true.mp audit _ hSite
    simp [hLo,hHi] at ha
  · exact Bool.eq_false_of_not_eq_true h

private def alphaBranch (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
  match i.op with
  | .bra target _ => !decide (alphaScope 0 target ∨ alphaScope 1 target)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem alphaBranchAudit : kernel.code.all alphaBranch = true := by kernel_rfl

private def alphaKeeps (stage : Fin 2) (pos : Nat) (i : Instr) : Bool :=
  (!((writesRegs i.op ++ scoreEventWrites i.op).contains (statsReg stage .alpha))) &&
    (pos == alphaPackPc stage ||
      !((writesRegs i.op ++ scoreEventWrites i.op).contains (rescaleAlphaPair stage))) &&
    (i.op.isLocal || correctionReturningOp i.op)

set_option maxRecDepth 100000 in
private theorem alphaKeepAudit (stage : Fin 2) :
    (((kernel.code.drop (statsPc stage .alpha + 1)).take
      (rescaleStorePc stage 7 - statsPc stage .alpha)).zipIdx
      (statsPc stage .alpha + 1)).all (fun (i,pos) => alphaKeeps stage pos i) = true := by
  fin_cases stage <;> kernel_rfl

private theorem alphaKeepAt (stage : Fin 2) {pos : Nat} {i : Instr}
    (hScope : alphaScope stage pos) (hCode : kernel.code[pos]? = some i) :
    alphaKeeps stage pos i = true := by
  apply List.all_eq_true.mp (alphaKeepAudit stage) (i,pos)
  apply List.mem_of_getElem? (i := pos - (statsPc stage .alpha + 1))
  have hLo : statsPc stage .alpha + 1 ≤ pos := hScope.1
  have hHi := hScope.2
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hCode]
  rfl

private theorem packAlpha {l : Launch} {g : Nat} {s u : TState} {word : Value}
    (stage : Fin 2) (hAt : s.pc = alphaPackPc stage)
    (hRead : s.regs (statsReg stage .alpha) = some word) (hWidth : word.bytes = 4)
    (hf : s.fault = none) (ht : Tau kernel Assumptions.all l g s u) :
    u.regs (rescaleAlphaPair stage) = some (joinValue word word) := by
  have hc : kernel.code[s.pc]? = some ⟨none,alphaPack stage⟩ := hAt.symm ▸ alphaPackCode stage
  have hPc : 8012 ≤ s.pc := by rw [hAt]; fin_cases stage <;> decide
  have hr := exec_pack (L := l) (g := g) (d := rescaleAlphaPair stage) numericPack hRead hRead
    (correctionSegFree hPc)
  rw [← Assumptions.execLocalA_all_eq_numeric] at hr
  simp only [hWidth,and_self,ite_true] at hr
  obtain rfl := tau_det ht (out_tau hf hc rfl rfl hr)
  simp [next,setReg]

/-- Each actual correction read of a rescale factor returns one finite FP32 word. -/
def RescaleStatisticsAreF32 (X : Execution) : Prop :=
  ∀ read stage access bytes, StatisticsRead X read stage .alpha access bytes →
    ∃ word alpha, rebuild 3 bytes = .ok word ∧ RescaleFactorWord word alpha

private theorem alphaFrameStep {l : Launch} {X : Execution} {g pos : Nat}
    {s u : TState} {ev : Option Event} (stage : Fin 2)
    (hReads : RescaleStatisticsAreF32 X) (hLo : 7745 ≤ s.pc) (hSub : s.sub ≤ 3)
    (hAcc : s.acc = []) (hs : alphaFrame X g stage pos s)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e ∈ ev.toList, X.get (g,pos) = some e) :
    alphaFrame X g stage (pos+ev.toList.length) u := by
  intro hu
  let a := statsReg stage .alpha
  let pair := rescaleAlphaPair stage
  have finish {i : Instr} (hc : kernel.code[s.pc]? = some i) (hSrc : alphaScope stage s.pc)
      (hRegs : ∀ r, r ∉ writesRegs i.op ++ scoreEventWrites i.op → u.regs r = s.regs r)
      (hPack : s.pc = alphaPackPc stage → ∀ word : Value, s.regs a = some word →
        word.bytes = 4 → u.regs pair = some (joinValue word word))
      (hFall : u.pc = s.pc ∨ u.pc = s.pc+1)
      (hAdvance : ((X.tr g).take (pos+ev.toList.length)).countP
        (correctionStatsWaitMark stage) = ((X.tr g).take pos).countP
          (correctionStatsWaitMark stage)) :
      ∃ word x, RescaleFactorWord word x ∧ u.regs a = some word ∧
        (alphaPackPc stage < u.pc → u.regs pair = some (joinValue word word)) ∧
        priorAlphaRead X g stage (pos+ev.toList.length) word := by
    obtain ⟨word,x,hWord,hRead,hPair,j,hBefore,acc,bytes,hTrace,hValue,hRank⟩ := hs hSrc
    have hKeep := alphaKeepAt stage hSrc hc
    simp only [alphaKeeps,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
      decide_eq_false_iff_not] at hKeep
    refine ⟨word,x,hWord,(hRegs a hKeep.1.1).trans hRead,(fun hLive => ?_),
      j,by omega,acc,bytes,hTrace,hValue,hRank.trans hAdvance.symm⟩
    by_cases hNow : s.pc = alphaPackPc stage
    · exact hPack hNow word hRead hWord.width
    · have hOld : alphaPackPc stage < s.pc := by rcases hFall with h | h <;> omega
      have hUnwritten : pair ∉ writesRegs i.op ++ scoreEventWrites i.op := by
        simpa only [beq_eq_false_iff_ne.mpr hNow, Bool.false_or, Bool.not_eq_true',
          decide_eq_false_iff_not] using hKeep.1.2
      exact (hRegs pair hUnwritten).trans (hPair hOld)
  have hFrom (hp : u.pc = s.pc ∨ u.pc = s.pc+1) :
      s.pc = statsPc stage .alpha ∨ alphaScope stage s.pc := by
    have hLow := hu.1
    have hHigh := hu.2
    unfold alphaScope
    rcases hp with h | h <;> omega
  rcases hStep with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false]
      omega
    obtain ⟨i,hc,hf,hTau⟩ := correctionTauFrame hOff ht
    have hNoRead (hRead : s.pc = statsPc stage .alpha) : False := by
      rw [hRead] at hc
      fin_cases stage
      · change kernel.code[8007]? = some i at hc
        rw [Flow.code_8007] at hc
        obtain rfl := Option.some.inj hc.symm
        rcases hTau with ⟨_,hGuard⟩ | ⟨_,hLocal,_⟩
        · cases hGuard
        · cases hLocal
      · change kernel.code[8226]? = some i at hc
        rw [Flow.code_8226] at hc
        obtain rfl := Option.some.inj hc.symm
        rcases hTau with ⟨_,hGuard⟩ | ⟨_,hLocal,_⟩
        · cases hGuard
        · cases hLocal
    have hKeep {u : TState} (ht : Tau kernel Assumptions.all l g s u)
        (hSeed : s.pc = alphaPackPc stage) (word : Value) (hReg : s.regs a = some word)
        (hWidth : word.bytes = 4) : u.regs pair = some (joinValue word word) :=
      packAlpha stage hSeed hReg hWidth hf ht
    rcases hTau with ⟨rfl,_⟩ | ⟨_,_,hl⟩
    · exact finish hc ((hFrom (.inr rfl)).resolve_left hNoRead) (by intros; rfl)
        (hKeep ht) (.inr rfl) rfl
    have hp := hl.pc
    have hb := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp alphaBranchAudit i
      (List.mem_of_getElem? hc))).2
    have hFall : u.pc = s.pc + 1 := by
      cases ho : i.op <;> simp only [ho,nextPc,BrxTarget,or_false] at hp
      case bra dest uni =>
        have hr : alphaScope 0 dest ∨ alphaScope 1 dest := by
          fin_cases stage
          · exact .inl (hp ▸ hu)
          · exact .inr (hp ▸ hu)
        simp [ho,hr] at hb
      case brx => simp [ho] at hb
      all_goals exact hp
    exact finish hc ((hFrom (.inr hFall)).resolve_left hNoRead)
      (fun r hr => hl.regs r (fun hm => hr (List.mem_append_left _ hm)))
      (hKeep ht) (.inr hFall) rfl
  · obtain ⟨i,hc,hLocal,hFire⟩ := estep_event_source he
    have hOrdinary := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp alphaBranchAudit i
      (List.mem_of_getElem? hc))).1
    simp only [hLocal,Bool.false_or] at hOrdinary
    have hEventFrame := Epilogue.ordinaryEventFrame
      (A := Assumptions.all) (l := l) (g := g) (s := s) hOrdinary
    have hFall := callbackFrame_fires hEventFrame hFire
    have hAt := hActual e (by simp)
    have hStepPc := estep_source_pc he
    have hBefore := hFrom hFall
    have hE₀ : statsPc stage .alpha ≤ e.pc := by
      rw [hStepPc]
      exact hBefore.elim (fun h => h.ge) (fun h => h.1.le)
    have hE₁ : e.pc ≤ rescaleStorePc stage 7 := by
      rw [hStepPc]
      have hEnd := hu.2
      rcases hFall with h | h <;> omega
    have hRank := countP_take_succ_false hAt (alphaScopeNotStatistics stage e hE₀ hE₁)
    rcases hBefore with hRead | hSrc
    · obtain ⟨access,bytes,hEvent,rfl⟩ := statisticsReadStep stage .alpha hRead he
      have hOccurrence : StatisticsRead X (g,pos) stage .alpha access bytes :=
        hAt.trans (congrArg some hEvent)
      obtain ⟨word,x,hValue,hWord⟩ := hReads _ _ _ _ hOccurrence
      have hNext := afterLoad_last hValue (show ¬ s.sub+1 < [a].length by simp)
      refine ⟨word,x,hWord,?_,?_,pos,by simp,access,bytes,hOccurrence,hValue,hRank.symm⟩
      · change (afterLoad s [a] bytes).regs a = _
        rw [hNext]
        simp [hAcc,setRegs,setReg]
      · intro hAfter
        have hp : (afterLoad s [a] bytes).pc = s.pc+1 := by rw [hNext]
        have hRange : statsPc stage .alpha + 1 ≤ alphaPackPc stage := by
          fin_cases stage <;> decide
        change alphaPackPc stage < (afterLoad s [a] bytes).pc at hAfter
        omega
    · have hChecked := alphaKeepAt stage hSrc hc
      simp only [alphaKeeps,Bool.and_eq_true,hLocal,Bool.false_or] at hChecked
      refine finish hc hSrc (fun r hr => (correctionEventProgress hc hChecked.2 hSub
        (fun h => hr (List.mem_append_right _ h)) he).2) ?_ hFall hRank
      intro hSite
      rw [hSite,alphaPackCode] at hc
      obtain rfl := Option.some.inj hc
      fin_cases stage <;> cases hLocal

/-- The loaded rescale coefficient is sourced from an actual ordinary read
in the same correction statistics visit. -/
theorem rescaleLoadFactorOfStatisticsRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hReads : RescaleStatisticsAreF32 X)
    {g position address : Nat} {stage : Fin 2} {chunk : Fin 8} {words : List Value}
    (he : X.get (g,position) = some ⟨rescaleLoadPc stage chunk,.tc (.ld address words .s32x32b)⟩) :
    ∃ (t : TState) (ending : Option TState) (word : Value) (alpha : ℝ),
      At t (rescaleLoadPc stage chunk) [] ∧
      t.regs (rescaleAddressReg stage chunk) =
        some (b32 (outputAddress l g stage (16 * chunk.val))) ∧
      RescaleFactorWord word alpha ∧
      (if chunk.val = 0 then t.regs (statsReg stage .alpha) = some word
        else t.regs (rescaleAlphaPair stage) = some (joinValue word word)) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop position) ending ∧
      ∃ j < position, ∃ acc bytes, StatisticsRead X (g,j) stage .alpha acc bytes ∧
        rebuild 3 bytes = .ok word ∧
        (correctionBefore X (g,j)).barrier (statsBarrierId l g stage) =
          (correctionBefore X (g,position)).barrier (statsBarrierId l g stage) := by
  obtain ⟨t,ending,ht,hAddr,hRun,hFactor⟩ := actualRescaleLoadStateWith hp hX stage chunk he
    (Q := fun pos s => alphaFrame X g stage pos s)
    (by
      intro t ht h
      rw [ht.1] at h
      exact (show ¬ alphaScope stage 7745 from by fin_cases stage <;> decide) h |>.elim)
    (fun hLo _ hSub hAcc hb hw hActual => alphaFrameStep stage hReads hLo hSub hAcc hb hw hActual)
  have hRange : alphaScope stage (rescaleLoadPc stage chunk) := by
    fin_cases stage <;> fin_cases chunk <;> decide
  obtain ⟨word,x,hWord,ha,hPair,j,hBefore,acc,bytes,hTrace,hValue,hRank⟩ :=
    hFactor (ht.1.symm ▸ hRange)
  refine ⟨t,ending,word,x,ht,hAddr,hWord,?_,hRun,j,hBefore,acc,bytes,hTrace,hValue,?_⟩
  · by_cases hc : chunk.val = 0
    · simpa only [ite_eq_left hc] using ha
    · rw [ite_eq_right hc]
      apply hPair
      rw [ht.1]
      have hChunk : 0 < chunk.val := Nat.pos_of_ne_zero hc
      unfold rescaleLoadPc alphaPackPc
      omega
  · have hRole := (OutputRescaleLoad.ofDecoded chunk he).correctionRole hp hX
    rw [correctionBarrierOrdinal,correctionBarrierOrdinal,
      ← correctionWaitPrefixCount hp hX stage (hBefore.trans (len_of_get he)) hRole,
      ← correctionWaitPrefixCount hp hX stage (len_of_get he) hRole]
    exact hRank

/-- Once the actual row's statistics bytes are finite FP32, both the scalar and
packed factor of each rescale chunk are fixed on its actual prefix. -/
theorem finiteRescaleFactorsOfReads {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hReads : RescaleStatisticsAreF32 X) : FiniteRescaleFactors l X := by
  intro g position stage chunk address words he
  obtain ⟨t,ending,word,alpha,ht,hAddr,hWord,hReg,hRun,_⟩ :=
    rescaleLoadFactorOfStatisticsRead hp hX hReads he
  exact ⟨t,ending,word,alpha,ht,hAddr,hWord,hReg,hRun⟩

/-- An actual rescale store's entry uses the observed alpha read of that same
correction visit on the same lane. -/
theorem rescaleChunkEntryOfStatisticsRead {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hReads : RescaleStatisticsAreF32 X) {writer : EvId} {stage : Fin 2}
    (hStore : OutputRescaleStore X writer stage) :
    ∃ (chunk : Fin 8) (alpha : ℝ) (word : Value) (reader : EvId)
      (access : Acc) (bytes : List (Option Byte)),
      RescaleChunkEntry l X writer stage chunk alpha ∧ RescaleFactorWord word alpha ∧
      StatisticsRead X reader stage .alpha access bytes ∧ rebuild 3 bytes = .ok word ∧
      TraceBefore X reader writer ∧
      (correctionBefore X reader).barrier (statsBarrierId l reader.1 stage) =
        (correctionBefore X writer).barrier (statsBarrierId l writer.1 stage) := by
  obtain ⟨⟨g,pos⟩,chunk,address,words,hOwner,hPos,hRead⟩ :=
    previousRescaleChunkLoadDecoded hp hX hStore
  obtain ⟨load,hLane,hLoadPos,_,hVisit⟩ :=
    OutputRescaleStore.previousChunkLoadWithStatistics hp hX hStore
  have hSame : load = (g,pos) := Prod.ext (hLane.trans hOwner.symm) (by dsimp at hPos; omega)
  rw [hSame] at hVisit
  obtain ⟨t,ending,word,alpha,ht,hAddr,hWord,hReg,hRun,j,hJ,a,bytes,hAlpha,hVal,hOrdinal⟩ :=
    rescaleLoadFactorOfStatisticsRead hp hX hReads hRead
  obtain ⟨_,_,_,_,hGet⟩ := hStore.decoded
  have hEntry : RescaleChunkEntry l X writer stage chunk alpha :=
    RescaleChunkEntry.ofLoadState hPos.symm ht (by rw [← hOwner]; exact hAddr) hWord hReg
      (by rw [← hOwner]; exact hRun)
  refine ⟨chunk,alpha,word,(g,j),a,bytes,hEntry,hWord,hAlpha,hVal,?_,hOrdinal.trans hVisit⟩
  exact ⟨hOwner,by dsimp at hPos ⊢; omega,len_of_get hGet⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
