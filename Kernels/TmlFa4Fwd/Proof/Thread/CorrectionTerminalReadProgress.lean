-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TerminalPublishedWords
public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseTerminalStores
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import all Kernels.TmlFa4Fwd.Proof.CorrectionStats
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Step.ReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy Prologue
open Thread.Correction

/-- Two known writes immediately before the actual final arrival identify all
payload fields expected by the terminal correction reads. -/
theorem terminalPublishedWordsOfActualWrites {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} (stage : Fin 2) {sum maximum : Value}
    (hFinal : Thread.Scores.Publishes X (terminalStatsProducer l g stage,pos+2) .final)
    (hS : X.Writes (terminalStatsProducer l g stage,pos)
      (Softmax.statsAcc l (terminalStatsProducer l g stage) (terminalStatsWarp l g stage) 2)
      sum.toBytes)
    (hM : X.Writes (terminalStatsProducer l g stage,pos+1)
      (Softmax.statsAcc l (terminalStatsProducer l g stage) (terminalStatsWarp l g stage) 3)
      maximum.toBytes) :
    TerminalPublishedWords l X g stage (pos+2) sum maximum := by
  obtain ⟨first,hFirst,_,_,_,_,hs,hm⟩ := terminalStoresOfPublicationAtSites hX hFinal
  have hEqual : first = pos := by omega
  subst first
  obtain ⟨_,ha⟩ := hS
  obtain ⟨_,hb⟩ := hM
  have hSum : _ := Option.some.inj (hs.symm.trans ha)
  have hMax : _ := Option.some.inj (hm.symm.trans hb)
  obtain ⟨_,⟨e,he,hKind,_,_⟩,_⟩ := Thread.Scores.publishes hp hX hFinal
  obtain ⟨f,hf,hNotice⟩ := hFinal
  have hPc := Thread.Scores.publicationSiteOfNotice hNotice
  rw [Option.some.inj (hf.symm.trans he)] at hPc
  have hWarp := terminalStatsProducerWarp hp g stage
  rw [hWarp] at hKind
  refine ⟨?_,?_,?_,by omega⟩
  · rw [Nat.add_sub_cancel]
    exact hs.trans (congrArg some (by cases hSum; rfl))
  · rw [Nat.add_sub_cancel]
    exact hm.trans (congrArg some (by cases hMax; rfl))
  · exact he.trans (congrArg some (by cases e; simp_all [Thread.Scores.publicationSite]))

private theorem statsLoadOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (stage : Fin 2) (kind : StatsKind) {g : Nat} {t : TState}
    (ht : At t (statsPc stage kind) [])
    (hReg : t.regs 1627 = some (b32 (l.sharedBase+4*rowOf l g))) :
    out kernel Assumptions.all l g t = .ev (.read
      { loc := statsLoc l g stage kind, size := 4 } (afterLoad t [statsReg stage kind])) := by
  rw [statsModel stage kind ht.1]
  rw [out_event ht.2.2.2.1 (ht.1.symm ▸ statsCode stage kind) rfl rfl]
  change Out.ev (loadTmpl [] l g t .shared false 32 [statsReg stage kind] 1627
    (statsOff stage kind)) = _
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hOff : statsOff stage kind ≤ 1904 ∧ statsOff stage kind % 4 = 0 := by
    cases kind <;> fin_cases stage <;> decide
  have hAddr : l.sharedBase+4*rowOf l g+statsOff stage kind < 2^32 := by
    have := hp.shared.2.1
    omega
  have hAlign : (l.sharedBase+4*rowOf l g+statsOff stage kind)%4 = 0 := by
    have := hp.shared.1
    omega
  rw [loadTmpl,effAddr_b32_off hReg hAddr]
  simp only [bind,Except.bind,List.length_singleton,ht.2.1,Nat.reduceDiv]
  rw [elemAcc_ok (by decide : 0 < 4) (by simpa only [statsLoc] using hAlign)]
  simp [Loc.at,statsLoc]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hSync : SyncGuarded l kernel X)
include hp hMax hSync

private theorem statsReadRecorded {g : Nat} (hg : g < l.threads) (stage : Fin 2) (kind : StatsKind)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (statsPc stage kind) F)
    (hBase : (1627,b32 (l.sharedBase+4*rowOf l g)) ∈ F) :
    let access : Acc := {loc := statsLoc l g stage kind,size := 4}
    ∃ bytes, X.get (g,c.pos) = some ⟨c.ready.pc,.rd access bytes⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1))
        (some (afterLoad c.ready [statsReg stage kind] bytes)) ∧
      Run kernel Assumptions.all l g (afterLoad c.ready [statsReg stage kind] bytes)
        ((X.tr g).drop (c.pos+1)) c.ending := by
  have hOut := statsLoadOut hp stage kind (c.checkpoint.mono trivial)
    (holds_mem c.checkpoint.2.2.2.2 hBase)
  exact Step.readSourceOfMaximal hMax hSync hg (Next.mk c.localSteps hOut) c.recorded
    c.remaining c.positive c.bounded c.released (fun _ _ _ =>
      Assumptions.wf_snoc_nonGlobal hMax.1 (by simp [statsLoc]))

/-- After the named wait releases, the terminal sum read is present in the actual
trace, before proving what its returned bytes encode. -/
theorem terminalStatsSumRecorded {g : Nat} (hg : g < l.threads) (stage : Fin 2)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (statsPc stage .sum) F)
    (hBase : (1627,b32 (l.sharedBase+4*rowOf l g)) ∈ F) :
    c.pos < (X.tr g).length := by
  obtain ⟨_,he,_,_⟩ := statsReadRecorded hp hMax hSync hg stage .sum c hBase
  exact len_of_get he

private theorem terminalStatReadOfMaximal {g wait publication : Nat} (hg : g < l.threads)
    {stage : Fin 2} (hWait : Thread.CorrectionWaits X (g,wait) .terminal stage)
    {sumValue maxValue : Value}
    (hWords : TerminalPublishedWords l X g stage publication sumValue maxValue)
    (hSizeSum : sumValue.bytes = 4) (hSizeMax : maxValue.bytes = 4)
    (hGeneration : TerminalGeneration l X g stage (publication-2) wait) (word : Fin 2)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (statsPc stage (finalStatsKind word)) F)
    (hPos : c.pos = wait+1+word.val) (hBase : (1627,b32 (l.sharedBase+4*rowOf l g)) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ statsReg stage (finalStatsKind word))
    (hScalar : let value := if word = 0 then sumValue else maxValue
      rebuild 3 (value.toBytes.map some) = .ok value) :
    let kind := finalStatsKind word
    let value := if word = 0 then sumValue else maxValue
    ∃ nextC : OpeningTripCursor l X g (statsPc stage kind+1)
        ((statsReg stage kind,value)::F),
      nextC.pos = c.pos+1 ∧
      X.get (g,c.pos) = some ⟨statsPc stage kind,
        .rd {loc := statsLoc l g stage kind,size := 4} (value.toBytes.map some)⟩ := by
  let kind := finalStatsKind word
  let value := if word = 0 then sumValue else maxValue
  let T := next (setReg c.ready (statsReg stage kind) value)
  obtain ⟨bytes,he,hPrefix,hTail⟩ := statsReadRecorded hp hMax hSync hg stage kind c hBase
  have hr : X.Reads (g,c.pos) {loc := statsLoc l g stage kind,size := 4} bytes := ⟨_,he⟩
  rw [hPos] at hr
  have hb := hWords.read hp hMax.1 hWait hSizeSum hSizeMax hGeneration word hr
  subst bytes
  have ht : afterLoad c.ready [statsReg stage kind] (value.toBytes.map some) = T := by
    rw [afterLoad_ok c.checkpoint.2.1 c.checkpoint.2.2.1 hScalar]
    simp [T,value,next,setReg,c.checkpoint.2.1,c.checkpoint.2.2.1]
  rw [ht] at hPrefix hTail
  refine ⟨⟨c.pos+1,T,T,c.ending,Nat.succ_pos _,len_of_get he,?_,
    c.checkpoint.set hFresh,hPrefix,hTail,.refl⟩,rfl,?_⟩
  · exact releasedIfLast he (by simp [Kind.resume])
  · simpa only [c.checkpoint.1] using he

/-- A released terminal correction lane reads both of its paired producer's
published statistics words in the same named-barrier generation. -/
theorem terminalStatsWordsOfMaximal {g wait publication : Nat} (hg : g < l.threads) {stage : Fin 2}
    (hWait : Thread.CorrectionWaits X (g,wait) .terminal stage) {sumValue maxValue : Value}
    (hWords : TerminalPublishedWords l X g stage publication sumValue maxValue)
    (hSizeSum : sumValue.bytes = 4) (hSizeMax : maxValue.bytes = 4)
    (hGeneration : TerminalGeneration l X g stage (publication-2) wait) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (statsPc stage .sum) F) (hPos : c.pos = wait+1)
    (hBase : (1627,b32 (l.sharedBase+4*rowOf l g)) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ statsReg stage .sum ∧ pair.1 ≠ statsReg stage .maximum)
    (hSumScalar : rebuild 3 (sumValue.toBytes.map some) = .ok sumValue)
    (hMaxScalar : rebuild 3 (maxValue.toBytes.map some) = .ok maxValue) :
    ∃ nextC : OpeningTripCursor l X g (statsPc stage .maximum+1)
        ((statsReg stage .maximum,maxValue)::(statsReg stage .sum,sumValue)::F),
      nextC.pos = wait+3 ∧
      X.get (g,wait+1) = some ⟨statsPc stage .sum,
        .rd {loc := statsLoc l g stage .sum,size := 4} (sumValue.toBytes.map some)⟩ ∧
      X.get (g,wait+2) = some ⟨statsPc stage .maximum,
        .rd {loc := statsLoc l g stage .maximum,size := 4} (maxValue.toBytes.map some)⟩ := by
  have hSites : statsPc stage .sum+1 = statsPc stage .maximum := by fin_cases stage <;> decide
  have hRegs : statsReg stage .sum ≠ statsReg stage .maximum := by fin_cases stage <;> decide
  obtain ⟨a,ha,hs⟩ := terminalStatReadOfMaximal hp hMax hSync hg hWait hWords hSizeSum
    hSizeMax hGeneration 0 c hPos hBase (fun pair hm => (hFresh pair hm).1) hSumScalar
  let a' : OpeningTripCursor l X g (statsPc stage .maximum)
      ((statsReg stage .sum,sumValue)::F) :=
    ⟨a.pos,a.before,a.ready,a.ending,a.positive,a.bounded,a.released,
      hSites ▸ a.checkpoint,a.recorded,a.remaining,a.localSteps⟩
  have ha' : a'.pos = wait+1+(1 : Fin 2).val := by
    change a.pos = wait+1+1
    omega
  obtain ⟨b,hb,hm⟩ := terminalStatReadOfMaximal hp hMax hSync hg hWait hWords hSizeSum
    hSizeMax hGeneration 1 a' ha' (List.mem_cons_of_mem _ hBase)
    (fun pair h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact hRegs
      · exact (hFresh pair h).2) hMaxScalar
  rw [hPos] at hs
  rw [ha'] at hm hb
  exact ⟨b,by omega,hs,hm⟩

end PTX.Kernels.TmlFa4Fwd.Correction
