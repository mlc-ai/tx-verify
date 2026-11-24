-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleLoadPriorPv
public import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleStatisticsSources
import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleChunkOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.TcMma Thread Thread.Correction Thread.Mma Thread.Scores
open Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

/-- The actual rescale store multiplies the last result of the immediately
preceding V visit by the coefficient that its correction lane received. -/
theorem rescaledCarryOfPreviousPv {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {writer : EvId}
    {stage : Fin 2} {row col : Fin 128} {g prior use d : Nat} {op : OperandSpec}
    {accum : Bool} {mask : List Nat} {previous : ℝ} {coefficient : ℝ}
    (hStore : OutputRescaleStore X writer stage)
    (hPv : PvInstruction X (g,prior) (firstPvBlock true stage) 7 d op accum mask)
    (hUse : LatestValueReadyUse l X g prior use)
    (seen : RescaleStatisticsScore l X writer stage)
    (hGeneration : scoreCommitOrdinal l X (writer.1/l.block) stage seen.commit = use/2+1)
    (hStats : Statistics.RescaleStoreValuesAreF32 X)
    (hFactor : ∀ (pos : Nat) (biased : Bool) (a : Acc) (data : List Byte) (word : Value) (α : ℝ),
      let producer := TmlFa4Fwd.Correction.terminalStatsProducer l writer.1 stage
      Thread.Scores.StatisticsStore X (producer,pos) (Softmax.rescaleStore biased) a data →
      (Thread.Scores.before X (producer,pos)).notices = use/2+1 →
      data = word.toBytes → RescaleFactorWord word α → α = coefficient)
    (hWords : ∀ (load : EvId) (a : Nat) (vals : List Value) (sh : TcShape),
      Relation.TransGen (TcStep l X) load writer → X.TLd load a vals sh →
      ∀ (j : Nat) (c : Cell), LoadCell l X load j c → RescaleLoadCell l X load c stage →
      ∃ x, vals[j]? = some (.float .f32 x)) :
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    (∃ value, StoreValue l X writer cell value) →
    (X.async.mmaDone (g,prior) = true →
      Result l Assumptions.all X (g,prior) cell (.float .f32 previous)) →
    StoreValue l X writer cell (.float .f32 (previous*coefficient)) := by
  dsimp only
  rintro ⟨value,hStored⟩ hPrevious
  have hCell : StoreCell l X writer ⟨g/l.block,row.val,outputColumn stage+col.val⟩ := by
    obtain ⟨a,vals,shape,i,he,hi,hAt⟩ := hStored
    exact ⟨a,vals,shape,i,he,(List.getElem?_eq_some_iff.mp hi).1,hAt⟩
  obtain ⟨_,hFoot⟩ := tensorStoreFootprint hp hX hCell
  have hWriter : g/l.block = writer.1/l.block := hFoot.cta
  obtain ⟨wordSeen,chunk,alpha,word,pos,biased,access,data,entry,hWord,hPub,hBytes,hNotice⟩ :=
    Statistics.rescaleChunkEntryOfPublication hp hX hCuQ hStats hStore
  obtain ⟨source,hsLane,hsIndex,hsLoad,hsCursor⟩ :=
    Thread.Correction.OutputRescaleStore.previousChunkLoadWithStatistics hp hX hStore
  have hWordRank : scoreCommitOrdinal l X (writer.1/l.block) stage wordSeen.commit =
      use/2+1 := by
    have hOne := wordSeen.cursor
    have hTwo := seen.cursor
    omega
  obtain ⟨load,address,words,j,x,hBefore,hIndex,_,hTLd,hCell,hLoad,hAt,hValue⟩ :=
    entry.storeProduct hp hStored hWords
  have hLoadEq : load = source := Prod.ext (hBefore.1.trans hsLane.symm) (by omega)
  rw [← hLoadEq] at hsCursor
  have hOwner := hWriter.trans (congrArg (· / l.block) hBefore.1.symm)
  obtain ⟨loadSeen,_,hLoadOrd⟩ := rescaleLoadStatisticsObservedScoreWithOrdinal hp hX hCuQ
    hLoad.loadEvent
  have hRank : scoreCommitOrdinal l X (load.1/l.block) stage loadSeen.commit = use/2+1 := by
    have hStoreOrd := seen.cursor
    have hCta : load.1/l.block = writer.1/l.block := congrArg (· / l.block) hBefore.1
    rw [hCta] at hLoadOrd ⊢
    omega
  obtain ⟨hSource,hDone⟩ :=
    loadSeen.loadReadsPreviousPv hp hX hCuQ hOwner hLoad hPv hUse hRank
  have hFrom := hX.tcRead.1.f32 hTLd hCell hSource (.inl (hPrevious (hDone.done hX.tcCommit)))
  have hEqual := Value.float.inj (Option.some.inj (hAt.symm.trans hFrom))
  have hRef : alpha = coefficient := by
    apply hFactor pos biased access data word alpha hPub ?_ hBytes hWord
    exact hNotice.trans hWordRank
  rw [hEqual.2,hRef] at hValue
  exact hValue ▸ hStored

end PTX.Kernels.TmlFa4Fwd.Protocol
