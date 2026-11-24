-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleStatisticsPublication
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleFactors
public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReadOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleStatisticsScore
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites
import Kernels.TmlFa4Fwd.Proof.SoftmaxExitPublications
public import Kernels.TmlFa4Fwd.Proof.SoftmaxAlpha
import Kernels.TmlFa4Fwd.Proof.CorrectionCreditExtent
import Lemmas.Order.ReadLast
import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Proof PTX.Flow Thread Prologue Epilogue
open Correction (statsLoc terminalStatsProducer terminalStatsWarp terminalStatsCta
  terminalStatsProducerWarp statsBarrierId
  rescaleWaitOrdinalBoundsBeforeTerminal statsWaitHasWork)

private theorem matchedRescalePublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g wait : Nat} {stage : Fin 2}
    (hWait : CorrectionWaits X (g,wait) .rescale stage) (hPass : wait+1 < (X.tr g).length) :
    ∃ publication biased,
      Scores.Publishes X (terminalStatsProducer l g stage,publication)
        (Scores.rescalePublication biased) ∧
      (Scores.before X (terminalStatsProducer l g stage,publication)).notices =
        (correctionBefore X (g,wait)).barrier (statsBarrierId l g stage) := by
  let producer := terminalStatsProducer l g stage
  let warp := terminalStatsWarp l g stage
  have hWarp := terminalStatsProducerWarp hp g stage
  have hCta := terminalStatsCta hp g stage
  have hWork := statsWaitHasWork hp hX hWait
  have hUsedK := usedKProtected hp hX
  obtain ⟨batch,hBatch,hLo,hHi,hPos,hUpper⟩ :=
    rescaleWaitOrdinalBoundsBeforeTerminal hp hX hWork hUsedK hWait
  obtain ⟨position,round,hPub,hOrd⟩ := publicationOfResumedRescale hp hX hCuQ hWait hPass
  dsimp only at hLo hHi hPos hUpper
  have hSoft : warpIndex l producer < 8 := hWarp.symm ▸ warp.isLt
  cases round with
  | biased => exact ⟨position,true,hPub,hOrd⟩
  | plain => exact ⟨position,false,hPub,hOrd⟩
  | first =>
    have hSources := statsBarrierSources hp hX warp
    have hOrdinal := Scores.firstOrdinal hp hX hPub ((congrArg (3 + ·) hWarp).symm ▸ hSources)
    rw [Scores.notificationOrdinal hp hX hSoft,hOrdinal] at hOrd
    omega
  | final =>
    obtain ⟨b,hb,hbLo,hbHi,hExtent⟩ :=
      Softmax.finalPublicationOrdinalLower hp hX hSoft (hCta.symm ▸ hWork) hCuQ hUsedK hPub
    have ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
    rw [hCta] at hbLo hbHi
    have hSame := (hUnique b ⟨hb,hbLo,hbHi⟩).trans (hUnique batch ⟨hBatch,hLo,hHi⟩).symm
    subst b
    rw [hCta,hOrd] at hExtent
    omega

private theorem rescaleStoreFootprint {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g writer : Nat} {stage : Fin 2} (biased : Bool) {a : Acc} {data : List Byte}
    (hStore : Scores.StatisticsStore X (terminalStatsProducer l g stage,writer)
      (Softmax.rescaleStore biased) a data) :
    a = {loc := statsLoc l g stage .alpha, size := 4} := by
  obtain ⟨warp,hWarp,rfl⟩ := Scores.statisticsStoreFootprint hp hX _ hStore
  have hEq := Fin.ext (hWarp.trans (terminalStatsProducerWarp hp g stage))
  subst warp
  have hLoc := Correction.terminalStatsLocation hp g stage 0
  cases biased <;> exact congrArg (fun loc => ({loc := loc, size := 4} : Acc)) hLoc

/-- Each real rescale reader sees the exact preceding producer word of its named barrier
generation. The paired writer is determined on any consistent protected prefix. -/
theorem rescaleStatisticsReadSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g j : Nat} {stage : Fin 2}
    {a : Acc} {bytes : List (Option Byte)}
    (hRead : Thread.Correction.StatisticsRead X (g,j) stage .alpha a bytes) :
    ∃ writer biased data,
      Scores.StatisticsStore X (terminalStatsProducer l g stage,writer)
        (Softmax.rescaleStore biased) a data ∧
      (Scores.before X (terminalStatsProducer l g stage,writer)).notices + 1 =
        (correctionBefore X (g,j)).barrier (statsBarrierId l g stage) ∧
      bytes = data.map some := by
  obtain ⟨⟨owner,wait⟩,hWait,hResume,hReaderOrd⟩ := Thread.statisticsBeforeRead hp hX hRead
  have hLane : owner = g := hResume.1.1
  subst owner
  have hPass : wait+1 < (X.tr g).length := by
    have ⟨hj,hLen⟩ := hResume.1.2
    change j < (X.tr g).length at hLen
    omega
  obtain ⟨publication,biased,hPub,hPubOrd⟩ := matchedRescalePublication hp hX hCuQ hWait hPass
  obtain ⟨writer,dst,data,hNext,hStore,hLen⟩ := Scores.rescaleStoreBeforePublication hX biased hPub
  let producer := terminalStatsProducer l g stage
  let read := (g,j)
  have hStoreOrd := (Scores.storeNoticeOfAdjacentPublication hStore hNext).trans hPubOrd
  have hCausal := statisticsStoreBeforeRead hp hX hCuQ hStore hRead rfl (by
    rw [hStoreOrd]
    exact hReaderOrd.symm ▸ Nat.lt_succ_self _)
  have hFoot := (rescaleStoreFootprint hp hX biased hStore).trans (hRead.footprint hp hX).symm
  subst dst
  have hWritten : X.Writes (producer,writer) a data := ⟨_,hStore⟩
  refine ⟨writer,biased,data,hStore,(congrArg (· + 1) hStoreOrd).trans hReaderOrd.symm,?_⟩
  have hObserved : X.MemReads (.thread read) a bytes := .inl ⟨_,hRead⟩
  have hWritten' : X.MemWrites (.thread (producer,writer)) a data := .inl hWritten
  apply read_of_last_write hX hObserved hWritten' rfl rfl hLen (fun _ _ => .inl hCausal)
  intro k hk ref access data' hWrite hCover
  have hReadFoot := hRead.footprint hp hX
  have hK : k < 4 := by simpa [hReadFoot] using hk
  obtain ⟨⟨peer,index⟩,rfl,ho⟩ := Thread.terminalStatisticsWriterOrdinary hp hX hK hWrite
    (by simpa only [hReadFoot] using hCover)
  obtain ⟨hPair,site,hOther,_⟩ :=
    ordinaryStatisticsWriter hp hX ho hRead hCover (Acc.covers_at hk)
  change peer = producer at hPair
  subst peer
  by_cases hLater : (correctionBefore X read).barrier (statsBarrierId l g stage) ≤
      (Scores.before X (producer,index)).notices
  · exact .inr (.inr (.inl (statisticsReadBeforeStore hp hX hCuQ hOther hRead rfl hLater)))
  have hOrd : (Scores.before X (producer,index)).notices ≤
      (Scores.before X (producer,publication)).notices := by
    rw [hPubOrd]
    change (correctionBefore X read).barrier (statsBarrierId l g stage) =
      (correctionBefore X (g,wait)).barrier (statsBarrierId l g stage) + 1 at hReaderOrd
    omega
  have hBefore := Scores.storeBeforePublicationOfNotice hOther hPub hOrd
  rcases Nat.eq_or_lt_of_le (show index ≤ writer by omega) with rfl | hEarlier
  · exact .inl rfl
  · exact .inr (.inl (.inl (Scores.overlappingStoreBefore ho hWritten hEarlier hCover
      (Acc.covers_at hk))))

/-- The softmax coefficient has the same finite value as a real word or an immediate. -/
theorem rescaleFactorOfSoftmaxWord (scale : ℝ) (old candidate : Option ℝ) :
    Thread.Correction.RescaleFactorWord (Softmax.alphaWord scale old candidate)
      (Softmax.correctionAlpha scale old candidate) := by
  by_cases hKeep : Softmax.keepReference scale old candidate
  · have hOne : f32Value 0x3F800000 = some 1 := by
      norm_num [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode,
        Layout.fieldVal, Layout.magnitude, Layout.bias,
        Layout.width, FVal.num]
    simp only [Softmax.alphaWord, Softmax.correctionAlpha, hKeep, ite_true]
    exact Thread.Correction.RescaleFactorWord.ofBits (by decide)
      (by simpa [b32] using valFloat_b32 (by decide : 0x3F800000 < 2 ^ 64) hOne)
  · simp only [Softmax.alphaWord, hKeep]
    exact Thread.Correction.RescaleFactorWord.ofFloat _

/-- Each actual producer publishes a finite FP32 rescale coefficient. -/
def RescaleStoreValuesAreF32 (X : Execution) : Prop :=
  ∀ (i : EvId) (biased : Bool) (a : Acc) (data : List Byte),
    Scores.StatisticsStore X i (Softmax.rescaleStore biased) a data →
    ∃ word alpha, data = word.toBytes ∧ Thread.Correction.RescaleFactorWord word alpha

/-- It suffices to establish that the actual softmax rescale stores hold finite FP32.
Their bytes are observed intact by correction. -/
theorem rescaleStatisticsFiniteOfStores {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
    (hFinite : RescaleStoreValuesAreF32 X) :
    Thread.Correction.RescaleStatisticsAreF32 X := by
  intro ⟨g,j⟩ stage a bytes hRead
  obtain ⟨writer,biased,data,hStore,_,rfl⟩ := rescaleStatisticsReadSource hp hX hCuQ hRead
  obtain ⟨word,alpha,rfl,hWord⟩ := hFinite _ _ _ _ hStore
  have hb : 0 < word.bytes := by rw [hWord.width]; decide
  exact ⟨word,alpha,PTX.Proof.rebuild_scalar hb hWord.head,hWord⟩

/-- The value used to rescale a chunk comes from the actual softmax writer
of the current score visit. The recorded word and factor are preserved. -/
theorem rescaleChunkEntryOfPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) (hFinite : RescaleStoreValuesAreF32 X)
    {writer : EvId} {stage : Fin 2} (hStore : OutputRescaleStore X writer stage) :
    ∃ seen : Protocol.Scores.RescaleStatisticsScore l X writer stage,
      ∃ (chunk : Fin 8) (alpha : ℝ) (word : Value) (pos : Nat) (biased : Bool)
        (acc : Acc) (data : List Byte),
        let producer := terminalStatsProducer l writer.1 stage
        Thread.Correction.RescaleChunkEntry l X writer stage chunk alpha ∧
          Thread.Correction.RescaleFactorWord word alpha ∧
          Scores.StatisticsStore X (producer,pos) (Softmax.rescaleStore biased) acc data ∧
          data = word.toBytes ∧
          (Scores.before X (producer,pos)).notices =
            Thread.Scores.scoreCommitOrdinal l X (writer.1/l.block) stage seen.commit := by
  obtain ⟨chunk,alpha,word,⟨g,j⟩,acc,bytes,hEntry,hWord,hRead,hValue,hBefore,hSame⟩ :=
    Thread.Correction.rescaleChunkEntryOfStatisticsRead hp hX
      (rescaleStatisticsFiniteOfStores hp hX hCuQ hFinite) hStore
  obtain ⟨pos,biased,data,hProducer,hOrd,hBytes⟩ :=
    rescaleStatisticsReadSource hp hX hCuQ hRead
  obtain ⟨verbatim,newAlpha,hData,hDecoded⟩ := hFinite _ _ _ _ hProducer
  have hSize : 0 < verbatim.bytes := by rw [hDecoded.width]; decide
  have hRebuilt : rebuild 3 bytes = .ok verbatim := by
    rw [hBytes,hData]
    exact PTX.Proof.rebuild_scalar hSize hDecoded.head
  have hSameWord := Except.ok.inj (hValue.symm.trans hRebuilt)
  obtain ⟨seen,_,hCursor⟩ := Protocol.Scores.rescaleStatisticsObservedScoreWithOrdinal
    hp hX hCuQ hStore
  have hLane : g = writer.1 := hBefore.1
  have hProducer' : Scores.StatisticsStore X (terminalStatsProducer l writer.1 stage,pos)
      (Softmax.rescaleStore biased) acc data := hLane ▸ hProducer
  refine ⟨seen,chunk,alpha,word,pos,biased,acc,data,hEntry,hWord,hProducer',
    hSameWord.symm ▸ hData,?_⟩
  have hRank := hOrd.trans hSame
  rw [hLane,← hCursor] at hRank
  exact Nat.add_right_cancel hRank

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
