-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRescaleVisit
public import Kernels.TmlFa4Fwd.Proof.Safety.RescaleFiniteLoads
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTmemAddress
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Correction
open Protocol.Statistics

noncomputable section

/-- Each observed rescale load supplies sixteen finite accumulator words. -/
theorem rescaleLoadValuesAt {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (hOperands : Safety.CompletedMmaOperandsAreBf16 X)
    (hStats : RescaleStoreValuesAreF32 X)
    {g index : Nat} (stage : Fin 2) (chunk : Fin 8) :
    ∃ old : Nat → ℝ, ∀ vals,
      X.get (g,index) = some ⟨rescaleLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (16*chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn fun i : Fin 16 => fl (old i.val) := by
  classical
  let addr := outputAddress l g stage (16*chunk.val)
  let load := (g,index)
  by_cases hPresent : ∃ words,
    X.get load = some ⟨rescaleLoadPc stage chunk,.tc (.ld addr words .s32x32b)⟩
  · obtain ⟨words,hWords⟩ := hPresent
    have hLength : words.length = 16 := (rescaleLoadActualAddress hp hX stage chunk hWords).2.2
    have hValue (i : Nat) (hi : i < 16) : ∃ x, words[i]? = some (.float .f32 x) := by
      let cell := tcDataCell l g .s32x32b addr i
      have hL : X.TLd load addr words .s32x32b := ⟨_,hWords⟩
      have hI : i < words.length := hLength.symm ▸ hi
      exact Safety.rescaleLoadWordOfOperandsAndStores hp hX hCuQ hOperands hStats
        (RescaleLoadCell.ofDecoded chunk hWords hI rfl) hL ⟨_,_,_,hL,hI,rfl⟩
    let old (i : Nat) : ℝ := if hi : i < 16 then Classical.choose (hValue i hi) else 0
    refine ⟨old,?_⟩
    intro vals hRead
    have hSame := (TcKind.ld.inj (Kind.tc.inj (Event.mk.inj
      (Option.some.inj (hRead.symm.trans hWords))).2)).2.1
    rw [hSame]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 16
    · simpa only [List.getElem?_ofFn,hi,↓reduceDIte,fl,old] using
        Classical.choose_spec (hValue i hi)
    · rw [List.getElem?_eq_none (by omega),List.getElem?_ofFn,dite_eq_right hi]
  · exact ⟨fun _ => 0,fun vals he => (hPresent ⟨vals,he⟩).elim⟩

/-- An actual finished rescale visit receives its coefficient from the recorded
statistics read and all of its load values from the earlier finite tensor writers. -/
theorem rescaleVisitOfFiniteWords {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (hOperands : Safety.CompletedMmaOperandsAreBf16 X)
    (hStats : RescaleStoreValuesAreF32 X)
    {g pos : Nat} (stage : Fin 2) {t : TState} {F : List (Nat × Value)}
    (ht : At t (statsBarrierPc stage true) F)
    (hFrame : RescaleVisitFrame l g stage F)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ alpha old word coefficient u, RescaleVisit l X g pos stage alpha old word coefficient ∧
      RescaleFactorWord coefficient alpha ∧ At u (rescaleSignalPc stage+3) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos+3+rescaleBodyEvents word+2)) none := by
  classical
  obtain ⟨_,hAt,hTail⟩ := observeStatsBarrier hp stage true ht
    (holds_mem ht.2.2.2.2 hFrame.rendezvous) hr
  obtain ⟨bytes,hRead,_⟩ := observeStats hp stage .alpha
    (hAt.mono ⟨holds_mem ht.2.2.2.2 hFrame.statistics,trivial⟩) hTail
  obtain ⟨coefficient,alpha,hRebuilt,hFactor⟩ := rescaleStatisticsFiniteOfStores hp hX hCuQ hStats
    (g,pos+1) stage _ _ hRead
  have hBytes : bytes = coefficient.toBytes.map some := by
    obtain ⟨j,biased,data,hPub,_,hData⟩ := rescaleStatisticsReadSource hp hX hCuQ
      (show StatisticsRead X (g,pos+1) stage .alpha _ bytes from hRead)
    obtain ⟨value,v,hExact,hValue⟩ := hStats _ _ _ _ hPub
    have hId : coefficient = value := by
      have hWidth : 0 < value.bytes := by rw [hValue.width]; decide
      have hRebuildActual : rebuild 3 bytes = .ok value := by
        rw [hData,hExact]
        exact PTX.Proof.rebuild_scalar hWidth hValue.head
      exact Except.ok.inj (hRebuilt.symm.trans hRebuildActual)
    rw [hId]
    exact hData.trans (congrArg (List.map some) hExact)
  have hOld (chunk : Fin 8) := rescaleLoadValuesAt hp hX hCuQ hOperands hStats
    (g := g) (index := pos+3+3*chunk.val) stage chunk
  choose old hOld using hOld
  obtain ⟨word,u,hVisit,hu,hRun⟩ := observeRescaleVisitOfWord hp stage coefficient alpha old
    hFactor ht (holds_mem ht.2.2.2.2 hFrame.rendezvous)
    (holds_mem ht.2.2.2.2 hFrame.statistics) hFrame.accumulator hFrame.credit hFrame.reuse
    hFrame.control hFrame.data hFrame.release
    (fun bs h => (PTX.Event.mk.inj (Option.some.inj (h.symm.trans hRead))).2 |> fun hK =>
      (Kind.rd.inj hK).2.trans hBytes)
    (fun _ _ _ chunk values he => hOld chunk values he) hr
  exact ⟨alpha,old,word,coefficient,u,hVisit,hFactor,hu,hRun⟩

/-- The coefficient read by the visit follows its own observed statistics wait. -/
theorem rescaleVisitStatisticsRead {l : Launch} {X : Execution} {g pos : Nat}
    {stage : Fin 2} {alpha : ℝ} {old : Fin 8 → Nat → ℝ}
    {vote : BitVec 32} {coefficient : Value}
    (hVisit : RescaleVisit l X g pos stage alpha old vote coefficient) :
    StatisticsRead X (g,pos+1) stage .alpha
      {loc := statsLoc l g stage .alpha,size := 4} (coefficient.toBytes.map some) ∧
    (correctionBefore X (g,pos+1)).barrier (statsBarrierId l g stage) =
      (correctionBefore X (g,pos)).barrier (statsBarrierId l g stage)+1 := by
  refine ⟨hVisit.alphaRead,?_⟩
  rw [correctionBarrierOrdinal,correctionBarrierOrdinal]
  exact countP_take_succ hVisit.rendezvous (by simp [Execution.isBarId])


end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
