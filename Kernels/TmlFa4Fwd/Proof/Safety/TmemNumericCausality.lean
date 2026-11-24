-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemLoadProvenance
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleFactors
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Thread.TmemOutputRescaleGeometry
import Lemmas.Order.WaitOrderObject

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread

/-- The FP32 correctness of a rescale store need only know the already evaluated results
and rescale writers before it in the actual Tensor Memory order. -/
def RescaleFiniteStep (l : Launch) (X : Execution) : Prop :=
  ∀ i cell stage value, TensorStoreFootprint l i cell (.rescale stage) →
    StoreValue l X i cell value →
    (∀ source, Relation.TransGen (TcStep l X) source i →
      X.async.mmaDone source = true → ∀ c, X.MmaCell source c →
      ∃ x, Result l Assumptions.all X source c (.float .f32 x)) →
    (∀ source, Relation.TransGen (TcStep l X) source i →
      ∀ c s v, TensorStoreFootprint l source c (.rescale s) → StoreValue l X source c v →
      ∃ x, v = .float .f32 x) →
    ∃ x, value = .float .f32 x

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
include hp hX hCuQ

/-- Acyclic Tensor Memory order lets the MMA and rescale proofs use each other's
earlier values without assuming an FP32 invariant for every rescale store. -/
theorem traceFiniteMmaAndRescale (hOperands : CompletedMmaOperandsAreBf16 X)
    (hStep : RescaleFiniteStep l X) :
    (∀ i cell, X.async.mmaDone i = true → X.MmaCell i cell →
      ∃ x, Result l Assumptions.all X i cell (.float .f32 x)) ∧
    (∀ i cell s v, TensorStoreFootprint l i cell (.rescale s) → StoreValue l X i cell v →
      ∃ x, v = .float .f32 x) := by
  classical
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  let nodes : Finset EvId := (Finset.range l.threads).biUnion fun g =>
    (Finset.range (X.tr g).length).image (g, ·)
  have actual {i : EvId} {e : Event} (he : X.get i = some e) : i ∈ nodes := by
    exact Finset.mem_biUnion.mpr ⟨i.1,Finset.mem_range.mpr (Proof.event_thread_lt hX he),
      Finset.mem_image.mpr ⟨i.2,Finset.mem_range.mpr (len_of_get he),Prod.eta i⟩⟩
  have mmaNode {i : EvId} {cell : Cell} (hMma : X.MmaCell i cell) : i ∈ nodes := by
    obtain ⟨_,_,_,_,_,_,⟨_,he⟩,_⟩ := hMma
    exact actual he
  have storeNode {i : EvId} {cell : Cell} {v : Value} (hStore : StoreValue l X i cell v) :
      i ∈ nodes := by
    obtain ⟨_,_,_,_,⟨_,he⟩,_,_⟩ := hStore
    exact actual he
  let P (i : EvId) :=
    (∀ cell, X.async.mmaDone i = true → X.MmaCell i cell →
      ∃ x, Result l Assumptions.all X i cell (.float .f32 x)) ∧
    (∀ cell s v, TensorStoreFootprint l i cell (.rescale s) →
      StoreValue l X i cell v → ∃ x, v = .float .f32 x)
  have step (i : EvId) (_ : i ∈ nodes)
      (ih : ∀ pred ∈ nodes, Relation.TransGen (TcStep l X) pred i → P pred) : P i := by
    refine ⟨?_,?_⟩
    · intro cell hDone hMma
      apply mmaCompletedResultOfEarlierValues hp hX hCuQ hOperands hDone hMma
      · intro pred hBefore _ hPred hCell
        exact (ih pred (mmaNode hCell) hBefore).1 cell hPred hCell
      · intro src hBefore value hRead hSource hStore
        have hNode := storeNode hStore
        obtain ⟨address, words, shape, j, hi, hv, hc⟩ := hStore
        have hStoreCell : StoreCell l X src cell :=
          ⟨address,words,shape,j,hi,(List.getElem?_eq_some_iff.mp hv).1,hc⟩
        obtain ⟨stage,hStage⟩ := storedAccumulatorIsRescale hp hX hCuQ hRead hSource hStoreCell
        exact (ih src hNode hBefore).2 cell stage value hStage ⟨address,words,shape,j,hi,hv,hc⟩
    · intro cell stage value hStage hStore
      apply hStep i cell stage value hStage hStore
      · intro source hEarlier hDone c hCell
        exact (ih source (mmaNode hCell) hEarlier).1 c hDone hCell
      · intro source hEarlier c s v hf hv
        exact (ih source (storeNode hv) hEarlier).2 c s v hf hv
  have all := induction_of_acyclic (tcStep_acyclic hX hGuard) nodes P step
  exact ⟨fun i c hd hc => (all i (mmaNode hc)).1 c hd hc,
    fun i c s v hf hv => (all i (storeNode hv)).2 c s v hf hv⟩

/-- The Tensor Memory source check follows from a local rescale arithmetic step and the
recorded BF16 operands. -/
theorem tensorSourcesOfRescaleStep (hOperands : CompletedMmaOperandsAreBf16 X)
    (hStep : RescaleFiniteStep l X) :
    SourceSafe l Assumptions.all X := by
  obtain ⟨_,hStores⟩ := traceFiniteMmaAndRescale hp hX hCuQ hOperands hStep
  exact tensorSourcesOfNumericValues hp hX hCuQ hOperands
    (fun i _ c s v _ _ hFrame hw => hStores i c s v hFrame hw)

omit hp hX hCuQ in
/-- The remaining rescale provenance is the actual chunk entry and its finite row factor. -/
def RescaleEntriesHaveFiniteAlpha (l : Launch) (X : Execution) : Prop :=
  ∀ writer cell stage value, TensorStoreFootprint l writer cell (.rescale stage) →
    StoreValue l X writer cell value →
    ∃ chunk alpha, Thread.Correction.RescaleChunkEntry l X writer stage chunk alpha

/-- Recorded rescale words are derived from earlier committed values and the row factor
at the actual entry. The chunk proof applies to a prefix ending at its store. -/
theorem rescaleFiniteStepOfEntries (hEntry : RescaleEntriesHaveFiniteAlpha l X) :
    RescaleFiniteStep l X := by
  intro i cell stage value hFoot hw hMma hStore
  obtain ⟨_,_,hChunk⟩ := hEntry i cell stage value hFoot hw
  apply hChunk.finiteStore hp hw
  intro load address vals shape hLoad hTLd j c hc hClass
  apply rescaleLoadWordOfEarlierValues hp hX hCuQ hClass hTLd hc
  · intro source hBefore hDone hCell
    exact hMma source (hBefore.trans hLoad) hDone c hCell
  · intro source hBefore v hf hv
    exact hStore source (hBefore.trans hLoad) c stage v hf hv

/-- The source check needs the actual MMA BF16 operands and the observed rescale row factor. -/
theorem tensorSourcesOfOperandsAndRescaleEntries (hOperands : CompletedMmaOperandsAreBf16 X)
    (hEntry : RescaleEntriesHaveFiniteAlpha l X) : SourceSafe l Assumptions.all X :=
  tensorSourcesOfRescaleStep hp hX hCuQ hOperands (rescaleFiniteStepOfEntries hp hX hCuQ hEntry)

omit hp hX hCuQ in
private theorem rescaleEntriesOfFactors {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFactors : Thread.Correction.FiniteRescaleFactors l X) :
    RescaleEntriesHaveFiniteAlpha l X := by
  intro writer cell stage value hFoot hw
  obtain ⟨address,words,shape,j,hStore,hV,hCell⟩ := hw
  have hCellStore : StoreCell l X writer cell :=
    ⟨address,words,shape,j,hStore,(List.getElem?_eq_some_iff.mp hV).1,hCell⟩
  exact Thread.Correction.rescaleChunkEntryOfFactor hp hX hFactors
    (outputRescaleStoreOfCell hp hX hCellStore hFoot)

/-- Actual rescale chunks need only their recorded finite statistics factor in addition
to the BF16 operands for completed MMA. -/
theorem tensorSourcesOfOperandsAndRescaleFactors (hOperands : CompletedMmaOperandsAreBf16 X)
    (hFactors : Thread.Correction.FiniteRescaleFactors l X) : SourceSafe l Assumptions.all X :=
  tensorSourcesOfOperandsAndRescaleEntries hp hX hCuQ hOperands
    (rescaleEntriesOfFactors hp hX hFactors)

/-- Finite decoded statistics and BF16 operands suffice for stable Tensor Memory sources. -/
theorem tensorSourcesOfOperandsAndRescaleStatistics (hOperands : CompletedMmaOperandsAreBf16 X)
    (hReads : Thread.Correction.RescaleStatisticsAreF32 X) : SourceSafe l Assumptions.all X :=
  tensorSourcesOfOperandsAndRescaleFactors hp hX hCuQ hOperands
    (Thread.Correction.finiteRescaleFactorsOfReads hp hX hReads)

/-- Every completed MMA has a result at each written cell when its inputs and the
actual rescale statistics are finite in the required formats. -/
theorem mmaCompletedValuesOfOperandsAndRescaleStatistics (hOperands : CompletedMmaOperandsAreBf16 X)
    (hReads : Thread.Correction.RescaleStatisticsAreF32 X) :
    ∀ i, CompletedValues l Assumptions.all X i := by
  have hFactors := Thread.Correction.finiteRescaleFactorsOfReads hp hX hReads
  have hStep := rescaleFiniteStepOfEntries hp hX hCuQ (rescaleEntriesOfFactors hp hX hFactors)
  have hMma := (traceFiniteMmaAndRescale hp hX hCuQ hOperands hStep).1
  intro i hDone cell hCell
  obtain ⟨x,hValue⟩ := hMma i cell hDone hCell
  exact ⟨.float .f32 x,hValue⟩

end PTX.Kernels.TmlFa4Fwd.Safety
