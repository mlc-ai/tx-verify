-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionOutputReadyTrace
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstOutputIssuer
public import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded
import Lemmas.Order.ByteCausalityAcyclic
import Lemmas.Order.WaitOrderObject
import Kernels.TmlFa4Fwd.Proof.ProxyFenceAudit
import Kernels.TmlFa4Fwd.Proof.MmaQueryCoverage

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.AsyncCopy PTX.Proof Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The staging lane has already acquired completion of each overlapping MMA operand
byte before it overwrites that byte. This applies in any consistent prefix. -/
theorem observedOperandBeforeFirstStaging {writer mma : EvId} {a : Acc} {bytes : List Byte}
    {d index : Nat} {op : TcMma.OperandSpec} {accum isB : Bool} {mask : List Nat} {loc : Loc}
    (hWrite : Correction.StageZeroStagingWrites X writer a bytes)
    (hMma : X.MmaIssue mma d op accum mask) (hCta : mma.1 / l.block = writer.1 / l.block)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc) (hCover : a.Covers loc)
    (hShared : loc.space = .shared) :
    ∃ wait scope value, AsyncObserved X mma .mmaDone wait true scope ∧
      ScopesMeet l .cluster mma.1 scope wait.1 ∧ po X wait writer ∧
      X.MmaRead mma isB index loc value ∧
      modelCausality l X loc (.async mma (.mmaRead isB index)) (.thread writer) := by
  obtain ⟨wait, hAcquire, hAfter⟩ := hWrite.firstAcquire hp hX
  obtain ⟨commit, spec, scope, hCommit, hSame, hRead⟩ := firstOutputAcquireReads hp hX hAcquire
  have hCta' : mma.1 / l.block = commit.1 / l.block := by
    rw [hSame.2.2, hAfter.1]
    exact hCta
  have hBefore := mmaBeforeSameCtaFirstOutputCommit hp hX hMma hCommit hCta'
  obtain ⟨hObs, hScope, b, hByte⟩ := hRead hMma hBefore.1 hBefore.2.1 hLoc
  have hReadByte : X.MemReads (.async mma (.mmaRead isB index)) {loc,size := 1} [b] :=
    ⟨b,hByte,rfl,rfl⟩
  have hReadCover : ({loc,size := 1} : Acc).Covers loc := ⟨rfl,rfl,le_rfl,Nat.lt_succ_self _⟩
  have hFinished : AsyncFinished l X mma (.mmaRead isB index) wait :=
    .inr ⟨scope,hObs,hScope⟩
  have hReuses : TcReadReuseBefore l X loc mma (.mmaRead isB index) wait writer :=
    ⟨hShared,.inr ⟨hAfter.1,hAfter.2.1,_,_,_,_,hMma⟩,.single (.inl hAfter),
      ⟨a,bytes,hWrite.writes,hCover⟩⟩
  exact ⟨wait,scope,b,hObs,hScope,hAfter,hByte,
    ⟨⟨_,false,hReadByte.intent,hReadCover⟩,wait,hFinished,.inr hReuses⟩⟩

/-- A first-stage staging store cannot precede an overlapping read already covered by
its lane's observed MMA completion. -/
theorem firstStagingCannotPrecedeObservedOperand (hCuQ : Epilogue.DrainCuQProtected p X)
    {writer mma : EvId} {a : Acc} {bytes : List Byte} {d index : Nat} {op : TcMma.OperandSpec}
    {accum isB : Bool} {mask : List Nat} {loc : Loc}
    (hWrite : Correction.StageZeroStagingWrites X writer a bytes)
    (hMma : X.MmaIssue mma d op accum mask) (hCta : mma.1 / l.block = writer.1 / l.block)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc) (hCover : a.Covers loc)
    (hShared : loc.space = .shared) :
    (∃ value, X.MmaRead mma isB index loc value) ∧
      ¬ ByteCausality l X loc (.thread writer) (.async mma (.mmaRead isB index)) := by
  obtain ⟨wait,scope,b,hObs,hScope,hAfter,hByte,_⟩ :=
    observedOperandBeforeFirstStaging hp hX hWrite hMma hCta hLoc hCover hShared
  have hMemoryWrite : X.MemWrites (.thread writer) a bytes := .inl hWrite.writes
  have hMemory := hMemoryWrite.intent
  refine ⟨⟨b, hByte⟩, ?_⟩
  intro hReverse
  have hLoop : ByteCausality l X loc (.thread writer) (.thread writer) :=
    .commitOperand hShared ⟨a, hMemory, hCover⟩ (.inl ⟨d, op, accum, mask, hMma⟩)
      ⟨b, hByte⟩ hReverse ⟨scope, hObs, hScope⟩ hAfter
      ⟨a, .inl ⟨true, hMemory⟩, hCover⟩
  exact ByteCausality.acyclic hX.effectValidity hX.object
    (DepStepAcyclic.of_dependency hX.dependency) (Progress.syncGuarded hp hX hCuQ)
    hX.guardOk loc (.thread writer) (.single hLoop)

omit hp hX in
/-- A mixed-size operand/store pair whose forward direction requires the source-reuse
reading. The previous forward relation was restricted to the explicit proxy-fence path. -/
def LegacyStagingOperandConflict (l : Launch) (X : Execution) : Prop :=
  ∃ (mma writer : EvId) (isB : Bool) (index : Nat) (src dst : Acc) (loc : Loc),
    let read := Ref.async mma (.mmaRead isB index)
    let write := Ref.thread writer
    Conflict X read write src dst ∧ ¬ src.SameFootprint dst ∧ src.Covers loc ∧ dst.Covers loc ∧
      (∀ wait, AsyncFinished l X mma (.mmaRead isB index) wait →
        ¬ ProxyBefore l X wait writer loc) ∧
      ¬ ByteCausality l X loc write read ∧ ByteCausality l X loc read write

/-- An overlapping first-stage word store and observed operand byte are a mixed access
if no completion observer is linked to the store by a covering proxy fence. -/
theorem firstStagingLegacyConflictWithoutOperandFence (hCuQ : Epilogue.DrainCuQProtected p X)
    {writer mma : EvId} {a : Acc} {bytes : List Byte} {d index : Nat} {op : TcMma.OperandSpec}
    {accum isB : Bool} {mask : List Nat} {loc : Loc}
    (hWrite : Correction.StageZeroStagingWrites X writer a bytes) (hWidth : 1 < a.size)
    (hMma : X.MmaIssue mma d op accum mask) (hCta : mma.1 / l.block = writer.1 / l.block)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc) (hCover : a.Covers loc)
    (hShared : loc.space = .shared)
    (hNoFence : ∀ wait, AsyncFinished l X mma (.mmaRead isB index) wait →
      ¬ ProxyBefore l X wait writer loc) : LegacyStagingOperandConflict l X := by
  obtain ⟨⟨value, hByte⟩, hReverse⟩ :=
    firstStagingCannotPrecedeObservedOperand hp hX hCuQ hWrite hMma hCta hLoc hCover hShared
  let load := Ref.async mma (.mmaRead isB index)
  let store := Ref.thread writer
  let src : Acc := {loc, size := 1}
  have hRead : X.MemReads load src [value] := ⟨value, hByte, rfl, rfl⟩
  have hSrc : src.Covers loc := ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  have hDst : X.MemWrites store a bytes := .inl hWrite.writes
  have hNe : load ≠ store := by
    change Ref.async mma (.mmaRead isB index) ≠ Ref.thread writer
    intro h
    cases h
  have hConflict : Conflict X load store src a :=
    ⟨hNe, false, true, hRead.intent, hDst.intent, .inr rfl, loc, hSrc, hCover⟩
  have hDiff : ¬ src.SameFootprint a := by
    intro h
    have hSize : 1 = a.size := h.2
    omega
  obtain ⟨_,_,_,_,_,_,_,hOrder⟩ :=
    observedOperandBeforeFirstStaging hp hX hWrite hMma hCta hLoc hCover hShared
  exact ⟨mma,writer,isB,index,src,a,loc,hConflict,hDiff,hSrc,hCover,hNoFence,hReverse,
    .direct hOrder⟩

/-- A fence already before the MMA issue cannot order the observed operand completion
before an ordinary staging write. -/
theorem priorFenceCannotObserveOperand (hCuQ : Epilogue.DrainCuQProtected p X)
    {fence mma wait : EvId} {isB : Bool} {index : Nat} (hEarlier : baseCausality l X fence mma)
    (hObserved : AsyncFinished l X mma (.mmaRead isB index) wait) :
    ¬ baseCausality l X wait fence := by
  intro hAfter
  have hGuard := Progress.syncGuarded hp hX hCuQ
  obtain ⟨notify, hNotify, hPath, hSource, hNotArrive⟩ :=
    observer_enables hX.effectValidity hGuard (.inl hObserved)
  have hLoop := (reach_notifier hGuard hX.tma.2.2.1 hX.guardOk hSource hNotArrive
    (hAfter.trans hEarlier) hNotify).trans hPath
  exact DepStepAcyclic.of_dependency hX.dependency _ hLoop

omit hp hX in
/-- A first O-stage store has no earlier first-stage store in its CTA. -/
def EarliestFirstStaging (l : Launch) (X : Execution) (writer : EvId) : Prop :=
  ∀ earlier a bytes, Thread.StageStagingWrite X earlier 0 a bytes →
    earlier.1 / l.block = writer.1 / l.block → ¬ baseCausality l X earlier writer

omit hp hX in
/-- Whenever a CTA starts O staging, a causally minimal first-stage store exists. -/
theorem earliestFirstStagingExists {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {bytes : List Byte} (hi : Thread.StageStagingWrite X i 0 a bytes) :
    ∃ writer b data, Correction.StageZeroStagingWrites X writer b data ∧
      writer.1 / l.block = i.1 / l.block ∧ EarliestFirstStaging l X writer ∧
      Thread.StageStagingWrite X writer 0 b data := by
  classical
  let nodes : Finset EvId := (Finset.range l.threads).biUnion fun g =>
    (Finset.range (X.tr g).length).image (g, ·)
  have hMem {j : EvId} {b : Acc} {bs : List Byte} (hj : Thread.StageStagingWrite X j 0 b bs) :
      j ∈ nodes := by
    obtain ⟨box, chunk, hEvent⟩ := hj.decoded
    exact Finset.mem_biUnion.mpr ⟨j.1, Finset.mem_range.mpr (event_thread_lt hX hEvent),
      Finset.mem_image.mpr ⟨j.2, Finset.mem_range.mpr (len_of_get hEvent), Prod.eta j⟩⟩
  have hTrans {a b : EvId} (h : Relation.TransGen (baseCausality l X) a b) :
      baseCausality l X a b := by
    induction h with
    | single h => exact h
    | tail _ h ih => exact ih.trans h
  have hAcyclic (v : EvId) : ¬ Relation.TransGen (baseCausality l X) v v :=
    fun h => baseCausality_irrefl hX.object.cause (hTrans h)
  let P (j : EvId) := ∀ b data, Thread.StageStagingWrite X j 0 b data →
    ∃ writer a bytes, Correction.StageZeroStagingWrites X writer a bytes ∧
      writer.1 / l.block = j.1 / l.block ∧ EarliestFirstStaging l X writer ∧
      Thread.StageStagingWrite X writer 0 a bytes
  have hStep : ∀ j ∈ nodes,
      (∀ prev ∈ nodes, Relation.TransGen (baseCausality l X) prev j → P prev) → P j := by
    intro j _ ih b data hj
    by_cases hMin : EarliestFirstStaging l X j
    · obtain ⟨box, chunk, he⟩ := hj.decoded
      exact ⟨j, b, data, .of_event box chunk he, rfl, hMin, hj⟩
    · unfold EarliestFirstStaging at hMin
      push Not at hMin
      obtain ⟨prev, a, bytes, hWrite, hCta, hOrder⟩ := hMin
      obtain ⟨writer, access, out, hw, hOwner, hFirst, hStage⟩ :=
        ih prev (hMem hWrite) (.single hOrder) a bytes hWrite
      exact ⟨writer, access, out, hw, hOwner.trans hCta, hFirst, hStage⟩
  exact induction_of_acyclic hAcyclic nodes P hStep i (hMem hi) a bytes hi

/-- At a CTA's earliest first-stage store, an operand read has no proxy order to
the store if every covering Bias fence already precedes the MMA issue. -/
theorem earliestFirstStagingNoOperandFence (hCuQ : Epilogue.DrainCuQProtected p X)
    {writer mma wait : EvId} {isB : Bool} {index : Nat} {loc : Loc}
    (hFirst : EarliestFirstStaging l X writer) (hCta : loc.cta = writer.1 / l.block)
    (hBias : ∀ fence repeated, Thread.BiasOperandFence X fence repeated →
      loc.cta = fence.1 / l.block → baseCausality l X fence mma)
    (hObserved : AsyncFinished l X mma (.mmaRead isB index) wait) :
    ¬ ProxyBefore l X wait writer loc := by
  have hOnly : ∀ f sp scope, X.IsProxyFence f (.async sp) scope →
      sp = some (.shared .cta) ∧ scope = none := by
    intro f sp scope hf
    obtain ⟨hKind, hScope⟩ := actualProxyFence hX hf
    cases hKind
    exact ⟨rfl, hScope⟩
  intro hOrder
  obtain ⟨_, fence, hProxyFence, _, hOwner, _, hBefore, hAfter⟩ :=
    (proxyBefore_iff_of_cta l hOnly).mp hOrder
  rcases Thread.proxyFenceObservation hX hProxyFence with ⟨repeated, hFence⟩ | ⟨stage, hFence⟩
  · exact priorFenceCannotObserveOperand hp hX hCuQ
      (hBias fence repeated hFence hOwner) hObserved hBefore
  · obtain ⟨g, j⟩ := fence
    obtain ⟨k, a, bytes, hWrite, hTrace⟩ := hFence.priorFirstStaging hp hX
    have hP : po X (g,k) (g,j) := by
      apply po_of_not_access hTrace.1 hTrace.2.1 hTrace.2.2
      obtain ⟨_, hf⟩ := hProxyFence
      rw [hf]
      rfl
    exact hFirst (g,k) a bytes hWrite (hOwner.symm.trans hCta)
      ((Relation.TransGen.single (.inl hP)).trans hAfter)

/-- When both Q banks have been issued after every Bias fence in the CTA, the
earliest staging store conflicts with a read in the bank covering its first byte. -/
theorem legacyConflictOfQueryBanksAfterBias (hCuQ : Epilogue.DrainCuQProtected p X) {writer : EvId}
    {a : Acc} {data : List Byte} (hStore : Thread.StageStagingWrite X writer 0 a data)
    (hBanks : ∀ (stage : Fin 2) (step : Fin 8),
      ∃ mma d op accum mask, X.MmaIssue mma d op accum mask ∧
        mma.1 / l.block = writer.1 / l.block ∧ Mma.QueryOperandFragment l mma.1 stage step op ∧
        ∀ fence repeated, Thread.BiasOperandFence X fence repeated →
          fence.1 / l.block = writer.1 / l.block → baseCausality l X fence mma) :
    LegacyStagingOperandConflict l X := by
  obtain ⟨first, dst, bytes, hWrite, hCta, hMin, hStage⟩ := earliestFirstStagingExists hX hStore
  obtain ⟨box, x, row, hx, hr, hDst⟩ := hStage.element hp hX
  let step := Mma.correctionQueryFragment box x 0 hx (by decide)
  obtain ⟨mma, d, op, accum, mask, hMma, hSame, hOperand, hAfterBias⟩ :=
    hBanks (Mma.correctionQueryStage box) step
  have hOwner := hSame.trans hCta.symm
  have hLoc := Mma.correctionQueryByteLoc hp hOwner hx hr (hb := by decide) hOperand
  rw [← hDst] at hLoc
  have hSize : dst.size = 4 := by rw [hDst]; rfl
  have hSpace : dst.loc.space = .shared := by rw [hDst]; rfl
  have hSlot : dst.loc.cta = first.1 / l.block := by rw [hDst]; rfl
  have hCover : dst.Covers (dst.loc.at 0) :=
    ⟨rfl, rfl, by simp [Loc.at], by simp [Loc.at, hSize]⟩
  apply firstStagingLegacyConflictWithoutOperandFence hp hX hCuQ hWrite (by omega) hMma hOwner
    (isB := false) hLoc hCover hSpace
  intro wait hObserved
  exact earliestFirstStagingNoOperandFence hp hX hCuQ hMin hSlot
    (fun fence repeated hBias hFence => hAfterBias fence repeated hBias
      (hFence.symm.trans (hSlot.trans hCta))) hObserved

end PTX.Kernels.TmlFa4Fwd.Safety
