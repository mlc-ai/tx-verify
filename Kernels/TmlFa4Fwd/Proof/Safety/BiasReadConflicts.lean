-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasReadOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitBiasWordOrder
import Kernels.TmlFa4Fwd.Proof.InputActualSources
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.AsyncCopy PTX.Proof Protocol.Bias Thread Thread.Scores Thread.Loader
open Prologue Softmax

private theorem biasReadByteInBox (l : Launch) (g : Nat) (stage : Fin 2)
    (repeated : Bool) (v : Fin 16) (word : Fin 4) {loc : Loc}
    (hCover : (biasReadAcc l g (biasVectorBase l g stage repeated v) repeated v word.val).Covers
      loc) :
    (⟨.shared,g/l.block,biasBoxStart l stage (biasVectorHalf v).val⟩ : Loc).InRange 16384 loc := by
  let acc := biasReadAcc l g (biasVectorBase l g stage repeated v) repeated v word.val
  have hLo : acc.loc.addr ≤ loc.addr := hCover.2.2.1
  have hHi : loc.addr < acc.loc.addr+4 := hCover.2.2.2
  let byte : Fin 4 := ⟨loc.addr-acc.loc.addr,by omega⟩
  have hLoc : acc.loc.at byte.val = loc := by
    obtain ⟨space,owner,addr⟩ := loc
    obtain ⟨hSpace,hOwner,_,_⟩ := hCover
    change space = acc.loc.space at hSpace
    change owner = acc.loc.cta at hOwner
    simp only [Loc.at, hSpace, hOwner]
    congr
    exact Nat.add_sub_of_le hLo
  let base := biasBoxStart l stage (biasVectorHalf v).val
  let raw := 128*((g%l.block)%128)+16*(v.val%8)
  have hRow : raw/128 = (g%l.block)%128 := by dsimp [raw]; omega
  have hByte : raw%16 = 0 := by dsimp [raw]; omega
  have hChunk := (TensorSwizzle.chunk .b128 base (raw/128) (BitVec.ofNat 3 (raw/16))).isLt
  have hSub := word.isLt
  have hCoord := byte.isLt
  have hRowBound : (g%l.block)%128 < 128 := Nat.mod_lt _ (by decide)
  rw [← hLoc]
  refine ⟨rfl,rfl,?_,?_⟩
  · simp only [acc,biasReadAcc,biasVectorBase_add,biasVectorAddress,Loc.at,biasVectorHalf]
    omega
  · change acc.loc.addr + byte.val < base+16384
    change biasVectorBase l g stage repeated v + (biasReadSite repeated v).offset +
      4*word.val + byte.val < base+16384
    rw [biasVectorBase_add]
    change base+TensorSwizzle.offset .b128 base raw+4*word.val+byte.val < base+16384
    unfold TensorSwizzle.offset
    rw [hRow,hByte,Nat.add_zero]
    rw [hRow] at hChunk
    omega

/-- Every overlap of a Bias input write with an actual softmax Bias word has a
byte-causality order in an arbitrary consistent execution prefix. -/
theorem tensorBiasReadConflictOrdered {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {tensor read : EvId} {x y byte : Nat} {a b : Acc} {loc : Loc}
    (hTensor : X.AsyncFootprint tensor (.write (.load x y byte)) a) (ha : a.Covers loc)
    {repeated : Bool} {v : Fin 16} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X read repeated v b bytes) (hb : b.Covers loc) :
    ByteCausality l X loc (.async tensor (.write (.load x y byte))) (.thread read) ∨
      ByteCausality l X loc (.thread read) (.async tensor (.write (.load x y byte))) := by
  have hCover : AsyncCovers X tensor (.write (.load x y byte)) loc := ⟨a,true,⟨rfl,hTensor⟩,ha⟩
  obtain ⟨spec,address,hIssue,hLocation,hSize⟩ := hTensor
  rw [Acc.loc_of_one ha hSize] at hLocation
  obtain ⟨w,word,hWarp,hStage,rfl⟩ := biasVectorReadAccess hp hX hRead
  let stage := stageOf w
  let half := biasVectorHalf v
  have hRange := biasReadByteInBox l read.1 stage repeated v word hb
  obtain ⟨hOwner,hBox⟩ := biasWriterOfHalf hp hX (g := read.1) hIssue hLocation hRange
  have hWarpBound : warpIndex l read.1 < 8 := hWarp ▸ w.isLt
  have hStageEq : warpIndex l read.1/4 = stage.val := hStage.symm
  obtain ⟨wait,j,phase,r,hRecord,hId,hOk,hObserved,hLower,hBefore⟩ :=
    biasReadReadyObservation hp hX stage hRead hWarpBound hStageEq
  rcases Nat.lt_trichotomy (biasTensorOrdinal l X stage half tensor) phase with hLt | hEq | hGt
  · exact .inl (.direct (earlierBiasWriteBeforeRead hp hX stage half (wait := (read.1,wait))
      hBox hOwner hRecord hId hOk hObserved hLt hBefore hCover))
  · obtain ⟨selected,box,hSelectedCta,hSelected,hOrdinal,hNotice⟩ :=
      biasReadyObservedHalfOwner hp hX stage half hRecord hOk hObserved
    have hSame := biasTensorOrdinalInjective hp hX hSelected hBox
      (hSelectedCta.trans hOwner.symm) (hOrdinal.trans hEq.symm)
    subst selected
    rw [hId] at hNotice
    have hObserve := biasTensorObservedAtCTA hX hNotice
    obtain ⟨_,_,_,_,_,hWait⟩ := hObserve.tensor
    obtain ⟨_,_,he⟩ := hWait.1
    have hSameCta : SameCta l tensor.1 read.1 := by
      obtain ⟨_,ht⟩ := hIssue
      exact ⟨event_thread_lt hX ht,event_thread_lt hX hRead,hOwner⟩
    have hOrdering : baseCausality l X (read.1,wait) read :=
      .single (.inl (po_of_source_not_access hBefore.1 hBefore.2.1 hBefore.2.2
        (by rw [he]; rfl)))
    exact .inl (.direct ⟨hCover,_,.inr ⟨.cta,hObserve,
      MbarRing.Unit.Gate.scopesMeet hSameCta .cluster .cta⟩,.inl hOrdering⟩)
  · exact .inr (.direct (biasReadBeforeLaterWrite hp hX stage half hRead hWarpBound hStageEq
      hBox hOwner (hLower.trans_lt hGt) hRange.1 hRange.2.1 hCover))

end PTX.Kernels.TmlFa4Fwd.Safety
