-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringKeyCopyLength
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValuePairSites
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPairSites
import Kernels.TmlFa4Fwd.Proof.LoaderWarmValueNoReentry
import Kernels.TmlFa4Fwd.Proof.LoaderCopyQuietSlice

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

private def valueSite (steady : Bool) : Fin 6 := recurringPacketSite (if steady then 3 else 1)

private def matchingKeySite (steady : Bool) : Fin 6 :=
  recurringPacketSite (if steady then 2 else 0)

private def valueCopyStart (steady : Bool) (pair : Fin 16) : Nat :=
  (if steady then steadyPairShufflePc true pair else warmVShufflePc pair) + 2

private def valueCopyStop (steady : Bool) : Nat := if steady then 1734 else 1341

private def selectorRegister (steady : Bool) (pair : Fin 16) : Nat :=
  packetSizeReg (matchingKeySite steady) pair

private theorem valueSelectorRegister (steady : Bool) (pair : Fin 16) :
    packetSizeReg (valueSite steady) pair = selectorRegister steady pair := by
  cases steady <;> fin_cases pair <;> decide

set_option maxRecDepth 100000 in
private theorem carrySelectorAudit (steady : Bool) (pair : Fin 16) (bound : Nat) :
    let lower := packetPairPc (matchingKeySite steady) pair
    let upper := valueCopyStart steady pair
    ((kernel.code.drop lower).take (upper-lower)).all
      (fun k => loaderPipelineCutOp lower upper bound [selectorRegister steady pair] k.op) =
      true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem carrySelectorRank (steady : Bool) (pair : Fin 16) :
    let lower := packetPairPc (matchingKeySite steady) pair
    let upper := valueCopyStart steady pair
    (((kernel.code.drop lower).take (upper-lower)).zipIdx lower).all
      (fun (k,pc) => LoaderRankedInstr upper pc k) = true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem carrySelectorCount (steady : Bool) (pair : Fin 16) :
    loaderShuffleTail (valueCopyStart steady pair)
      (packetPairPc (matchingKeySite steady) pair) = 32 := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem valueCopyFrame (steady : Bool) (pair : Fin 16) :
    let lower := valueCopyStart steady pair
    let upper := valueCopyStop steady
    ((kernel.code.drop lower).take (upper-lower)).all
      (fun k => loaderPipelineCutOp lower upper (upper-1) [selectorRegister steady pair] k.op) =
      true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem valueCopyAudit (steady : Bool) (pair : Fin 16) (bound : Nat) :
    let lower := valueCopyStart steady pair
    let upper := valueCopyStop steady
    ((kernel.code.drop lower).take (upper-lower)).all
      (fun k => loaderPipelineCutOp lower upper bound [] k.op) = true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem steadyValueCopyQuiet : CopyQuietAudit 1470 1734 := by
  refine ⟨by decide, ⟨_, steadyPairShuffleCode false 0 0, rfl, rfl⟩, ?_, ?_⟩
  · kernel_rfl
  · kernel_rfl

set_option maxRecDepth 100000 in
/-- The V copy reuses the full-vector selector computed for its matching K row. -/
theorem recurringValueCopyFullFromResidual {l : Launch} {X : Execution} {g pos j value : Nat}
    (steady : Bool) (pair : Fin 16) (upper : Bool) {s : TState} {ending : Option TState}
    {spec : AsyncCopy.Spec} (hLive : 8*pair.val < value) (hValue : value < 2^31)
    (hs : At s (if steady then 1468 else 1002) [(if steady then 2155 else 1997,b32 value)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hBefore : pos ≤ j)
    (he : X.get (g,j) = some
      ⟨packetPlanePc (recurringPacketSite (if steady then 3 else 1)) pair upper, .copy spec⟩)
    (hOrdinal : ((X.tr g).take j).countP Execution.isShfl =
      ((X.tr g).take pos).countP Execution.isShfl + 32 + 2*pair.val + 2) :
    spec.src.size = 16 := by
  let key := packetPairPc (matchingKeySite steady) pair
  let start := valueCopyStart steady pair
  let stop := valueCopyStop steady
  let tgt : Event := ⟨packetPlanePc (valueSite steady) pair upper, .copy spec⟩
  let F := [(selectorRegister steady pair,b32 16)]
  have hGet : X.get (g,j) = some tgt := he
  have hSafe : ∀ f, tgt.kind ≠ .ub f := by intro f h; cases h
  have hSpan : 174 ≤ key ∧ key ≤ start ∧ start ≤ tgt.pc ∧ tgt.pc < stop ∧ stop ≤ 1901 := by
    change 174 ≤ key ∧ key ≤ start ∧ start ≤ packetPlanePc (valueSite steady) pair upper ∧
      packetPlanePc (valueSite steady) pair upper < stop ∧ stop ≤ 1901
    cases steady <;> fin_cases pair <;> cases upper <;> decide
  obtain ⟨u,i,_,hu,hU,hI,hRank⟩ :=
    recurringCacheSelectorForLaterEvent steady pair hLive hValue hs hr hBefore hGet
      (hSpan.2.1.trans hSpan.2.2.1) hSafe
  have hu' : At u key F := hu
  obtain ⟨v,passed,_,_,hv,hV,hCount,hCurrent⟩ :=
    prefixRankedShuffleCut (F := F) (show 174 ≤ key ∧ key ≤ start ∧ start ≤ 1901 by omega)
      (carrySelectorAudit steady pair) (carrySelectorRank steady pair)
      hu' hU hGet hI (.inl hSpan.2.2.1) hSafe
  let now := i+passed.length
  have hNow : now ≤ j := hCurrent
  change ((X.tr g).take now).countP Execution.isShfl =
    ((X.tr g).take i).countP Execution.isShfl + loaderShuffleTail start key at hCount
  rw [carrySelectorCount steady pair,hRank] at hCount
  have hEqual : ((X.tr g).take j).countP Execution.isShfl =
      ((X.tr g).take now).countP Execution.isShfl := by omega
  have hQuiet : (((X.tr g).drop now).take (j-now)).countP Execution.isShfl = 0 := by
    conv at hEqual => left; rw [← Nat.add_sub_of_le hNow,List.take_add,List.countP_append]
    omega
  obtain ⟨visits,hWalk⟩ := Mma.walkFromRun hV
  have hj : ((X.tr g).drop now)[j-now]? = some tgt := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hNow]
    exact hGet
  have hPC : start ≤ v.pc ∧ v.pc ≤ stop := by rw [hv.1]; omega
  have hSeen : tgt ∈ loaderSliceEvents start stop visits := by
    cases steady
    · have hWindow : 1004 < tgt.pc ∧ tgt.pc < 1341 := by
        change 1004 < packetPlanePc (valueSite false) pair upper ∧
          packetPlanePc (valueSite false) pair upper < 1341
        fin_cases pair <;> cases upper <;> decide
      exact warmValueQuietSlice (hSpan.1.trans hSpan.2.1) (valueCopyAudit false pair)
        hWalk hPC (ringShapeOfAt hv) hj hWindow hQuiet
    · have hWindow : 1470 < tgt.pc ∧ tgt.pc < 1734 := by
        change 1470 < packetPlanePc (valueSite true) pair upper ∧
          packetPlanePc (valueSite true) pair upper < 1734
        fin_cases pair <;> cases upper <;> decide
      exact copyQuietSlice steadyValueCopyQuiet (hSpan.1.trans hSpan.2.1)
        (valueCopyAudit true pair) hWalk hPC (ringShapeOfAt hv) hj hWindow hQuiet
  obtain ⟨t,w,hPc,hF,hCopy⟩ := loaderCopyWithRegisters (F := F) le_rfl (hSpan.1.trans hSpan.2.1)
    hSpan.2.2.2.2 (valueCopyFrame steady pair) hWalk hv.1.ge (ringShapeOfAt hv)
    hv.2.2.2.2 hSeen rfl
  have hTarget : tgt = ⟨t.pc,.copy spec⟩ := by rw [hPc]
  rw [hTarget] at hCopy
  have hReg := hF.1
  rw [← valueSelectorRegister steady pair] at hReg
  exact packetCopyFullSize (valueSite steady) pair upper hPc hReg hCopy

end PTX.Kernels.TmlFa4Fwd.Loader
