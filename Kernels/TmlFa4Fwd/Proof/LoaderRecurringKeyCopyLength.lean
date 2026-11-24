-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringLengthSeed
public import Kernels.TmlFa4Fwd.Proof.LoaderCopyGeometry
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeyPairSites
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Flow.Code.Part016
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part023
import Kernels.TmlFa4Fwd.Flow.Code.Part024

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private def keySite (steady : Bool) : Fin 6 := recurringPacketSite (if steady then 2 else 0)

private def residualPc (steady : Bool) : Nat := if steady then 1468 else 1002

private def residualReg (steady : Bool) : Nat := if steady then 2155 else 1997

private def keyComparePc (steady : Bool) (pair : Fin 16) : Nat :=
  (if steady then
      (![1468,1479,1488,1496,1504,1512,1520,1528,1536,1545,1553,1561,1569,1577,1585,1593]
        : Fin 16 → Nat)
    else
      (![1002,1014,1023,1031,1039,1047,1055,1063,1071,1080,1088,1096,1104,1112,1120,1128]
        : Fin 16 → Nat)) pair

private def keyCopyPredicate (steady : Bool) (pair : Fin 16) : Nat :=
  (if steady then 212 else 169) + pair.val

private def keySelectPc (steady : Bool) (pair : Fin 16) : Nat :=
  packetPairPc (keySite steady) pair - 1

private def keyCopyCut (steady : Bool) (pair : Fin 16) : Nat :=
  if steady then 1734 else warmKNextShuffleCut pair

private theorem compareCode (steady : Bool) (pair : Fin 16) :
    kernel.code[keyComparePc steady pair]? = some ⟨none,
      signedCompareOp .gt (keyCopyPredicate steady pair) (residualReg steady) (8*pair.val)⟩ := by
  cases steady
  · fin_cases pair
    · exact Flow.code_1002
    · exact Flow.code_1014
    · exact Flow.code_1023
    · exact Flow.code_1031
    · exact Flow.code_1039
    · exact Flow.code_1047
    · exact Flow.code_1055
    · exact Flow.code_1063
    · exact Flow.code_1071
    · exact Flow.code_1080
    · exact Flow.code_1088
    · exact Flow.code_1096
    · exact Flow.code_1104
    · exact Flow.code_1112
    · exact Flow.code_1120
    · exact Flow.code_1128
  · fin_cases pair
    · exact Flow.code_1468
    · exact Flow.code_1479
    · exact Flow.code_1488
    · exact Flow.code_1496
    · exact Flow.code_1504
    · exact Flow.code_1512
    · exact Flow.code_1520
    · exact Flow.code_1528
    · exact Flow.code_1536
    · exact Flow.code_1545
    · exact Flow.code_1553
    · exact Flow.code_1561
    · exact Flow.code_1569
    · exact Flow.code_1577
    · exact Flow.code_1585
    · exact Flow.code_1593

private theorem selectCode (steady : Bool) (pair : Fin 16) :
    kernel.code[keySelectPc steady pair]? = some ⟨none, .int ⟨.selp,.int .b 32,false,
      [some (packetSizeReg (keySite steady) pair)],
      [.imm 16,.imm 0,.reg (keyCopyPredicate steady pair)]⟩⟩ := by
  cases steady
  · fin_cases pair
    · exact Flow.code_1011
    · exact Flow.code_1020
    · exact Flow.code_1028
    · exact Flow.code_1036
    · exact Flow.code_1044
    · exact Flow.code_1052
    · exact Flow.code_1060
    · exact Flow.code_1068
    · exact Flow.code_1077
    · exact Flow.code_1085
    · exact Flow.code_1093
    · exact Flow.code_1101
    · exact Flow.code_1109
    · exact Flow.code_1117
    · exact Flow.code_1125
    · exact Flow.code_1133
  · fin_cases pair
    · exact Flow.code_1476
    · exact Flow.code_1485
    · exact Flow.code_1493
    · exact Flow.code_1501
    · exact Flow.code_1509
    · exact Flow.code_1517
    · exact Flow.code_1525
    · exact Flow.code_1533
    · exact Flow.code_1542
    · exact Flow.code_1550
    · exact Flow.code_1558
    · exact Flow.code_1566
    · exact Flow.code_1574
    · exact Flow.code_1582
    · exact Flow.code_1590
    · exact Flow.code_1598

theorem loaderStraightCore {l : Launch} {g n pc pc' : Nat} {F H : List (Nat × Value)}
    (hSpan : 174 ≤ pc ∧ pc+n ≤ 1906)
    (hStraight : ((kernel.code.drop pc).take (n-1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hCore : Seg kernel [] l g n pc F pc' H) : Seg kernel Assumptions.all l g n pc F pc' H := by
  intro s hs
  obtain ⟨u,hu,hU⟩ := hCore s hs
  exact ⟨u,(loaderLinear (regs := []) hSpan.1 hSpan.2 hs.1 (by simp) hStraight hu).1,hU⟩

private theorem keyCopySpan (steady : Bool) (pair : Fin 16) (upper : Bool) :
    174 ≤ residualPc steady ∧ residualPc steady ≤ keyComparePc steady pair ∧
    keyComparePc steady pair+1 ≤ keySelectPc steady pair ∧
    keySelectPc steady pair+1 = packetPairPc (keySite steady) pair ∧
    packetPairPc (keySite steady) pair ≤ packetPlanePc (keySite steady) pair upper ∧
    packetPlanePc (keySite steady) pair upper < keyCopyCut steady pair ∧
    keyCopyCut steady pair ≤ 1901 := by
  cases steady <;> fin_cases pair <;> cases upper <;> decide

set_option maxRecDepth 100000 in
private theorem compareAudit (steady : Bool) (pair : Fin 16) (bound : Nat) :
    let r := residualPc steady
    let c := keyComparePc steady pair
    ((kernel.code.drop r).take (c-r)).all
      (fun i => loaderPipelineCutOp r c bound [residualReg steady] i.op) = true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem compareRank (steady : Bool) (pair : Fin 16) :
    let r := residualPc steady
    let c := keyComparePc steady pair
    (((kernel.code.drop r).take (c-r)).zipIdx r).all
      (fun (i,pc) => LoaderRankedInstr c pc i) = true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem selectAudit (steady : Bool) (pair : Fin 16) (bound : Nat) :
    let beginPc := keyComparePc steady pair+1
    let endPc := keySelectPc steady pair
    ((kernel.code.drop beginPc).take (endPc-beginPc)).all
      (fun i => loaderPipelineCutOp beginPc endPc bound [keyCopyPredicate steady pair] i.op)
        = true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem selectRank (steady : Bool) (pair : Fin 16) :
    let beginPc := keyComparePc steady pair+1
    let endPc := keySelectPc steady pair
    (((kernel.code.drop beginPc).take (endPc-beginPc)).zipIdx beginPc).all
      (fun (i,pc) => LoaderRankedInstr endPc pc i) = true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem selectorRankCount (steady : Bool) (pair : Fin 16) :
    let r := residualPc steady
    let c := keyComparePc steady pair
    let d := keySelectPc steady pair
    loaderShuffleTail c r + loaderShuffleTail d (c+1) = 2*pair.val+2 := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem copyAudit (steady : Bool) (pair : Fin 16) (bound : Nat) :
    let lower := packetPairPc (keySite steady) pair
    let cut := keyCopyCut steady pair
    ((kernel.code.drop lower).take (cut-lower)).all
      (fun k => loaderPipelineCutOp lower cut bound [] k.op) = true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem copyRank (steady : Bool) (pair : Fin 16) :
    let lower := packetPairPc (keySite steady) pair
    let cut := keyCopyCut steady pair
    (((kernel.code.drop lower).take (cut-lower)).zipIdx lower).all
      (fun (k,pc) => LoaderRankedInstr cut pc k) = true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem copyRemaining (steady : Bool) (pair : Fin 16) :
    0 < loaderShuffleTail (keyCopyCut steady pair) (packetPairPc (keySite steady) pair) := by
  cases steady <;> fin_cases pair <;> exact of_decide_eq_true (by kernel_rfl)

set_option maxRecDepth 100000 in
private theorem copyFrame (steady : Bool) (pair : Fin 16) :
    let lower := packetPairPc (keySite steady) pair
    let cut := keyCopyCut steady pair
    ((kernel.code.drop lower).take (cut-lower)).all
      (fun k => loaderPipelineCutOp lower cut (cut-1) [packetSizeReg (keySite steady) pair] k.op)
        = true := by
  cases steady <;> fin_cases pair <;> kernel_rfl

set_option maxRecDepth 100000 in
/-- The observed packet's live-row comparison establishes the selector shared
by its K and V copies. The demanding event may be in either packet. -/
theorem recurringCacheSelectorForLaterEvent {l : Launch} {X : Execution} {g pos j value : Nat}
    (steady : Bool) (pair : Fin 16) {s : TState} {stop : Option TState}
    (hLive : 8*pair.val < value) (hValue : value < 2^31)
    (hs : At s (if steady then 1468 else 1002)
      [(if steady then 2155 else 1997,b32 value)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) stop)
    (hBefore : pos ≤ j) {target : Event} (he : X.get (g,j) = some target)
    (hDemand : packetPairPc (recurringPacketSite (if steady then 2 else 0)) pair ≤ target.pc)
    (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u i ending,
      let stage := recurringPacketSite (if steady then 2 else 0)
      At u (packetPairPc stage pair) [(packetSizeReg stage pair,b32 16)] ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop i) ending ∧ i ≤ j ∧
        ((X.tr g).take i).countP Execution.isShfl =
          ((X.tr g).take pos).countP Execution.isShfl + 2*pair.val+2 := by
  let r := residualPc steady
  let c := keyComparePc steady pair
  let d := keySelectPc steady pair
  let stage := keySite steady
  let pred := keyCopyPredicate steady pair
  let lower := packetPairPc stage pair
  let A := [(residualReg steady,b32 value)]
  let B : List (Nat × Value) := [(pred,.pred true)]
  let C := [(packetSizeReg stage pair,b32 16)]
  have hs' : At s r A := hs
  have hSpan := keyCopySpan steady pair false
  change 174 ≤ r ∧ r ≤ c ∧ c+1 ≤ d ∧ d+1 = lower ∧
    lower ≤ packetPlanePc stage pair false ∧
    packetPlanePc stage pair false < keyCopyCut steady pair ∧ keyCopyCut steady pair ≤ 1901 at hSpan
  change lower ≤ target.pc at hDemand
  have hCompareRange : 174 ≤ r ∧ r ≤ c ∧ c ≤ 1901 := by omega
  have hCompareAudit (bound : Nat) : ((kernel.code.drop r).take (c-r)).all
      (fun i => loaderPipelineCutOp r c bound (A.map Prod.fst) i.op) = true :=
    compareAudit steady pair bound
  have hCompareRank : (((kernel.code.drop r).take (c-r)).zipIdx r).all
      (fun (i,pc) => LoaderRankedInstr c pc i) = true := compareRank steady pair
  obtain ⟨a,front,out,_,ha,haRun,haRank,haBefore⟩ :=
    prefixRankedShuffleCut hCompareRange hCompareAudit hCompareRank hs' hr he hBefore
      (.inl (by omega)) hSafe
  have hCmpSeg : Seg kernel Assumptions.all l g 1 c A (c+1) B :=
    loaderStraightCore (by omega) (by simp)
      (liveKeyCompareCore (compareCode steady pair) hLive hValue)
  obtain ⟨b,hb,hB⟩ := hCmpSeg a ha
  have hbRun := haRun.after_local_nonempty (run_rtg hb) (traceAfterObservedEvent he haBefore)
  have hSelectRange : 174 ≤ c+1 ∧ c+1 ≤ d ∧ d ≤ 1901 := by omega
  have hSelectAudit (bound : Nat) : ((kernel.code.drop (c+1)).take (d-(c+1))).all
      (fun i => loaderPipelineCutOp (c+1) d bound (B.map Prod.fst) i.op) = true :=
    selectAudit steady pair bound
  have hSelectRank : (((kernel.code.drop (c+1)).take (d-(c+1))).zipIdx (c+1)).all
      (fun (i,pc) => LoaderRankedInstr d pc i) = true := selectRank steady pair
  obtain ⟨t,front',out',_,ht,htRun,htRank,htBefore⟩ :=
    prefixRankedShuffleCut hSelectRange hSelectAudit hSelectRank hB hbRun he
      haBefore (.inl (by omega)) hSafe
  have hsSeg : Seg kernel Assumptions.all l g 1 d B (d+1) C :=
    loaderStraightCore (by omega) (by simp) (liveKeySelectCore (selectCode steady pair))
  obtain ⟨u,hu,hU⟩ := hsSeg t ht
  have huRun := htRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he htBefore)
  have huAt : At u lower C := by simpa only [hSpan.2.2.2.1] using hU
  let i := pos+front.length+front'.length
  have hRankSum : loaderShuffleTail c r + loaderShuffleTail d (c+1) = 2*pair.val+2 :=
    selectorRankCount steady pair
  refine ⟨u,i,out',huAt,huRun,htBefore,?_⟩
  change ((X.tr g).take (pos+front.length+front'.length)).countP Execution.isShfl =
    ((X.tr g).take (pos+front.length)).countP Execution.isShfl + _ at htRank
  unfold i
  rw [htRank,haRank]
  omega

set_option maxRecDepth 100000 in
/-- A copy at the observed shuffle ordinal uses its live row's full-vector selector. -/
theorem recurringKeyCopyFullFromResidual {l : Launch} {X : Execution} {g pos j value : Nat}
    (steady : Bool) (pair : Fin 16) (upper : Bool) {s : TState} {stop : Option TState}
    {sp : AsyncCopy.Spec} (hLive : 8*pair.val < value) (hValue : value < 2^31)
    (hs : At s (if steady then 1468 else 1002)
      [(if steady then 2155 else 1997,b32 value)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) stop)
    (hBefore : pos ≤ j)
    (he : X.get (g,j) =
      some ⟨packetPlanePc (recurringPacketSite (if steady then 2 else 0)) pair upper,.copy sp⟩)
    (hOrdinal : ((X.tr g).take j).countP Execution.isShfl =
      ((X.tr g).take pos).countP Execution.isShfl + 2*pair.val+2) :
    sp.src.size = 16 := by
  let tgt : Event := ⟨packetPlanePc (keySite steady) pair upper,.copy sp⟩
  let stage := keySite steady
  let lower := packetPairPc stage pair
  let cut := keyCopyCut steady pair
  let C := [(packetSizeReg stage pair,b32 16)]
  have hGet : X.get (g,j) = some tgt := he
  have hSafe : ∀ f, tgt.kind ≠ .ub f := by intro f h; cases h
  have hSpan : 174 ≤ residualPc steady ∧ residualPc steady ≤ keyComparePc steady pair ∧
      keyComparePc steady pair+1 ≤ keySelectPc steady pair ∧
      keySelectPc steady pair+1 = lower ∧ lower ≤ tgt.pc ∧ tgt.pc < cut ∧ cut ≤ 1901 :=
    keyCopySpan steady pair upper
  obtain ⟨u,i,_,huAt,huRun,hi,hRank⟩ :=
    recurringCacheSelectorForLaterEvent steady pair hLive hValue hs hr hBefore hGet
      hSpan.2.2.2.2.1 hSafe
  have hEqual : ((X.tr g).take j).countP Execution.isShfl =
      ((X.tr g).take i).countP Execution.isShfl := hOrdinal.trans hRank.symm
  obtain ⟨walk,hWalk⟩ := Mma.walkFromRun huRun
  have hj : ((X.tr g).drop i)[j-i]? = some tgt := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hi]
    exact hGet
  have hSpan' : 174 ≤ lower ∧ lower ≤ cut ∧ cut ≤ 1901 := by omega
  have hAudit (bound : Nat) : ((kernel.code.drop lower).take (cut-lower)).all
      (fun k => loaderPipelineCutOp lower cut bound [] k.op) = true := copyAudit steady pair bound
  have hCounted : (((kernel.code.drop lower).take (cut-lower)).zipIdx lower).all
      (fun (k,pc) => LoaderRankedInstr cut pc k) = true := copyRank steady pair
  have hRemain : 0 < loaderShuffleTail cut lower := copyRemaining steady pair
  have hNoShfl : (((X.tr g).drop i).take (j-i)).countP Execution.isShfl = 0 := by
    conv at hEqual => left; rw [← Nat.add_sub_of_le hi, List.take_add, List.countP_append]
    omega
  have hSeen := loaderEventInRankedSlice hSpan' le_rfl hAudit hCounted hWalk
    (by rw [huAt.1]; exact ⟨le_rfl,hSpan'.2.1⟩) (ringShapeOfAt huAt) hj
    (by rw [hNoShfl,huAt.1]; exact hRemain)
  have hFrame : ((kernel.code.drop lower).take (cut-lower)).all
      (fun k => loaderPipelineCutOp lower cut (cut-1) (C.map Prod.fst) k.op) = true :=
    copyFrame steady pair
  obtain ⟨v,w,hV,hC,hCopy⟩ := loaderCopyWithRegisters le_rfl hSpan'.1 hSpan'.2.2
    hFrame hWalk huAt.1.ge (ringShapeOfAt huAt) huAt.2.2.2.2 hSeen rfl
  have hTarget : tgt = ⟨v.pc,.copy sp⟩ := by rw [hV]
  rw [hTarget] at hCopy
  exact packetCopyFullSize stage pair upper hV hC.1 hCopy

end
end PTX.Kernels.TmlFa4Fwd.Loader
