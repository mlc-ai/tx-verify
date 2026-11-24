-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPairSites
import Kernels.TmlFa4Fwd.Proof.LoaderCopyQuietSlice

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

set_option maxRecDepth 100000 in
private theorem steadyCopyQuietAudit : CopyQuietAudit 1470 1734 := by
  refine ⟨by decide, ⟨_, steadyPairShuffleCode false 0 0, rfl, rfl⟩, ?_, ?_⟩
  · kernel_rfl
  · kernel_rfl

private theorem steadyPairSourceRun {l : Launch} {g base tid : Nat}
    (hBase : base < 2 ^ 64) (value : Bool) (pair : Fin 16) :
    Seg kernel Assumptions.all l g
      (steadyPairSourceCut value pair - (steadyPairShufflePc value pair + 2))
      (steadyPairShufflePc value pair + 2) (steadyPairInputs value pair base tid)
      (steadyPairSourceCut value pair)
      [(packetSrcReg (recurringPacketSite (steadySpillSite value)) pair,
        b64 (recurringSourceAddress base tid))] := by
  intro s hs
  obtain ⟨u, hu, hU⟩ := steadyPairSourceCore hBase value pair s hs
  have hL : 174 ≤ steadyPairShufflePc value pair + 2 := by cases value <;> fin_cases pair <;> decide
  have hH : steadyPairShufflePc value pair + 2 +
      (steadyPairSourceCut value pair - (steadyPairShufflePc value pair + 2)) ≤
      1906 := by cases value <;> fin_cases pair <;> decide
  have hSeq : ((kernel.code.drop (steadyPairShufflePc value pair + 2)).take
      (steadyPairSourceCut value pair - (steadyPairShufflePc value pair + 2) - 1)).all
        (fun ins => schedulerFallsThrough ins.op) = true := by
    cases value <;> fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)
  exact ⟨u, (loaderLinear (regs := []) hL hH hs.1 (by simp) hSeq hu).1, hU⟩

set_option maxRecDepth 100000 in
/-- A recorded copy at the freshly broadcast ordinal uses its lane's computed source. -/
theorem steadyPairSourceOfTrace {l : Launch} {X : Execution}
    {g start j base tid : Nat} (hBase : base < 2 ^ 64) (value : Bool)
    (pair : Fin 16) (upper : Bool)
    {s : TState} {ending : Option TState} {sp : AsyncCopy.Spec}
    (hs : At s (steadyPairShufflePc value pair + 2) (steadyPairInputs value pair base tid))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop start) ending)
    (hOrder : start ≤ j)
    (he : X.get (g, j) =
      some ⟨packetPlanePc (recurringPacketSite (steadySpillSite value)) pair upper, .copy sp⟩)
    (hRank : ((X.tr g).take j).countP Execution.isShfl =
      ((X.tr g).take start).countP Execution.isShfl) :
    sp.src.loc = globalLoc ((base + 16 * (tid % 8) + packetSrcOff upper) % 2 ^ 64) := by
  let lower := steadyPairShufflePc value pair + 2
  let cut := 1734
  let seed := steadyPairSourceCut value pair
  let site := recurringPacketSite (steadySpillSite value)
  let target : Event := ⟨packetPlanePc site pair upper, .copy sp⟩
  let F := [(packetSrcReg site pair, b64 (recurringSourceAddress base tid))]
  obtain ⟨walk, hWalk⟩ := Mma.walkFromRun hr
  have hNext : ((X.tr g).drop start)[j - start]? = some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hOrder]
    exact he
  have hStarts : 174 ≤ lower ∧ lower ≤ cut ∧ cut ≤ 1901 := by
    cases value <;> fin_cases pair <;> decide
  have hAudit (bound : Nat) : ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut bound [] ins.op) = true := by
    cases value <;> fin_cases pair <;> kernel_rfl
  have hZero : (((X.tr g).drop start).take (j - start)).countP Execution.isShfl = 0 := by
    conv at hRank => left; rw [← Nat.add_sub_of_le hOrder, List.take_add, List.countP_append]
    omega
  have hInside : 1470 < target.pc ∧ target.pc < cut := by
    change 1470 < packetPlanePc site pair upper ∧ packetPlanePc site pair upper < cut
    cases value <;> fin_cases pair <;> cases upper <;> decide
  have hSlice : target ∈ loaderSliceEvents lower cut walk :=
    copyQuietSlice steadyCopyQuietAudit hStarts.1 hAudit hWalk
      (by rw [hs.1]; exact ⟨le_rfl, hStarts.2.1⟩) (ringShapeOfAt hs) hNext hInside hZero
  obtain ⟨t, ht, hT⟩ := steadyPairSourceRun hBase value pair s hs
  obtain ⟨tail, hTail, _, hSaw⟩ := loaderEventAfterLocal ht hWalk hSlice
  have hScope : lower ≤ seed := by cases value <;> fin_cases pair <;> decide
  have hLower : 174 ≤ seed := hStarts.1.trans hScope
  have hFrame : ((kernel.code.drop seed).take (cut - seed)).all
      (fun ins => loaderPipelineCutOp seed cut (cut - 1) (F.map Prod.fst) ins.op) = true := by
    cases value <;> fin_cases pair <;> kernel_rfl
  obtain ⟨u, v, hpc, hField, hStep⟩ := loaderCopyWithRegisters
    hScope hLower hStarts.2.2 hFrame hTail hT.1.ge
    (ringShapeOfAt hT) hT.2.2.2.2 hSaw rfl
  have heq : target = ⟨u.pc, .copy sp⟩ := by rw [hpc]
  rw [heq] at hStep
  simpa [recurringSourceAddress, Nat.mod_add_mod] using
    packetCopySource site pair upper hpc hField.1
      (Nat.mod_lt _ (by decide : 0 < 2 ^ 64)) hStep

end
end PTX.Kernels.TmlFa4Fwd.Loader
