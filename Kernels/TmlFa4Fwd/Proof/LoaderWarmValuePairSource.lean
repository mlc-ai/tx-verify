-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValuePairSites
import Kernels.TmlFa4Fwd.Proof.LoaderWarmValueNoReentry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem warmVPairSourceRun {l : Launch} {g base tid : Nat}
    (hBase : base < 2 ^ 64) (hTid : tid < 512) (pair : Fin 16) :
    Seg kernel Assumptions.all l g (warmVSourceCut pair - (warmVShufflePc pair + 2))
      (warmVShufflePc pair + 2) (warmVPairInputs pair base tid) (warmVSourceCut pair)
      [(packetSrcReg (recurringPacketSite 1) pair, b64 (recurringSourceAddress base tid))] := by
  intro s hs
  obtain ⟨u, hu, hU⟩ := warmVPairSourceCore hBase hTid pair s hs
  have hL : 174 ≤ warmVShufflePc pair + 2 := by fin_cases pair <;> decide
  have hH : warmVShufflePc pair + 2 + (warmVSourceCut pair - (warmVShufflePc pair + 2)) ≤
      1906 := by fin_cases pair <;> decide
  have hSeq : ((kernel.code.drop (warmVShufflePc pair + 2)).take
      (warmVSourceCut pair - (warmVShufflePc pair + 2) - 1)).all
        (fun ins => schedulerFallsThrough ins.op) = true := by
    fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)
  exact ⟨u, (loaderLinear (regs := []) hL hH hs.1 (by simp) hSeq hu).1, hU⟩

set_option maxRecDepth 100000 in
/-- A warm V copy at the broadcast ordinal has the
source computed from the two broadcast words and its own lane column. -/
theorem warmVPairSourceOfTrace {l : Launch} {X : Execution}
    {g start j base tid : Nat} (hBase : base < 2 ^ 64) (hTid : tid < 512)
    (pair : Fin 16) (upper : Bool)
    {s : TState} {ending : Option TState} {sp : AsyncCopy.Spec}
    (hs : At s (warmVShufflePc pair + 2) (warmVPairInputs pair base tid))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop start) ending)
    (hOrder : start ≤ j)
    (he : X.get (g, j) = some ⟨packetPlanePc (recurringPacketSite 1) pair upper, .copy sp⟩)
    (hRank : ((X.tr g).take j).countP Execution.isShfl =
      ((X.tr g).take start).countP Execution.isShfl) :
    sp.src.loc = globalLoc ((base + 16 * (tid % 8) + packetSrcOff upper) % 2 ^ 64) := by
  let lower := warmVShufflePc pair + 2
  let cut := 1341
  let seed := warmVSourceCut pair
  let target : Event := ⟨packetPlanePc (recurringPacketSite 1) pair upper, .copy sp⟩
  let F := [(packetSrcReg (recurringPacketSite 1) pair, b64 (recurringSourceAddress base tid))]
  obtain ⟨walk, hWalk⟩ := Mma.walkFromRun hr
  have hNext : ((X.tr g).drop start)[j - start]? = some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hOrder]
    exact he
  have hStarts : 174 ≤ lower ∧ lower ≤ cut ∧ cut ≤ 1901 := by fin_cases pair <;> decide
  have hAudit (bound : Nat) : ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut bound [] ins.op) = true := by
    fin_cases pair <;> kernel_rfl
  have hZero : (((X.tr g).drop start).take (j - start)).countP Execution.isShfl = 0 := by
    conv at hRank => left; rw [← Nat.add_sub_of_le hOrder, List.take_add, List.countP_append]
    omega
  have hInside : 1004 < target.pc ∧ target.pc < 1341 := by
    change 1004 < packetPlanePc (recurringPacketSite 1) pair upper ∧
      packetPlanePc (recurringPacketSite 1) pair upper < 1341
    fin_cases pair <;> cases upper <;> decide
  have hSlice : target ∈ loaderSliceEvents lower cut walk :=
    warmValueQuietSlice hStarts.1 hAudit hWalk
      (by rw [hs.1]; exact ⟨le_rfl, hStarts.2.1⟩) (ringShapeOfAt hs) hNext hInside hZero
  obtain ⟨t, ht, hT⟩ := warmVPairSourceRun hBase hTid pair s hs
  obtain ⟨tail, hTail, _, hSaw⟩ := loaderEventAfterLocal ht hWalk hSlice
  have hScope : lower ≤ seed := by fin_cases pair <;> decide
  have hLower : 174 ≤ seed := hStarts.1.trans hScope
  have hFrame : ((kernel.code.drop seed).take (cut - seed)).all
      (fun ins => loaderPipelineCutOp seed cut (cut - 1) (F.map Prod.fst) ins.op) = true := by
    fin_cases pair <;> kernel_rfl
  obtain ⟨u, v, hpc, hField, hStep⟩ := loaderCopyWithRegisters
    hScope hLower hStarts.2.2 hFrame hTail hT.1.ge
    (ringShapeOfAt hT) hT.2.2.2.2 hSaw rfl
  have heq : target = ⟨u.pc, .copy sp⟩ := by rw [hpc]
  rw [heq] at hStep
  simpa [recurringSourceAddress, Nat.mod_add_mod] using
    packetCopySource (recurringPacketSite 1) pair upper hpc hField.1
      (Nat.mod_lt _ (by decide : 0 < 2 ^ 64)) hStep

end
end PTX.Kernels.TmlFa4Fwd.Loader
