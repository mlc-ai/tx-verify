-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeyPairSites
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem warmKPairSourceRun {l : Launch} {g base tid : Nat}
    (hBase : base < 2 ^ 64) (pair : Fin 16) :
    Seg kernel Assumptions.all l g (warmKSourceCut pair - (warmKShufflePc pair + 2))
      (warmKShufflePc pair + 2) (warmKPairInputs pair base tid) (warmKSourceCut pair)
      [(packetSrcReg (recurringPacketSite 0) pair, b64 (recurringSourceAddress base tid))] := by
  intro s hs
  obtain ⟨u, hu, hU⟩ := warmKPairSourceCore hBase pair s hs
  have hL : 174 ≤ warmKShufflePc pair + 2 := by fin_cases pair <;> decide
  have hH : warmKShufflePc pair + 2 + (warmKSourceCut pair - (warmKShufflePc pair + 2)) ≤
      1906 := by fin_cases pair <;> decide
  have hSeq : ((kernel.code.drop (warmKShufflePc pair + 2)).take
      (warmKSourceCut pair - (warmKShufflePc pair + 2) - 1)).all
        (fun ins => schedulerFallsThrough ins.op) = true := by
    fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)
  exact ⟨u, (loaderLinear (regs := []) hL hH hs.1 (by simp) hSeq hu).1, hU⟩

set_option maxRecDepth 100000 in
/-- A copy following the selected broadcast, before the next shuffle, has the
source computed from the two broadcast words and its own lane column. -/
theorem warmKPairSourceOfTrace {l : Launch} {X : Execution}
    {g start j base tid : Nat} (hBase : base < 2 ^ 64) (pair : Fin 16) (upper : Bool)
    {s : TState} {ending : Option TState} {sp : AsyncCopy.Spec}
    (hs : At s (warmKShufflePc pair + 2) (warmKPairInputs pair base tid))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop start) ending)
    (hOrder : start ≤ j)
    (he : X.get (g, j) = some ⟨packetPlanePc (recurringPacketSite 0) pair upper, .copy sp⟩)
    (hRank : ((X.tr g).take j).countP Execution.isShfl =
      ((X.tr g).take start).countP Execution.isShfl) :
    sp.src.loc = globalLoc ((base + 16 * (tid % 8) + packetSrcOff upper) % 2 ^ 64) := by
  let lower := warmKShufflePc pair + 2
  let cut := warmKNextShuffleCut pair
  let seed := warmKSourceCut pair
  let target : Event := ⟨packetPlanePc (recurringPacketSite 0) pair upper, .copy sp⟩
  let F := [(packetSrcReg (recurringPacketSite 0) pair, b64 (recurringSourceAddress base tid))]
  obtain ⟨walk, hWalk⟩ := Mma.walkFromRun hr
  have hNext : ((X.tr g).drop start)[j - start]? = some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hOrder]
    exact he
  have hStarts : 174 ≤ lower ∧ lower ≤ cut ∧ cut ≤ 1901 := by fin_cases pair <;> decide
  have hAudit (bound : Nat) : ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut bound [] ins.op) = true := by
    fin_cases pair <;> kernel_rfl
  have hCounted : (((kernel.code.drop lower).take (cut - lower)).zipIdx lower).all
      (fun (ins, pc) => LoaderRankedInstr cut pc ins) = true := by
    fin_cases pair <;> kernel_rfl
  have hCount : loaderShuffleTail cut lower = 1 := by fin_cases pair <;> kernel_rfl
  have hZero : (((X.tr g).drop start).take (j - start)).countP Execution.isShfl = 0 := by
    conv at hRank => left; rw [← Nat.add_sub_of_le hOrder, List.take_add, List.countP_append]
    omega
  have hSlice : target ∈ loaderSliceEvents lower cut walk := by
    apply loaderEventInRankedSlice hStarts le_rfl hAudit hCounted hWalk
      (by rw [hs.1]; exact ⟨le_rfl, hStarts.2.1⟩) (ringShapeOfAt hs) hNext
    rw [hZero, hs.1, hCount]
    decide
  obtain ⟨t, ht, hT⟩ := warmKPairSourceRun hBase pair s hs
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
    packetCopySource (recurringPacketSite 0) pair upper hpc hField.1
      (Nat.mod_lt _ (by decide : 0 < 2 ^ 64)) hStep

end
end PTX.Kernels.TmlFa4Fwd.Loader
