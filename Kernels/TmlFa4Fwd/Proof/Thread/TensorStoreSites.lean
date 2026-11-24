-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemStores
import Lemmas.Flow.NotTcSt
import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow

private def scoreStoreRounds : List Softmax.Round := [.first,.biased,.unbiased]

private def probabilityStoreSites : List Nat :=
  scoreStoreRounds.flatMap fun round => (List.finRange 4).map (Softmax.probabilityPc round)

private def correctionStoreSites : List Nat :=
  (List.finRange 2).flatMap fun stage => (List.finRange 8).map (Correction.rescaleStorePc stage)

set_option maxRecDepth 100000 in
private theorem tensorStoreCode :
    OpPcsFast kernel.code tcStOp (probabilityStoreSites ++ correctionStoreSites) = true := by
  kernel_rfl

/-- Every actual Tensor Memory store is a probability publication or an output rescale. -/
theorem tensorStoreSite {l : Launch} {m : Mem0} {X : Execution} {A : List Assumption}
    (hX : Consistent l kernel A m X) {i : EvId} {pc addr : Nat} {vals : List Value}
    {sh : TcShape} (he : X.get i = some ⟨pc,.tc (.st addr vals sh)⟩) :
    (∃ (round : Softmax.Round) (q : Fin 4), pc = Softmax.probabilityPc round q) ∨
    (∃ (stage : Fin 2) (chunk : Fin 8), pc = Correction.rescaleStorePc stage chunk) := by
  rcases get_source hX he with ⟨_,hf⟩ | ⟨_,_,_,_,hCode,hFires⟩
  · cases hf
  rcases List.mem_append.mp (OpPcsFast.mem tensorStoreCode hCode (fires_tcSt_op hFires rfl))
    with hProb | hCorrection
  · obtain ⟨round,_,hR⟩ := List.mem_flatMap.mp hProb
    obtain ⟨q,_,hQ⟩ := List.mem_map.mp hR
    exact .inl ⟨round,q,hQ.symm⟩
  · obtain ⟨stage,_,hS⟩ := List.mem_flatMap.mp hCorrection
    obtain ⟨chunk,_,hQ⟩ := List.mem_map.mp hS
    exact .inr ⟨stage,chunk,hQ.symm⟩

end PTX.Kernels.TmlFa4Fwd.Thread
