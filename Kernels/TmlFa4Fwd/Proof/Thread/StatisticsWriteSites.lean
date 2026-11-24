-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites
public import Kernels.TmlFa4Fwd.Proof.SoftmaxStats
public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputStores
import Kernels.TmlFa4Fwd.Proof.GlobalWrites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow

noncomputable section

private def correctionSharedSites : List Nat :=
  (List.ofFn fun stage : Fin 2 =>
    List.ofFn fun box : Fin 4 =>
      List.ofFn fun chunk : Fin 8 => Correction.outputStorePc stage box chunk).flatten.flatten

private def statsSharedSites : List Nat := List.ofFn fun i : Fin 4 => (Softmax.statsStore i).pc

private theorem sharedSitesAudit :
    OpPcsFast kernel.code (fun op => storeSpace op == some .shared)
      (1909 :: statsSharedSites ++ correctionSharedSites) = true := by
  decide +kernel

/-- Only the allocator, softmax statistics and correction staging contain ordinary shared writes. -/
theorem sharedWriteSite {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {a : Acc} {bs : List Byte}
    (he : X.Writes i a bs) (hShared : a.loc.space = .shared) :
    X.get i = some ⟨1909, .wr a bs⟩ ∨
      (∃ site : Fin 4, X.get i = some ⟨(Softmax.statsStore site).pc, .wr a bs⟩) ∨
      ∃ (stage : Fin 2) (box : Fin 4) (chunk : Fin 8),
        X.get i = some ⟨Correction.outputStorePc stage box chunk, .wr a bs⟩ := by
  obtain ⟨pc, ins, he, hc, hSpace, _⟩ := sharedWriteInstruction hX he hShared
  have hPc := OpPcsFast.mem sharedSitesAudit hc (by simp only [hSpace, beq_self_eq_true])
  rcases List.mem_cons.mp hPc with rfl | hPc
  · exact .inl he
  rcases List.mem_append.mp hPc with hm | hm
  · obtain ⟨site, rfl⟩ := List.mem_ofFn.mp hm
    exact .inr (.inl ⟨site, he⟩)
  · obtain ⟨sticks, hs, hPc⟩ := List.mem_flatten.mp hm
    obtain ⟨stages, hStages, hSticks⟩ := List.mem_flatten.mp hs
    obtain ⟨stage, rfl⟩ := List.mem_ofFn.mp hStages
    obtain ⟨box, rfl⟩ := List.mem_ofFn.mp hSticks
    obtain ⟨chunk, rfl⟩ := List.mem_ofFn.mp hPc
    exact .inr (.inr ⟨stage, box, chunk, he⟩)

end
end PTX.Kernels.TmlFa4Fwd.Thread
