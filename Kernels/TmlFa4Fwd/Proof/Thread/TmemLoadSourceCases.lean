-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemFinalLoadSources
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleLoadSources
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreLoadSources
import Kernels.TmlFa4Fwd.Proof.Thread.TensorLoadSites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.TcMma

/-- Every observed Tensor Memory load register belongs to one of the three role operations. -/
theorem loadCellCases {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load : EvId} {j : Nat} {cell : Cell} (hLoad : LoadCell l X load j cell) :
    (∃ stage, Scores.ScoreLoadCell l X load cell stage) ∨
    (∃ stage, Correction.RescaleLoadCell l X load cell stage) ∨
    ∃ stage, Correction.FinalizationLoadCell l X load cell stage := by
  obtain ⟨address,words,shape,⟨site,he⟩,hJ,hC⟩ := hLoad
  rcases tensorLoadSite hX he with
    ⟨round,quarter,rfl⟩ | ⟨stage,chunk,rfl⟩ | ⟨stage,chunk,rfl⟩
  · exact .inl (Scores.ScoreLoadCell.ofDecoded hp hX round quarter he hJ hC)
  · exact .inr (.inl ⟨stage,Correction.RescaleLoadCell.ofDecoded chunk he hJ hC⟩)
  · exact .inr (.inr ⟨stage,Correction.FinalizationLoadCell.ofDecoded chunk he hJ hC⟩)

end PTX.Kernels.TmlFa4Fwd.Thread
