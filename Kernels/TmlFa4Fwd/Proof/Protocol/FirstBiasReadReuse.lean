-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.FirstBiasReadReuse
public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasReturnObservation
import Lemmas.Protocol.StagingHandoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Proof PTX.AsyncCopy Thread.Scores Thread.Loader Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A later Bias TMA cannot replace a first-round Bias word. The actual proxy fence
orders the read through the stage rendezvous and the loader's reuse acquire. -/
theorem firstBiasReadBeforeReusedBoxInPrefix (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g read wait : Nat} {stage half : Fin 2}
    (hWord : FirstBiasWordRead X (g,read)) (hWait : FirstBiasAcquire l X g wait stage)
    (hWarp : warpIndex l g < 8) {tensor : EvId} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X tensor stage half spec) (hSame : tensor.1/l.block = g/l.block)
    (hReused : 0 < biasTensorOrdinal l X stage half tensor) {part : Part} {loc : Loc}
    (hShared : loc.space = .shared) (hLocal : loc.cta = g/l.block)
    (hCover : AsyncCovers X tensor part loc) :
    modelCausality l X loc (.thread (g,read)) (.async tensor part) := by
  obtain ⟨loader,index⟩ := tensor
  obtain ⟨empty,k,hEmpty,hOwner,_,_,hObserve,hResume⟩ :=
    biasTensorReuseOfConsumerWarp hp hX (0 : Fin 4) hIssue hReused
  obtain ⟨fence,hFence,hg,hBefore,hAfter⟩ :=
    hWord.fenceBeforeReturnInPrefix hp hX hWait hWarp (hSame ▸ hEmpty)
  have hWaited := reuseWaitObservesAtCTA hp hX hIssue hEmpty hObserve
  obtain ⟨_,hT⟩ := hIssue.1
  have hEmptyRecord := hEmpty
  obtain ⟨_,hE⟩ := hEmptyRecord
  have hLoader := event_thread_lt hX hT
  have hEmptyThread := event_thread_lt hX hE
  have hScope : ScopesMeet l .cta empty.1 .cta loader :=
    ⟨⟨hEmptyThread,hLoader,hOwner⟩,⟨hLoader,hEmptyThread,hOwner.symm⟩⟩
  have hReuse := Staging.baseCausality_of_handoff (e := empty) (f := (loader,index))
    ⟨0,1,hEmpty⟩ hWaited hScope ⟨rfl,le_rfl⟩ hResume.1
  have hCluster : SameCluster l g loader :=
    ⟨hg,hLoader,congrArg l.clusterOfCta hSame.symm⟩
  exact ⟨hCover,.inl ⟨(g,fence),_,_,hFence,hg,⟨hShared,hLocal⟩,hCluster,hBefore,
    hAfter.trans hReuse⟩⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
