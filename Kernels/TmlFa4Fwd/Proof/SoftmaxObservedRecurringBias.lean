-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasReadGeneration
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitBiasWordOrder
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.InputActualSources
import Lemmas.Order.ReadLast
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.AsyncCopy PTX.MBarrier PTX.Flow PTX.Proof Prologue Thread Thread.Scores
open Thread.Loader Protocol.Bias

/-- Every performed Bias read has the completed half of its exact generation, and
all other writes to each of its bytes are ordered around that read. -/
theorem biasWordObservedOrder {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g read : Nat} {repeated : Bool} {i : Fin 16} {access : Acc} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X (g,read) repeated i access bytes) :
    ∃ (warp : Fin 8) (word : Fin 4) (wait : Nat) (tensor : EvId)
        (observation : TensorCopy.Observation),
      let stage := stageOf warp
      warp.val = warpIndex l g ∧
      access = biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val ∧
      wait < read ∧
      AcquiredBiasBox p l X stage g wait tensor (biasVectorHalf i) observation ∧
      biasTensorOrdinal l X stage (biasVectorHalf i) tensor =
        observedBarrierOrdinal X (g,read) (11+stage.val) ∧
      BiasWordOrder p l X stage repeated i word g read tensor := by
  obtain ⟨warp,word,hWarp,hStage,hAccess⟩ := biasVectorReadAccess hp hX hRead
  let stage := stageOf warp
  let half := biasVectorHalf i
  have hw : warpIndex l g < 8 := hWarp ▸ warp.isLt
  have hs : warpIndex l g/4 = stage.val := hStage.symm
  obtain ⟨wait,index,phase,record,hRecord,hId,hSuccess,hPhase,hLower,hBefore⟩ :=
    biasReadReadyObservation hp hX stage hRead hw hs
  have hExact := biasReadReadyPhase hp hX stage hRead hw hs
    hRecord hId hSuccess hPhase hLower hBefore
  obtain ⟨tensor,spec,hOwner,hSubbox,hOrdinal,hNotice⟩ :=
    biasReadyObservedHalfOwner hp hX stage half hRecord hSuccess hPhase
  rw [hId] at hNotice
  have hObserved := biasTensorObservedAtCTA hX hNotice
  obtain ⟨observation,_,hObservation,hIssue,_,_⟩ := hObserved.tensor
  have hSpec : observation.spec = spec := by
    obtain ⟨_,hGet⟩ := hIssue
    obtain ⟨_,hActual⟩ := hSubbox.1
    exact (Kind.tensorIssue.inj (congrArg Event.kind
      (Option.some.inj (hGet.symm.trans hActual)))).2
  have hBox : AcquiredBiasBox p l X stage g wait tensor half observation := by
    obtain ⟨hSource,hTarget,hDestination,hDesc,hRows,hCluster,hGroup⟩ := hSubbox
    rw [hOwner] at hTarget hDestination
    refine ⟨hObserved,hObservation,hSpec.symm ▸ hSource,hOwner,hSpec.symm ▸ hTarget,?_,
      hSpec.symm ▸ hDesc,hSpec.symm ▸ hRows,hSpec.symm ▸ hCluster,hSpec.symm ▸ hGroup⟩
    rw [hSpec,hDestination]
    simp only [biasBoxStart,Nat.add_assoc]
  refine ⟨warp,word,wait,tensor,observation,hWarp,hAccess,hBefore.2.1,hBox,
    hOrdinal.trans hExact,?_⟩
  apply biasWordOrderForRound hp hX repeated i word hBox
  intro byte writer other x y k loc hOther hOtherOwner hLocation hRange hLoc hCover
  obtain ⟨part,hPart,hTarget⟩ := hCover
  rcases Nat.lt_trichotomy (biasTensorOrdinal l X stage half writer) phase with
    hOlder | hSame | hLater
  · exact .inr (.inl (hPart.symm ▸ biasModelWriteBeforeReuse hp hX hOther hSubbox
      (hOtherOwner.trans hOwner.symm) (hOrdinal.symm ▸ hOlder) hLoc hTarget))
  · exact .inl (biasTensorOrdinalInjective hp hX hOther hSubbox
      (hOtherOwner.trans hOwner.symm) (hSame.trans hOrdinal.symm))
  · exact .inr (.inr (biasReadBeforeLaterWrite hp hX stage half hRead hw hs hOther hOtherOwner
      (hExact ▸ hLater) hRange.1 hRange.2.1 hLoc))

end PTX.Kernels.TmlFa4Fwd.Softmax
