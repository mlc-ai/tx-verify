-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ScoreLoadSources
import Kernels.TmlFa4Fwd.Proof.Thread.ScoreActive
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.TcMma Prologue Softmax Protocol.Scores

/-- The score acquire of a recorded probability store came from a scheduled CTA.
The store also identifies that softmax lane's physical stage. -/
theorem probabilityStoreScheduled {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (round : Softmax.Round) (q : Fin 4)
    {i : EvId} {address : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get i = some ⟨probabilityPc round q,.tc (.st address vals shape)⟩) :
    i.1/l.block < tilePrefix p p.batch*p.heads ∧
      ∃ stage : Fin 2, warpIndex l i.1/4 = stage.val := by
  obtain ⟨w,hWarp,rfl,hLen,rfl⟩ := probabilityStoreAddress hp hX round q he
  let stage := stageOf w
  have hStage : warpIndex l i.1/4 = stage.val := by change _ = w.val/4; rw [hWarp]
  let addr := probabilityAddress l i.1 stage q
  let cell := tcDataCell l i.1 .s32x32b addr 0
  have hStore : StoreCell l X i cell := ⟨addr,vals,.s32x32b,0,⟨_,he⟩,by rw [hLen]; decide,rfl⟩
  have hCol := probabilityColumn_range stage
  have hLimit := scoreColumn_range stage
  have hQ := q.isLt
  have hAddr : probabilityColumn stage+16*q.val < 512 := by omega
  have hGeom : TensorStoreFootprint l i cell (.probability stage) := by
    dsimp only [cell,addr,probabilityAddress]
    rw [tcDataCell_warp32 l i.1 0 hAddr]
    refine ⟨rfl,?_,?_,?_,?_⟩
    · change i.1%l.block/32%4*32+i.1%l.block%32 = i.1%l.block%128
      omega
    · change probabilityColumn stage ≤ probabilityColumn stage+16*q.val+0
      omega
    · change probabilityColumn stage+16*q.val+0 < probabilityColumn stage+64
      omega
    · change i.1%l.block/128 = stage.val
      unfold warpIndex at hStage
      omega
  have hJoint : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  obtain ⟨seen,_⟩ := probabilityStoreObservesLatestScore hp hX hJoint stage hStore hGeom
  have hCta : seen.commit.1/l.block = i.1/l.block :=
    (scoreCommitActor hp hX seen.score).1
  have hActive := scoreCommitActive hp hX hCuQ (hCta.symm ▸ seen.score)
  exact ⟨hCta ▸ hActive,stage,hStage⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
