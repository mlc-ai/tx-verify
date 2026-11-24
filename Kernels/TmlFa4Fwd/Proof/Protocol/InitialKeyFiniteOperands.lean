-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.CacheOperandFinite
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialKeyPrefixReady
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialCacheOperandOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheOperandWriterOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheReleaseIssuer
import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedQkBank
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreLoadGeneration

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof PTX.TcMma PTX.AsyncCopy Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

/-- The actually acquired opening K packet supplies BF16 data, including zero fill. -/
theorem primingKeyOperandFinite {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (stage : Fin 2)
    {g index d : Nat} {step : Fin 8} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hQk : QkInstruction X (g,index) (initialQkBlock stage) step d op acc mask)
    {row k : Nat} (hr : row < 128) (hk : k < 16)
    {ops : MmaOperands} (hOps : X.async.mmaOperands (g,index) = some ops) :
    ∃ value, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok value := by
  have hInit := hQk.initialQueryFragment
  have hIssue := hQk.mmaIssue
  obtain ⟨wait,hPoll,hEarlier,hOrdinal⟩ := hInit.keyReadyInPrefix hp hX
  have hWarp : Prologue.warpIndex l g = 12 := (mmaIssueElection hp hX hIssue).1
  obtain ⟨done⟩ := completedForObservedIssuer hp hX hWarp
    (Thread.Mma.sameCacheReleaseIssuer hp hX hIssue) hPoll (actualEmptyGuardLower hp hX g 0)
  rw [hOrdinal] at done
  have hExact := hQk.operandsOfKey hp hX (hQk.initialKeyOperand hp hX stage)
  have hBytes (b : Fin 2) : op.byteLoc .b (qkByteIndex row k b.val) =
      (cacheOperand l g (initialQkBlock stage) step 0 .key).byteLoc .b
        (qkByteIndex row k b.val) := by rw [hExact]; rfl
  apply done.actualCacheOperandElement (use := 0) hp hX hFrame
    (initialQkBlock stage) step .key hr hk hIssue hEarlier hBytes hOps
  intro issue group j spec word hPub hPhase hMember hWord b
  dsimp only
  intro hLoc other a data hWrite hCover
  have hCopy := ((group.member j spec).mp hMember).2.2
  have hShape := actualCopyShape hX hCopy
  have hSource : spec.dst.Covers (spec.dst.loc.at (2*word+b.val)) := by
    have hb := b.isLt
    simp only [Acc.Covers,Loc.InRange,Loc.at,hShape.widthEq,true_and]
    exact ⟨by omega,by omega⟩
  rw [hEarlier.1] at hPub
  apply cacheOperandOrderOfCopyOrder hp hX hIssue hLoc _ hWrite hCover
  intro rival copy hRival hOverlap
  exact (initialKeyCopyCompetitors hp hX hInit hIssue hPub hPhase hMember
    hLoc hSource rival copy hRival hOverlap).elim .inl (.inr ∘ .inr)

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
