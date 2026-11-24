-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.SingleVisitEarlyProbability
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstProbabilityHandoff
import Kernels.TmlFa4Fwd.Proof.Thread.InitialProbabilityAcquire
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Proof PTX.TcMma PTX.AsyncCopy Prologue Epilogue Softmax Thread Thread.Scores

/-- Every early P store of a one-visit lane is complete before its consumer's PV issue.
The initial acquire observes that lane's release among its actual joint-packet credits. -/
theorem singleVisitEarlyProbabilityStoreDoneBeforePv {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {warp : Fin 8} {g j batch head row cap past : Nat}
    (hg : g < l.threads) (hw : warpIndex l g < 8)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRound : FirstRoundProgress p l X warp g j batch head row 1 cap past)
    {i : EvId} {frag : Fin 8} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hPv : PvInstruction X i (firstPvBlock false (stageOf warp)) frag d op acc mask)
    (hCta : g/l.block = i.1/l.block) (q : Fin 4) (hQuarter : q.val < 3) :
    StoreDoneBefore l X (g,j+1+probabilityTraceIndex q) i := by
  let stage := stageOf warp
  let loc := probabilityObject l (g/l.block) stage 0
  have hGuard : CorrectionJointGuards l X :=
    correctionJointGuardsOfCuQ hp hX (hFrame.metadataProtected hp).1
  obtain ⟨_,_,_,hCredit⟩ := firstProbabilityStoresBeforeCredit (X := X) hRound q hQuarter
  obtain ⟨creditIndex,credit,hRecord,hCreditId,hUpdate⟩ := probabilityCreditRecord hX hCredit
  have hOrdinal := singleVisitSoftmaxCreditOrdinalZero hp hX hDone hFrame
    hb hLo hHi hTrip stage 0 hw hCredit
  obtain ⟨hClean,hPhase⟩ := jointProbabilityCreditPhaseExact hp hX hGuard stage
    hRecord hUpdate hCreditId
  rw [hOrdinal] at hPhase
  obtain ⟨later,hLater⟩ := hPv.tailProbabilityAcquire hp hX stage 0 (.inl rfl)
  obtain ⟨w,k,poll,hPoll,hPollId,hAction,hSuccess,⟨e,scope,he,hKind⟩,hResume⟩ :=
    firstProbabilityAcquireRecord hp hX hLater
  rw [← hCta] at hPoll hKind
  have hSeen := singleVisitEarlyObservedPhaseZero hp hX hDone hFrame hGuard
    hb hLo hHi hTrip stage hPoll hAction hSuccess
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hObserve := hX.observed_of_phase hNo hRecord hClean hUpdate hPoll hSuccess hPhase hSeen
  rw [hCreditId,hPollId] at hObserve
  have hMma : i.1 < l.threads := event_thread_lt hX (e := i)
    (List.getElem?_eq_getElem hResume.1.2.2)
  exact firstProbabilityStoresDoneBeforeObservedPv hRound q hQuarter ⟨hg,hMma,hCta⟩
    hResume (probabilityAcquireObserves he hKind hObserve)

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
