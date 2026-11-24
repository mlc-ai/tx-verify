-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.SingleVisitTailProbability
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstProbabilityHandoff
import Kernels.TmlFa4Fwd.Proof.Thread.InitialProbabilityAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Proof PTX.TcMma PTX.AsyncCopy Prologue Epilogue Softmax Thread Thread.Scores

/-- The actual first tail acquire orders the observed warp's last P store before
either final PV fragment that reads the tail packet. -/
theorem singleVisitTailProbabilityStoreDoneBeforePv {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {warp : Fin 8} {g j batch head row cap past : Nat}
    (hg : g < l.threads) (hw : warp.val = warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRound : FirstRoundProgress p l X warp g j batch head row 1 cap past)
    {i : EvId} {frag : Fin 8} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hPv : PvInstruction X i (firstPvBlock false (stageOf warp)) frag d op acc mask)
    (hFrag : 6 ≤ frag.val) (hCta : g/l.block = i.1/l.block) :
    StoreDoneBefore l X (g,j+1+probabilityTraceIndex (3 : Fin 4)) i := by
  let stage := stageOf warp
  let slot : Fin 4 := ⟨warp.val % 4,Nat.mod_lt _ (by decide)⟩
  obtain ⟨later,hLater⟩ := hPv.tailProbabilityAcquire hp hX stage 1 (.inr hFrag)
  obtain ⟨w,k,poll,hPoll,hPollId,hAction,hSuccess,⟨e,scope,he,hKind⟩,hResume⟩ :=
    firstProbabilityAcquireRecord hp hX hLater
  rw [← hCta] at hPoll hKind
  obtain ⟨credit,hCredit,hWarp,hObserved⟩ := singleVisitTailCreditOfWarp hp hX hDone hFrame
    hb hLo hHi hTrip stage slot hPoll hAction hSuccess
  rw [hPollId] at hObserved
  have hCreditEvent := hCredit
  obtain ⟨_,hArrival⟩ := hCreditEvent
  have hIssuer := event_thread_lt hX hArrival
  have hMma : i.1 < l.threads := event_thread_lt hX (e := i)
    (List.getElem?_eq_getElem hResume.1.2.2)
  have hCreditCta := (probabilityCreditRole hp hX stage 1 hCredit).1
  have hSame : SameWarp l g credit.1 := by
    refine ⟨⟨hg,hIssuer,hCreditCta.symm⟩,?_⟩
    change warpIndex l g = warpIndex l credit.1
    rw [← hw,hWarp]
    change warp.val = 4 * (warp.val/4) + warp.val%4
    omega
  exact firstTailProbabilityStoreDoneBeforePv hp hX hRound hSame
    ⟨hIssuer,hMma,hCreditCta.trans hCta⟩ hResume hCredit
    (probabilityAcquireObserves he hKind hObserved)

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
