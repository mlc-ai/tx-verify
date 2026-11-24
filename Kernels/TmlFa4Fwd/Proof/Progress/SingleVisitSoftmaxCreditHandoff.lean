-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.SingleVisitSoftmaxRetire
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Correction Protocol.Statistics

/-- The matching correction credit certifies the softmax lane's actual final
named generation in a single-visit tile. -/
theorem singleVisitSoftmaxReleaseOfCorrectionCredits {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hOne : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hCredits : TerminalCorrectionCredits l X (g/l.block) (Softmax.stageOf ⟨warpIndex l g,hw⟩) 1) :
    SingleVisitSoftmaxRelease l X g := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  let stage := Softmax.stageOf warp
  let cta := g/l.block
  let lane : Fin 128 := ⟨32*(warp.val%4),by have := Nat.mod_lt warp.val (by decide : 0 < 4); omega⟩
  let peer := statsCreditLane l cta lane
  obtain ⟨j,e,he,hCredit,hCount⟩ := hCredits lane
  have hPeerCta : peer/l.block = cta := by
    dsimp only [peer,statsCreditLane]
    rw [hp.block]
    have := lane.isLt
    omega
  have hPeerWarp : warpIndex l peer = 8+warp.val%4 := by
    have hn : warp.val%4 < 4 := Nat.mod_lt _ (by decide)
    change (cta*l.block+256+32*(warp.val%4)) % l.block / 32 = _
    rw [hp.block]
    omega
  have hBarrier : statsBarrierId l peer stage = 3+warpIndex l g := by
    unfold statsBarrierId
    rw [hPeerWarp]
    change (8+warpIndex l g%4)%4+3+4*(warpIndex l g/4) = _
    omega
  have hDone := observedCorrectionCreditReleases hp hMax.1 stage he hCredit
  change CtaBarDone l X (peer/l.block)
    (statsBarrierId l peer stage+16*(correctionBefore X (peer,j)).count (.statsCredit stage))
    at hDone
  change (correctionBefore X (peer,j)).count (.statsCredit stage) = 1 at hCount
  rw [hBarrier,hPeerCta,hCount] at hDone
  unfold CtaBarDone at hDone
  have hn : 3+warpIndex l g < 16 := by omega
  rw [show (3+warpIndex l g+16*1)%16 = 3+warpIndex l g by omega,
    show (3+warpIndex l g+16*1)/16 = 1 by omega] at hDone
  obtain ⟨i,_,_,hFinal,hOrdinal,_,_⟩ :=
    singleVisitSoftmaxTerminalWordsOfMaximal hp hMax hFrame hg stage rfl hb hLo hHi
      (hOne.symm ▸ Nat.one_lt_two)
  intro k hPub _
  have hSame : k = i+2 := by
    rcases lt_trichotomy k (i+2) with hBefore | hEq | hAfter
    · exact (Scores.noPublicationAfterFinal hMax.1 hPub hBefore hFinal).elim
    · exact hEq
    · exact (Scores.noPublicationAfterFinal hMax.1 hFinal hAfter hPub).elim
  rw [Scores.notificationOrdinal hp hMax.1 hw,Scores.barrierOrdinal] at hOrdinal
  rw [hSame,hOrdinal]
  exact hDone

/-- A single-visit softmax warp makes its real final allocation arrivals after the
matching correction credits, including the named release witnessed by those credits. -/
theorem singleVisitSoftmaxAllocationOfCorrectionCredits {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hDeps : CreditAcquireDependencies l X)
    {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hOne : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hCredits : TerminalCorrectionCredits l X (g/l.block) (Softmax.stageOf ⟨warpIndex l g,hw⟩) 1) :
    ∀ lane < 32, ∃ j, FinalAllocationArrival X (warpLane l g lane,j) .arrive := by
  apply singleVisitSoftmaxAllocationArrivalsOfMaximal hp hMax hFrame hDeps hg hw hb hLo hHi
    hOne hCredits
  intro lane hl
  let thread := warpLane l g lane
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hWarp : warpIndex l g = warpIndex l thread := hSame.2
  have hw' : warpIndex l thread < 8 := hWarp ▸ hw
  have hCta : thread/l.block = g/l.block := hSame.1.2.2.symm
  have hStage : Softmax.stageOf ⟨warpIndex l thread,hw'⟩ =
      Softmax.stageOf ⟨warpIndex l g,hw⟩ := Fin.ext (congrArg (·/4) hWarp.symm)
  apply singleVisitSoftmaxReleaseOfCorrectionCredits (g := thread) hp hMax hFrame
    hSame.1.2.1 hw' hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi)
    (by rw [hCta]; exact hOne)
  rw [hCta,hStage]
  exact hCredits

end PTX.Kernels.TmlFa4Fwd.Progress
