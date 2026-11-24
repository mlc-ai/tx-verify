-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedTerminalCredits
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedSoftmaxRetire
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityAck
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Correction Protocol.Statistics

def TerminalProducerRows (p : Params) (l : Launch) (X : Execution) (cta trips : Nat) : Prop :=
  ∀ h < l.threads, h/l.block = cta → ∀ w : Fin 8, warpIndex l h = w.val →
    Nonempty (Softmax.TerminalProducerRow p l X h w trips)

theorem TerminalProducerRows.publications {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {cta trips : Nat}
    (rows : TerminalProducerRows p l X cta trips) : TerminalRowPublications l X cta trips := by
  intro h hg hc w hw
  obtain ⟨row⟩ := rows h hg hc w hw
  obtain ⟨hs,hm,pub⟩ := row.published hp hMax hg hw.symm
  exact ⟨_,_,_,pub,row.ordinal,hs,hm,row.valid⟩

private theorem producerReleaseOfCredits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g trips : Nat}
    (hw : warpIndex l g < 8) (hCredits : TerminalCorrectionCredits l X (g/l.block)
      (Softmax.stageOf ⟨warpIndex l g,hw⟩) trips) :
    CtaBarrier.Released l.block (X.barriers (g/l.block)) (3+warpIndex l g) trips := by
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
  have hDone := observedCorrectionCreditReleases hp hX stage he hCredit
  change CtaBarDone l X (peer/l.block)
    (statsBarrierId l peer stage+16*(correctionBefore X (peer,j)).count (.statsCredit stage))
    at hDone
  change (correctionBefore X (peer,j)).count (.statsCredit stage) = trips at hCount
  rw [hBarrier,hPeerCta,hCount] at hDone
  unfold CtaBarDone at hDone
  have hn : 3+warpIndex l g < 16 := by omega
  rw [show (3+warpIndex l g+16*trips)%16 = 3+warpIndex l g by omega,
    show (3+warpIndex l g+16*trips)/16 = trips by omega] at hDone
  exact hDone

theorem repeatedSoftmaxArrivalsOfRows {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch issuer : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ g/l.block) (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (rows : TerminalProducerRows p l X (g/l.block)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1))
    (cta : issuer/l.block = g/l.block) (issues : Mma.TerminalOutputIssues l X issuer) :
    ∀ lane < 32, ∃ j, FinalAllocationArrival X (warpLane l g lane,j) .arrive := by
  let stage := Softmax.stageOf ⟨warpIndex l g,hw⟩
  obtain ⟨q,k⟩ := (frame X hMax.1).metadataProtected hp
  have deps := creditDependenciesOfCountedExitBound hp hMax.1 (countedExitCreditBound hp hMax.1 q k)
  have credit := repeatedTerminalCreditsOfRows hp hMax frame (NamedBar.cta_lt hg) hb lo hi
    multiple (TerminalProducerRows.publications hp hMax rows) cta issues stage
  obtain ⟨s,hs,phase⟩ := terminalStatisticsPhaseOfCredits hp hMax.1 deps hb lo hi stage credit
  apply Softmax.allocationArrivalsOfTerminalRows hp hMax q hg hw hb lo hi _
    (producerReleaseOfCredits hp hMax.1 hw credit)
  · exact ⟨s,hs,by rw [phase]; omega⟩
  · intro lane hl
    have same := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
    exact rows _ same.1.2.1 same.1.2.2.symm _ same.2.symm

end PTX.Kernels.TmlFa4Fwd.Progress
