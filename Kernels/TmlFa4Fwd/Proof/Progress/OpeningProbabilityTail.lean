-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityStores
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityTailCredit
import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningProbabilityTail
import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof Prologue Epilogue

/-- An active softmax warp issues an opening tail credit through its selected lane. -/
theorem openingProbabilityTailCreditOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hRole : warpIndex l g/4 = stage.val) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ peer j, SameWarp l g peer ∧
      Thread.Scores.ProbabilityCredit l X (peer,j) (g/l.block) stage 1 := by
  obtain ⟨c⟩ := openingProbabilityTailElectionOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  have hRole' {peer : Nat} (h : SameWarp l g peer) : warpIndex l peer/4 = stage.val := by
    simpa only [warpIndex,← h.2] using hRole
  obtain ⟨peer,hPeer,o,hLeader⟩ := c.selectedPeer hp hMax.1 hg (fun peer h =>
    openingProbabilityTailElectionOfMaximal hp hMax hFrame
      h.1.2.1 stage (hRole' h) hb (h.1.2.2 ▸ hLo) (h.1.2.2 ▸ hHi))
  obtain ⟨j,hCredit⟩ := o.creditOfMaximal hp hMax hPeer.1.2.1 (hRole' hPeer) hLeader
  exact ⟨peer,j,hPeer,hPeer.1.2.2.symm ▸ hCredit⟩

/-- Four elected softmax lanes advance each active CTA's opening P-tail object. -/
theorem openingProbabilityTailAdvancedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {cta batch : Nat} (hc : cta < l.grid) (stage : Fin 2)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads) :
    let log := X.objects (Thread.Scores.probabilityObject l cta stage 1)
    ∃ s, MBarrier.stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  classical
  let thread (w : Fin 4) := cta*l.block+(4*stage.val+w.val)*32
  have hAnchor (w : Fin 4) : thread w < l.threads ∧ thread w/l.block = cta ∧
      warpIndex l (thread w) = 4*stage.val+w.val := by
    let lane := (4*stage.val+w.val)*32
    have hStage := stage.isLt
    have hWarp := w.isLt
    have hl : lane < l.block := by rw [hp.block]; dsimp [lane]; omega
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta) hBlock hl
    change thread w/l.block = cta at hOwner
    change thread w%l.block = lane at hLocal
    refine ⟨NamedBar.cta_thread_lt hc hl,hOwner,?_⟩
    rw [warpIndex,hLocal]
    dsimp [lane]
    omega
  have hCredit (w : Fin 4) : ∃ i : EvId, SameWarp l (thread w) i.1 ∧
      Thread.Scores.ProbabilityCredit l X i cta stage 1 := by
    obtain ⟨hThread,hOwner,hAt⟩ := hAnchor w
    have hRole : warpIndex l (thread w)/4 = stage.val := by
      rw [hAt]
      have := w.isLt
      omega
    obtain ⟨peer,j,hPeer,hCredit⟩ := openingProbabilityTailCreditOfMaximal hp hMax hFrame
      hThread stage hRole hb (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi)
    exact ⟨(peer,j),hPeer,hOwner ▸ hCredit⟩
  choose credits hWarp hIssued using hCredit
  apply Protocol.Scores.tailProbabilityAdvancedOfCredits hp hMax.1 stage credits _ hIssued
  intro a b hEq
  have hSame : warpIndex l (thread a) = warpIndex l (thread b) :=
    (hWarp a).2.trans ((congrArg (fun i : EvId => warpIndex l i.1) hEq).trans (hWarp b).2.symm)
  rw [(hAnchor a).2.2,(hAnchor b).2.2] at hSame
  exact Fin.ext (by omega)

end PTX.Kernels.TmlFa4Fwd.Progress
