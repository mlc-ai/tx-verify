-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbability
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityElection
import Lemmas.Step.WarpAppend

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX

private theorem probabilityPeers {l : Launch} {X : Execution} {g ordinal : Nat}
    (hBlock : l.block%32 = 0) (hg : g < l.threads)
    (hReach : ∀ peer, SameWarp l g peer → ∃ k, X.TcK (peer,k) ordinal) :
    ∀ peer ∈ warpLanes l g, ∃ k, X.TcK (peer,k) ordinal := by
  intro peer hPeer
  obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hPeer
  have hl : lane < 32 := (List.mem_range.mp hLane).trans_le (Nat.min_le_left ..)
  exact hReach _ (Step.sameWarp_lane hBlock hg hl).1

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (stage : Fin 2) (hRole : Prologue.warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp hMax hFrame hg stage hRole hb hLo hHi

/-- Every active softmax lane has recorded each of the three opening main-packet stores. -/
theorem openingProbabilityStoreCursorOfMaximal (quarter : Fin 3) :
    Nonempty (Softmax.OpeningProbabilityStoreCursor p l X g stage quarter) := by
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSelf : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  have wait (peer : Nat) (hPeer : SameWarp l g peer) :
      Nonempty (Softmax.OpeningProbabilityWaitCursor p l X peer stage) := by
    have hr : Prologue.warpIndex l peer/4 = stage.val := by
      simpa only [Prologue.warpIndex,← hPeer.2] using hRole
    exact openingProbabilityWaitCursorOfMaximal hp hMax hFrame hPeer.1.2.1 stage hr hb
      (hPeer.1.2.2 ▸ hLo) (hPeer.1.2.2 ▸ hHi)
  have first (peer : Nat) (hPeer : SameWarp l g peer) :
      Nonempty (Softmax.OpeningProbabilityStoreCursor p l X peer stage 0) := by
    obtain ⟨c⟩ := wait peer hPeer
    apply c.firstStoreOfMaximal hp hMax hPeer.1.2.1
    apply probabilityPeers hBlock hPeer.1.2.1
    intro lane hLane
    obtain ⟨other⟩ := wait lane (Step.sameWarp_trans hPeer hLane)
    exact ⟨_,other.ordinal⟩
  have second (peer : Nat) (hPeer : SameWarp l g peer) :
      Nonempty (Softmax.OpeningProbabilityStoreCursor p l X peer stage 1) := by
    obtain ⟨c⟩ := first peer hPeer
    apply c.nextStoreOfMaximal hp hMax hPeer.1.2.1 (q := 0)
    apply probabilityPeers hBlock hPeer.1.2.1
    intro lane hLane
    obtain ⟨other⟩ := first lane (Step.sameWarp_trans hPeer hLane)
    exact ⟨_,other.ordinal⟩
  fin_cases quarter
  · exact first g hSelf
  · exact second g hSelf
  · obtain ⟨c⟩ := second g hSelf
    apply c.nextStoreOfMaximal hp hMax hg (q := 1)
    apply probabilityPeers hBlock hg
    intro peer hPeer
    obtain ⟨other⟩ := second peer hPeer
    exact ⟨_,other.ordinal⟩

/-- Every active softmax lane reached the first main probability packet wait. -/
theorem openingProbabilityStoreWaitCursorOfMaximal :
    Nonempty (Softmax.OpeningProbabilityStoreWaitCursor p l X g stage) := by
  obtain ⟨c⟩ := openingProbabilityStoreCursorOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi 2
  apply c.waitOfMaximal hp hMax hg
  apply probabilityPeers (by rw [hp.block]) hg
  intro peer hPeer
  have hr : Prologue.warpIndex l peer/4 = stage.val := by
    simpa only [Prologue.warpIndex,← hPeer.2] using hRole
  obtain ⟨other⟩ := openingProbabilityStoreCursorOfMaximal hp hMax hFrame hPeer.1.2.1 stage hr hb
    (hPeer.1.2.2 ▸ hLo) (hPeer.1.2.2 ▸ hHi) 2
  exact ⟨_,other.ordinal⟩

/-- Every active softmax lane contributes its opening main probability credit to its stage. -/
theorem openingProbabilityCreditCursorOfMaximal :
    Nonempty (Softmax.OpeningProbabilityCreditCursor p l X g stage) := by
  obtain ⟨c⟩ := openingProbabilityStoreWaitCursorOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  have hPeers : ∀ peer ∈ warpLanes l g, ∃ pos, X.TcK (peer,pos) 8 := by
    apply probabilityPeers (by rw [hp.block]) hg
    intro peer hPeer
    have hr : Prologue.warpIndex l peer/4 = stage.val := by
      simpa only [Prologue.warpIndex,← hPeer.2] using hRole
    obtain ⟨other⟩ := openingProbabilityStoreWaitCursorOfMaximal hp hMax hFrame
      hPeer.1.2.1 stage hr hb
      (hPeer.1.2.2 ▸ hLo) (hPeer.1.2.2 ▸ hHi)
    exact ⟨_,other.ordinal⟩
  obtain ⟨next,_⟩ := c.creditCursorOfMaximal hp hMax hg hPeers
  exact ⟨next⟩

/-- Every active softmax lane contributes its opening main probability credit to its stage. -/
theorem openingProbabilityCreditOfMaximal :
    ∃ j, Thread.Scores.ProbabilityCredit l X (g,j) (g/l.block) stage 0 := by
  obtain ⟨c⟩ := openingProbabilityCreditCursorOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  exact ⟨_,c.credited⟩

/-- The fourth opening probability store is recorded in every active softmax lane. -/
theorem openingProbabilityTailStoreOfMaximal :
    Nonempty (Softmax.OpeningProbabilityTailStore p l X g stage) := by
  obtain ⟨c⟩ := openingProbabilityCreditCursorOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  exact c.tailStoreOfMaximal hp hMax hg

/-- The four opening probability stores lead to the real tail store wait. -/
theorem openingProbabilityTailWaitOfMaximal :
    Nonempty (Softmax.OpeningProbabilityTailWait p l X g stage) := by
  obtain ⟨c⟩ := openingProbabilityTailStoreOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  apply c.waitOfMaximal hp hMax hg
  apply probabilityPeers (by rw [hp.block]) hg
  intro peer hPeer
  have hr : Prologue.warpIndex l peer/4 = stage.val := by
    simpa only [Prologue.warpIndex,← hPeer.2] using hRole
  obtain ⟨other⟩ := openingProbabilityTailStoreOfMaximal hp hMax hFrame
    hPeer.1.2.1 stage hr hb (hPeer.1.2.2 ▸ hLo) (hPeer.1.2.2 ▸ hHi)
  exact ⟨_,other.ordinal⟩

/-- Each active softmax warp reaches its first probability tail rendezvous. -/
theorem openingProbabilityTailWarpBarOfMaximal :
    Nonempty (Softmax.OpeningProbabilityWarpBar p l X g stage) := by
  obtain ⟨c⟩ := openingProbabilityTailWaitOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  apply c.warpBarOfMaximal hp hMax hg
  intro peer hPeer
  have hr : Prologue.warpIndex l peer/4 = stage.val := by
    simpa only [Prologue.warpIndex,← hPeer.2] using hRole
  exact openingProbabilityTailWaitOfMaximal hp hMax hFrame
    hPeer.1.2.1 stage hr hb (hPeer.1.2.2 ▸ hLo) (hPeer.1.2.2 ▸ hHi)

/-- Each active softmax warp reaches its actual election for the opening tail release. -/
theorem openingProbabilityTailElectionOfMaximal :
    Nonempty (Softmax.OpeningProbabilityElection p l X g stage) := by
  obtain ⟨c⟩ := openingProbabilityTailWarpBarOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  apply c.electionOfMaximal hp hMax hg
  intro peer hPeer
  have hr : Prologue.warpIndex l peer/4 = stage.val := by
    simpa only [Prologue.warpIndex,← hPeer.2] using hRole
  exact openingProbabilityTailWarpBarOfMaximal hp hMax hFrame
    hPeer.1.2.1 stage hr hb (hPeer.1.2.2 ▸ hLo) (hPeer.1.2.2 ▸ hHi)

end PTX.Kernels.TmlFa4Fwd.Progress
