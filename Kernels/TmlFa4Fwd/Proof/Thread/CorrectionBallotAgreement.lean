-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBallotWindow
import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTrip
import Lemmas.Flow.VoteSeq

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow Epilogue Prologue

/-- A correction rescale vote with the recorded ballot word. -/
@[no_expose] def CorrectionRescaleBallot (X : Execution) (i : EvId) (word : BitVec 32) : Prop :=
  ∃ site input, (site = 8009 ∨ site = 8228) ∧
    X.get i = some ⟨site,.vote (2^32-1) input word⟩

/-- A decoded ballot observation at either correction rescale stage. -/
theorem CorrectionRescaleBallot.ofEvent {X : Execution} {i : EvId} {site : Nat}
    {input : Bool} {word : BitVec 32} (hs : site = 8009 ∨ site = 8228)
    (he : X.get i = some ⟨site,.vote (2^32-1) input word⟩) :
    CorrectionRescaleBallot X i word := ⟨site,input,hs,he⟩

/-- A rescale decision is shared by all observed peers of the ballot instance. -/
theorem CorrectionRescaleBallot.wordsAgree {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g h i j k : Nat} {left right : BitVec 32} (hWarp : SameWarp l g h)
    (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hUsedK : ∀ index < p.batch, ∀ byte < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*index)).at byte))
    (hLeft : CorrectionRescaleBallot X (g,i) left)
    (hRight : CorrectionRescaleBallot X (h,j) right)
    (hi : X.MaskK voteClass (g,i) (2^32-1) k)
    (hj : X.MaskK voteClass (h,j) (2^32-1) k) :
    left = right := by
  obtain ⟨site,a,hSite,he⟩ := hLeft
  obtain ⟨_,_,_,hf⟩ := hRight
  obtain ⟨part,hPart⟩ := FlashAttn4Fwd.Proof.ballot_instance hX he hi
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  apply ballot_eq hX.vote hBlock hWarp he hi hf hj hPart
  intro peer hPeer
  exact correctionRescaleBallotNoPeerExit hp hX hPeer hLo hHi hUsedK he hSite hi

end PTX.Kernels.TmlFa4Fwd.Thread
