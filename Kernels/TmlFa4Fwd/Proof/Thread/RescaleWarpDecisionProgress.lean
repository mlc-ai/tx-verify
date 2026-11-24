-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionStatistics
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleChunkInputs
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalReadProgress
public import Kernels.TmlFa4Fwd.Proof.Protocol.RescalePublicationValues
public import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
public import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleBranch
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Step.WarpVoteProgress
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Thread.Correction

/-- A reached lane holds its actual coefficient immediately before the full-warp vote. -/
structure RescaleBallotLane (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (ordinal : Nat) where
  frame : List (Nat × Value)
  coefficient : Value
  alpha : ℝ
  valid : RescaleFactorWord coefficient alpha
  cursor : OpeningTripCursor l X g (statsPc stage .alpha+1)
    ((statsReg stage .alpha,coefficient)::frame)
  vote : ((X.tr g).take cursor.pos).countP isFullWarpVote = ordinal
  fresh : ∀ pair ∈ frame, pair.1 ≠ rescalePredReg stage ∧ pair.1 ≠ rescaleVoteReg stage ∧
    pair.1 ≠ maskZeroReg stage

/-- State after the opening rescale ballot, including the physical row frame
needed by the selected update or skip path. -/
structure FirstRescaleDecisionReached (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) where
  index : Nat
  word : BitVec 32
  coefficient : Value
  alpha : ℝ
  valid : RescaleFactorWord coefficient alpha
  voted : X.get (g,index) = some ⟨statsPc 0 .alpha+2,
    .vote (2^32-1) (decide (alpha < 1)) word⟩
  tensor : ((X.tr g).take (index+1)).countP isTcColl = 0
  mask : X.MaskK voteClass (g,index) (2^32-1) 1
  cursor : OpeningTripCursor l X g (if word = 0 then rescaleSkipPc 0 else rescaleLoadPc 0 0)
    ((statsReg 0 .alpha,coefficient)::correctionRescaleSetupFacts p l g batch (laneOf l g))
  position : cursor.pos = index+1

/-- Once all warp lanes reach the same rescale vote generation, each lane
records the collective result and takes the matching skip or update branch. -/
theorem rescaleDecisionOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g ordinal : Nat} (hg : g < l.threads) (stage : Fin 2)
    (lanes : ∀ h, SameWarp l g h → RescaleBallotLane l X h stage ordinal) :
    let c := lanes g ⟨⟨hg,hg,rfl⟩,rfl⟩
    ∃ word, X.get (g,c.cursor.pos) = some ⟨statsPc stage .alpha+2,
        .vote (2^32-1) (decide (c.alpha < 1)) word⟩ ∧
      X.MaskK voteClass (g,c.cursor.pos) (2^32-1) ordinal ∧
      ∃ nextC : OpeningTripCursor l X g (if word = 0 then rescaleSkipPc stage
          else rescaleLoadPc stage 0) ((statsReg stage .alpha,c.coefficient)::c.frame),
        nextC.pos = c.cursor.pos+1 := by
  classical
  let index (h : Nat) := if hh : SameWarp l g h then (lanes h hh).cursor.pos else 0
  let hit (h : Nat) := if hh : SameWarp l g h then decide ((lanes h hh).alpha < 1) else false
  have hNext (h : Nat) (hh : SameWarp l g h) :=
    rescaleBallotNext (g := h) hp stage (lanes h hh).cursor.checkpoint
      (fun pair hm => ⟨((lanes h hh).fresh pair hm).1,((lanes h hh).fresh pair hm).2.1⟩)
      (lanes h hh).valid.value
  have hSelf : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  let c := lanes g hSelf
  obtain ⟨word,he,hMask⟩ := Step.ballot_occurs_of_maximal hMax (by rw [hp.block]) hg
    (pc := statsPc stage .alpha+2) (ordinal := ordinal) index hit
    (fun h _ => (PTX.electMember_full l h).2) (fun h hh => .inl
      (List.ne_nil_of_length_pos
        ((lanes h hh).cursor.positive.trans_le (lanes h hh).cursor.bounded)))
    (fun h hh => by
      let a := lanes h hh
      obtain ⟨s,k,hPc,hn,_⟩ := hNext h hh
      simp only [index,hit,dite_eq_left hh]
      exact ⟨a.cursor.before,s,a.cursor.ending,k,a.cursor.bounded,a.vote,a.cursor.released,
        hPc,a.cursor.recorded,a.cursor.remaining,⟨a.cursor.localSteps.trans hn.1,hn.2⟩⟩)
    (fun _ h => Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
      (noNewRead_appendLanes h))
  simp only [index,hit,dite_eq_left hSelf] at he hMask
  obtain ⟨s,k,hPc,hn,hReturn⟩ := hNext g hSelf
  let nextVote : Next kernel Assumptions.all l g c.cursor.before s
      (.vote (2^32-1) (decide (c.alpha < 1)) k) := ⟨c.cursor.localSteps.trans hn.1,hn.2⟩
  have hLt : c.cursor.pos < (X.tr g).length := len_of_get he
  obtain ⟨actual,hActual,_,hTail⟩ := nextVote.ballot_at_nonempty c.cursor.remaining
    (fun h => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp h)) c.vote
  rw [hPc] at hActual
  have hEq := Option.some.inj (hActual.symm.trans he)
  have hWord : actual = word := (Kind.vote.inj (Event.mk.inj hEq).2).2.2
  subst actual
  have hs := hReturn word
  have hpref : Run kernel Assumptions.all l g {} ((X.tr g).take (c.cursor.pos+1))
      (some (k word)) := by
    rw [List.take_succ_eq_append_getElem hLt,(List.getElem?_eq_some_iff.mp he).2]
    exact c.cursor.recorded.snoc nextVote.1 ⟨_,nextVote.2,word,by rw [hPc]; exact hEq.symm,rfl⟩
  obtain ⟨u,hu,hSteps⟩ := rescaleDecisionSteps (g := g) stage word (hs.mono hs.2.2.2.2.2)
    hs.2.2.2.2.1 (by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | h
      · fin_cases stage <;> dsimp only <;> decide
      · exact (c.fresh pair h).2.2)
  exact ⟨word,he,hMask,⟨c.cursor.pos+1,k word,u,c.cursor.ending,Nat.succ_pos _,hLt,
    releasedIfLast he (by intro h; cases h),hu,hpref,hTail,hSteps⟩,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Correction
