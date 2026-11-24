-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsSync
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsCredit
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsFree
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsOFull
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsOFree
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsStaged
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsBar2
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsTcLd
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsTcSt
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsWaitSt
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsVotes
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsVoteN
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsTcColl
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataNz
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsData

@[expose] public section

/-! # `Counts` is a run invariant

It holds at the role's first state for a trace prefix with none of the counted events (the
prologue's), and every step of the machine keeps it (`counts_step`, from the step of each count). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The role's first state. -/
def start : D := { site := .setMaxReg }

/-- A trace prefix with none of the events `Counts` counts. -/
structure Quiet (L : Launch) (g : Nat) (es : List Event) : Prop where
  sync : ∀ st < 2, barEvents (kOf L g + 3 + 4 * st) 64 .sync es = 0
  credit : ∀ st < 2, arrivals (ownLoc L g (240 + 8 * st)) es = 0
  free : ∀ st < 2, arrivals (leadLoc L g (144 + 8 * st)) es = 0
  oFull : ∀ st < 2, okPolls (ownLoc L g (192 + 8 * st)) es = 0
  oFree : ∀ st < 2, okPolls (ownLoc L g (272 + 8 * st)) es = 0
  staged : ∀ st < 2, arrivals (ownLoc L g (256 + 8 * st)) es = 0
  bar2 : barEvents 2 416 .sync es = 0 ∧ barEvents 2 416 .arrive es = 0
  tcLd : ∀ st < 2, tcLdsIn (oLo L g st) (oHi L g st) es = 0
  tcSt : ∀ st < 2, tcStsIn (oLo L g st) (oHi L g st) es = 0
  waitSt : tcWaitSts es = 0
  vote : ∀ st < 2, es.countP (nzVote (votePc st)) = 0
  voteAll : ∀ st < 2, es.countP (isVoteAt (votePc st)) = 0
  voteAny : es.countP isVote = 0
  nzAny : es.countP isNzVote = 0
  tcAll : es.countP isTcColl = 0

theorem counts_start {L : Launch} {g : Nat} {es : List Event} (h : Quiet L g es) :
    Counts L g start es where
  sync st hst := by rw [h.sync st hst]; rfl
  credit st hst := by rw [h.credit st hst]; rfl
  free st hst := by rw [h.free st hst]; rfl
  oFull st hst := by rw [h.oFull st hst]; rfl
  oFree st hst := by rw [h.oFree st hst]; rfl
  staged st hst := by rw [h.staged st hst]; rfl
  bar2 := by rw [h.bar2.1, h.bar2.2]; exact ⟨rfl, rfl⟩
  tcLd st hst := by rw [h.tcLd st hst, h.vote st hst]; rfl
  tcSt st hst := by rw [h.tcSt st hst, h.vote st hst]; rfl
  waitSt := by rw [h.waitSt, h.vote 0 (by decide), h.vote 1 (by decide)]; rfl
  votes st hst := by rw [h.voteAll st hst]; rfl
  voteN := by rw [h.voteAny]; rfl
  tcColl := by rw [h.tcAll, h.nzAny]; rfl
  rsNz h := by simp [tcLack, start] at h
  finLd st j hf := by simp [finChunk, start] at hf
  finOk st j h el hs := by simp [start] at hs
  finSt st hf := by simp [finStat, finRecip, finChunk, start] at hf
  finA st hf := by simp [finRecip, finChunk, start] at hf
  wrote st j h el hd := by simp [wDone, start] at hd
  fenced st := ⟨fun hs => by simp [start] at hs, fun hs => by simp [start] at hs⟩
  rsLd st j hf := by simp [rsChunk, start] at hf
  rsSt st hf := by simp [rsSite, rsChunk, start] at hf
  rsWrote st j hd := by simp [rsStored, start] at hd
  rsVote st hf := by simp [rsAfterVote, start] at hf

/-- **`Counts` is kept by every step of the machine** whose event has the site's shape (and,
at a staging store, the store's footprint; at a vote, its predicate). -/
theorem counts_step {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event}
    (hT : 1 ≤ trips L) (hi : Inv L g d) (hev : Ev L g d e) (hw : WrAt L g d e)
    (hvote : VoteAt d e)
    (hn : next L g d e = some (some d')) (hc : Counts L g d es) :
    Counts L g d' (es ++ [e]) where
  sync st hst := step_sync hT hi hev hn st hst (hc.sync st hst)
  credit st hst := step_credit hT hi hev hn st hst (hc.credit st hst)
  free st hst := step_free hT hi hev hn st hst (hc.free st hst)
  oFull st hst := step_oFull hT hi hev hn st hst (hc.oFull st hst)
  oFree st hst := step_oFree hT hi hev hn st hst (hc.oFree st hst)
  staged st hst := step_staged hT hi hev hn st hst (hc.staged st hst)
  bar2 := step_bar2 hT hi hev hn hc.bar2
  tcLd st hst := step_tcLd hT hi hev hn st hst (hc.tcLd st hst)
  tcSt st hst := step_tcSt hT hi hev hn st hst (hc.tcSt st hst)
  waitSt := step_waitSt hT hi hev hn hc.waitSt
  votes st hst := step_votes hT hi hev hn st hst (hc.votes st hst)
  voteN := step_voteN hT hi hev hn hc.voteN
  tcColl := step_tcColl hT hi hev hn hc.tcColl
  rsNz := step_rsNz hev hn hc.rsNz
  finLd := step_finLd hev hn hc
  finOk := step_finOk hn hc
  finSt := step_finSt hev hn hc
  finA := step_finA hn hc
  wrote := step_wrote hw hev hn hc
  fenced := step_fenced hev hn hc
  rsLd := step_rsLd hev hn hc
  rsSt := step_rsSt hev hn hc
  rsWrote := step_rsWrote hev hn hc
  rsVote := step_rsVote hi hev hvote hn hc

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
