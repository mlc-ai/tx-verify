-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotShfl
public import Lemmas.Kernel.FullVote

@[expose] public section

/-! # Votes

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/NotVote.lean`, the
analogue of `Lemmas/Flow/NotShfl.lean`): only `vote.sync` fires a vote event (`fires_vote_op`).
The warp collective source (`Frame.shfl_src`) asks that no lane of the warp makes a full-mask vote
before the shuffle's instance; a kernel whose code has no `vote.sync` meets it with this lemma and
one evaluated check of its code. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- A `vote.sync`. -/
def Op.isVote : Op → Bool
  | .warp ⟨.vote _ _, _, _, _, _⟩ => true
  | _ => false

/-- A template that does not vote. -/
def NotVote : Tmpl → Prop
  | .vote .. => False
  | .voteMode .. => False
  | _ => True

theorem ofExec_notVote {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotVote r) :
    NotVote (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notVote {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotVote m) :
    NotVote (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals first
      | exact h
      | (case arrive m' tx t count release scope => cases release <;> cases scope <;> exact h)
      | (case wait m' parity k acquire scope => cases acquire <;> cases scope <;> exact h)
  · exact h

theorem ruleTmpl_notVote {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotVote (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · rename_i r _
    cases r <;> simp only [localSregTmpl, sregTmpl, NotVote]
  · simp only [NotVote]

/-- Every instruction other than `vote.sync` fires no vote. -/
theorem eventTmpl_notVote {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : Op.isVote op = false) : NotVote (eventTmpl A L g t op) := by
  cases op
  case warp w =>
    rcases w with ⟨⟨⟩, _, _, _, _⟩ <;> first
      | (simp [Op.isVote] at hop; done)
      | (simp only [eventTmpl, warpTmpl, warpBarTmpl, electTmpl, voteTmpl, voteModeTmpl,
           reduxTmpl, matchTmpl, activemaskTmpl, shflTmpl]
         repeat' first
           | trivial
           | split)
  case int i => exact ruleTmpl_notVote (op := .int i)
  case move m => exact ruleTmpl_notVote (op := .move m)
  case cvt c => exact ruleTmpl_notVote (op := .cvt c)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notVote
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notVote)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        SetMaxNReg.tmpl, matrixTmpl, matrixMoveTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcTmpl, tcCommitTmpl, mmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notVote)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- **A vote event is fired by a `vote.sync`.** -/
theorem fires_vote_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} {m : Nat} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hs : voteWith m e = true) : Op.isVote op = true := by
  by_contra hq
  have hm := eventTmpl_notVote (A := A) (L := L) (g := g) (t := t) (by simpa using hq)
  obtain ⟨epc, ek⟩ := e
  cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotVote] at hm <;>
    simp only [Fires] at hf <;> cases ek <;> simp_all [voteWith, voteClass]

end
end PTX.Flow
