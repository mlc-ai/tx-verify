-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveSites
public import Lemmas.Flow.Hooks
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch
import Lemmas.Flow.ElectMask
import Lemmas.Flow.Final
import Lemmas.Flow.OpPcsFast

public section

/-! # The actual softmax reference vote in a followed thread -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0VoteSites

open PTX PTX.Flow

/-- A template without a ballot or predicate vote. -/
private def NotVote : Tmpl → Prop
  | .vote .. | .voteMode .. => False
  | _ => True

/-- Check the frozen warp instruction for either form of vote. -/
private def voteOp : Op → Bool
  | .warp ⟨.vote .., _, _, _, _⟩ => true
  | _ => false

private theorem ofExec_notVote {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotVote r) :
    NotVote (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

private theorem widen_notVote {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotVote m) :
    NotVote (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals first
      | exact h
      | (case arrive m' tx t count release scope => cases release <;> cases scope <;> exact h)
      | (case wait m' parity k acquire scope => cases acquire <;> cases scope <;> exact h)
  · exact h

/-- A non-vote operation has no ballot or predicate-vote outcome. -/
private theorem eventTmpl_notVote {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op}
    (hop : voteOp op = false) : NotVote (eventTmpl A L g t op) := by
  cases op
  case warp w =>
    simp only [eventTmpl]
    rcases w with ⟨kind, ty, dsts, srcs, mask⟩
    unfold warpTmpl
    split
    · simp only [shflTmpl]; repeat' first | trivial | split
    · simp_all [voteOp]
    · simp_all [voteOp]
    · simp only [reduxTmpl]; repeat' first | trivial | split
    · simp only [matchTmpl]; repeat' first | trivial | split
    · trivial
    · simp only [electTmpl]; repeat' first | trivial | split
    · simp only [warpBarTmpl]; repeat' first | trivial | split
    · trivial
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine Flow.tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
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
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notVote)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A template without a vote does not produce a vote-class event. -/
private theorem fires_notVote {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (hm : NotVote m) (hf : Fires pc m e o) : voteClass e.kind = none := by
  cases m <;> simp only [NotVote] at hm <;> simp only [Fires] at hf
  all_goals aesop

set_option maxRecDepth 100000 in
private theorem vote_cover : OpPcsFast kernel.code voteOp [578] = true := by
  decide +kernel

local macro "exclude_vote " h:ident : tactic => `(tactic| (
  exfalso
  revert $h
  first
  | decide
  | rename_i a; revert a; decide
  | rename_i a b; revert a b; decide
  | rename_i a b c; revert a b c; decide
  ))

variable {P : Params} {L : Launch} {g : Nat}

private theorem vote_site {d : Machine.ThreadD} (h : (Machine.code P L g).pc d = 578) :
    ∃ q, d = .wg0 q ∧ q.site = .rescaleVote := by
  cases d
  case prologue s =>
    change s.pc = 578 at h
    cases s <;> exclude_vote h
  case wg0 d =>
    change d.site.pc = 578 at h
    refine ⟨d, rfl, ?_⟩
    generalize d.site = s at h ⊢
    clear d
    cases s <;> first | rfl | exclude_vote h
  case mma d =>
    exfalso
    change d.site.pc = 578 at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_vote h
  case tma d =>
    exfalso
    change d.site.pc = 578 at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_vote h
  case index d =>
    exfalso
    change d.site.pc = 578 at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_vote h
  case wg2 d =>
    exfalso
    change d.site.pc = 578 at h
    generalize d.site = s at h
    clear d
    cases s <;> exclude_vote h
  case idle s =>
    change s.pc = 578 at h
    cases s <;> exclude_vote h
  case head =>
    change 1843 = 578 at h
    exclude_vote h
  case done =>
    change 3611 = 578 at h
    exclude_vote h

/-- A vote-class firing belongs to the softmax reference vote and names every lane. -/
theorem of_fired {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hv : voteClass e.kind ≠ none) :
    ∃ q r, d = .wg0 q ∧ q.site = .rescaleVote ∧
      e.kind = .voteMode .any (2 ^ 32 - 1) q.voteTest r := by
  have ⟨q, hq, hs⟩ : ∃ q, d = .wg0 q ∧ q.site = .rescaleVote := by
    obtain ⟨t, _, he⟩ := hf
    change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) e o at he
    cases hc : kernel.code[(Machine.code P L g).pc d]? with
    | none =>
      rw [hc] at he
      exact (hv (fires_notVote (m := .ub .pcOutOfRange) trivial he)).elim
    | some ins =>
      rw [hc] at he
      cases hop : voteOp ins.op
      · exact (hv (fires_notVote (eventTmpl_notVote hop) he)).elim
      · exact vote_site (List.mem_singleton.mp (OpPcsFast.mem vote_cover hc hop))
  subst d
  obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
    cases o with
    | none =>
      obtain ⟨t, _, he⟩ := hf
      have hend := fires_none_ends he
      cases hk : e.kind <;> simp_all [Ends, voteClass]
    | some u => exact ⟨u, rfl⟩
  have hc : kernel.code[q.site.pc]? =
      some ⟨none, .warp ⟨.vote .any false, some .pred, [some 1], [.reg 109],
        some (.reg 1112)⟩⟩ := by
    rw [hs]
    exact Flow.code_578
  obtain ⟨t, hat, he⟩ := RingGateEvents.fired_at_code hf hc
  obtain ⟨r, hr, _⟩ := Wg0.fires_rescaleVote hs hat hc he
  exact ⟨q, r, rfl, hs, hr⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0VoteSites
