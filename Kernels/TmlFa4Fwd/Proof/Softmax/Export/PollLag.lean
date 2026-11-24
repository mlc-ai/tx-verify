-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Lag
public import Kernels.TmlFa4Fwd.Proof.Top.Table
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The round and the time of a softmax lane at a poll

`soft_poll_at`: a softmax lane at a poll of S full, Bias full or (the closing poll of a round) the
credit barrier is in a round `u` of the tile; its successful polls of the barrier and its time are
closed forms in `u`. `soft_wend_at`: the final credit poll, after all rounds. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before inBias inPlain allSites
  mem_allSites)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A poll of a round, with the round's S-full polls and the poll's own before it. -/
def midPoll : Softmax.Site → Option (Nat × Nat)
  | .ws _ => some (0, 0)
  | .wb _ => some (1, 0)
  | .pwend _ => some (1, 1)
  | _ => none

/-- The regions and the poll points of the polls of a round. -/
private def pollChk (b : Bool) (s : Softmax.Site) : Bool := match midPoll s with
  | none => true
  | some (x, y) =>
    decide (SmWarp.epi s = .ready 0) && s.hasUk &&
    (Softmax.preR s || inBias s.pos || inPlain s.pos) &&
    (let z := if Softmax.preR s then 0 else 1
     decide ((ptsOf b (.acquire 80)).countP (before s) = z + x) &&
     decide ((ptsOf b (.acquire (Softmax.pollOff s))).countP (before s) = z + y)) &&
    decide ((ptsOf b (.acquire (Softmax.pollOff s))).countP inBias = 1) &&
    (decide ((ptsOf b (.acquire (Softmax.pollOff s))).countP inPlain = 1) ||
      (decide (Softmax.pollOff s = 320) && !inPlain s.pos))

private theorem poll_chk : [false, true].all (fun b => allSites.all (pollChk b)) = true := by
  decide +kernel

private theorem poll_ok (b : Bool) (s : Softmax.Site) : pollChk b s = true :=
  List.all_eq_true.mp (List.all_eq_true.mp poll_chk b (by cases b <;> simp)) s (mem_allSites s)

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) {d : Softmax.Control.D} {n : Cls → Nat}
  (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.softmax, d⟩, n)))
include hp hX hFw hub hg hσ

/-- The reference at the end of the trace. -/
theorem soft_end : Prologue.warpIndex L g < 8 ∧ ∃ c rb rp, RefQ p L g d c rb rp ∧
    SmWarp.SFits p L g d (n .shfl) (n .vote) ∧
    (∀ c', c'.pointed = true → ((X.tr g)).countP (cls L g (.soft c')) = c c') ∧
    n (.soft (.acquire 80)) = c (.acquire 80) := by
  have hJ := (goodR hp hX hFw hg _).2 _ hσ
  obtain ⟨hw, -, hR⟩ := JR.softmax hJ
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR hub0
  refine ⟨hw, c, rb, rp, hQ, hF, fun c' hc' => ?_, (hLk _ rfl).symm⟩
  have := count hσ (.soft c')
  rw [List.take_length] at this
  rw [this, ← hLk c' hc']

/-- **A softmax lane at a poll of a round**: its round, its polls and its time. -/
theorem soft_poll_at {x y : Nat} (hs : midPoll d.scheduler.site = some (x, y)) :
    ∃ T u, SoftRounds p L g T ∧ u < T ∧
      okPolls (sobj L g (Softmax.pollOff d.scheduler.site)) (X.tr g) = u + y ∧
      n (.soft (.acquire 80)) = u + x := by
  obtain ⟨hw, c, rb, rp, hQ, hF, hc, hn⟩ := soft_end hp hX hFw hub hg hσ
  have hchk := poll_ok (Softmax.lz L g) d.scheduler.site
  simp only [pollChk, hs, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hep, huk⟩, hr⟩, h80, ho⟩, hb⟩, hpl⟩ := hchk
  obtain ⟨T, hT, h1, h2⟩ := soft_round_lt hQ hF hep huk (by tauto)
  have e80 := hQ.cnt (.acquire 80) rfl
  have eo := hQ.cnt (.acquire (Softmax.pollOff d.scheduler.site)) rfl
  have t80 : ∀ b : Bool, (ptsOf b (.acquire 80)).countP inBias = 1 ∧
      (ptsOf b (.acquire 80)).countP inPlain = 1 := by decide +kernel
  obtain ⟨t1, t2⟩ := t80 (Softmax.lz L g)
  have hok : okPolls (sobj L g (Softmax.pollOff d.scheduler.site)) (X.tr g) =
      c (.acquire (Softmax.pollOff d.scheduler.site)) := by
    have := soft_okPolls (X := X) (k := (X.tr g).length) hw (Softmax.pollOff d.scheduler.site)
    rw [List.take_length] at this
    rw [sobj, this, hc _ rfl]
  simp only [passed, t1, t2, hb] at e80 eo
  rw [hok, hn, e80, eo, h80, ho]
  have hrp : rp *
      (ptsOf (Softmax.lz L g) (.acquire (Softmax.pollOff d.scheduler.site))).countP inPlain =
      rp := by
    rcases hpl with hpl | ⟨-, hpl⟩
    · rw [hpl, Nat.mul_one]
    · have h0 : rp = 0 := by
        rcases hr with (hr | hr) | hr
        · exact (hQ.pre hr).2
        · exact (hQ.bias hr).1
        · simp [hr] at hpl
      rw [h0, Nat.zero_mul]
  rw [hrp]
  cases hpre : Softmax.preR d.scheduler.site with
  | true =>
    obtain ⟨rfl, rfl⟩ := hQ.pre hpre
    exact ⟨T, 0, hT, by omega, by simp, by simp⟩
  | false =>
    rw [hpre] at h2
    refine ⟨T, 1 + rb + rp, hT, by simpa using h2, ?_, ?_⟩ <;> simp <;> omega

/-- The first credit poll, and the only one of a lane without a tile, is the lane's first. -/
theorem soft_first_poll (hs : d.scheduler.site = .wq ∨ d.scheduler.site = .wend false) :
    okPolls (sobj L g 192) (X.tr g) = 0 := by
  obtain ⟨hw, c, rb, rp, hQ, hF, hc, hn⟩ := soft_end hp hX hFw hub hg hσ
  have hok := soft_okPolls (X := X) (k := (X.tr g).length) hw 192
  rw [List.take_length] at hok
  have e := hQ.cnt (.acquire 192) rfl
  have t : ∀ b : Bool, ((ptsOf b (.acquire 192)).countP (before .wq) = 0 ∧
      (ptsOf b (.acquire 192)).countP (before (.wend false)) = 0) ∧
      Softmax.preR .wq = true ∧ Softmax.preR (.wend false) = true := by decide +kernel
  obtain ⟨⟨t1, t2⟩, t3, t4⟩ := t (Softmax.lz L g)
  rw [sobj, hok, hc _ rfl, e, passed]
  rcases hs with hs | hs
  · obtain ⟨rfl, rfl⟩ := hQ.pre (by rw [hs]; exact t3)
    rw [hs, t1]; omega
  · obtain ⟨rfl, rfl⟩ := hQ.pre (by rw [hs]; exact t4)
    rw [hs, t2]; omega

/-- The last credit poll of a lane with a tile is after its rounds. -/
theorem soft_last_poll (hs : d.scheduler.site = .wend true) :
    ∃ T, SoftRounds p L g T ∧ okPolls (sobj L g 192) (X.tr g) = T + 1 := by
  obtain ⟨hw, c, rb, rp, hQ, hF, hc, hn⟩ := soft_end hp hX hFw hub hg hσ
  have hok : ∀ a, okPolls (sobj L g a) (X.tr g) = c (.acquire a) := fun a => by
    have := soft_okPolls (X := X) (k := (X.tr g).length) hw a
    rw [List.take_length] at this
    rw [sobj, this, hc _ rfl]
  have e192 := hQ.cnt (.acquire 192) rfl
  have e80 := hQ.cnt (.acquire 80) rfl
  have enb := hQ.cnt .nb rfl
  have t : ∀ b : Bool, ((ptsOf b (.acquire 192)).countP (before (.wend true)) = 2 ∧
      (ptsOf b (.acquire 80)).countP (before (.wend true)) = 1 ∧
      (ptsOf b .nb).countP (before (.wend true)) = 2) ∧
      ((ptsOf b (.acquire 192)).countP inBias = 1 ∧ (ptsOf b (.acquire 192)).countP inPlain = 1) ∧
      ((ptsOf b (.acquire 80)).countP inBias = 1 ∧ (ptsOf b (.acquire 80)).countP inPlain = 1) ∧
      (ptsOf b .nb).countP inBias = 1 ∧ (ptsOf b .nb).countP inPlain = 1 := by decide +kernel
  obtain ⟨⟨t1, t2, t3⟩, ⟨t4, t5⟩, ⟨t6, t7⟩, t8, t9⟩ := t (Softmax.lz L g)
  rw [hs] at e192 e80 enb
  simp only [passed, t1, t2, t3, t4, t5, t6, t7, t8, t9] at e192 e80 enb
  refine ⟨c (.acquire 80), soft_late_rounds hp hX hFw hw (k := (X.tr g).length) ?_ ?_, ?_⟩
  · rw [List.take_length]
    have := soft_isBarId (X := X) (k := (X.tr g).length) hw
    rw [List.take_length] at this
    rw [this, hc _ rfl, enb, e80]; omega
  · rw [List.take_length, hok]
  · rw [hok, e192, e80]; omega

end
/-- **The barrier a softmax lane's poll event is on**, and the offsets. -/
theorem soft_wait_loc (hw : Prologue.warpIndex L g < 8) {d : Softmax.Control.D} {n : Cls → Nat}
    {pc q : Nat} {l : Loc} {ok acq : Bool} {sc : MbarScope}
    (hev : TEv p L g (.inr ⟨.softmax, d⟩, n) ⟨pc, .wait l q ok acq sc⟩) :
    l = sobj L g (Softmax.pollOff d.scheduler.site) ∧ (Softmax.pollOff d.scheduler.site = 192 ∨
      Softmax.pollOff d.scheduler.site = 80 ∨ Softmax.pollOff d.scheduler.site = 320) := by
  rcases soft_mbar hev.1 (l := l) rfl with ⟨hk, -⟩ | ⟨_, _, -, hl, hmem⟩
  · cases hk
  · exact ⟨hl.trans (soft_bl hw _), by simpa using hmem⟩

/-- The sites of the polls by their barriers. -/
theorem soft_site_of_off {s : Softmax.Site} (h : Softmax.pollOff s = 80 ∨
    Softmax.pollOff s = 320) : (∃ r, s = .ws r) ∨ ∃ b, s = .wb b := by
  cases s <;> simp [Softmax.pollOff] at h ⊢

theorem soft_ws_off (r : Softmax.Rd) : Softmax.pollOff (.ws r) = 80 := rfl

theorem soft_wb_off (b : Bool) : Softmax.pollOff (.wb b) = 320 := rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof
