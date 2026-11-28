-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.TcOrd
public import Lemmas.Kernel.FullVote

@[expose] public section

/-! # Warpgroup 0's collectives and votes along a step

`succ_tc`: every step off the block's end (`succ_tcOrd_*`, `succ_vote_*` by region and order);
`evK_vote`: the role's only vote is the vote site's, of the full mask. -/

/-! # Warpgroup 0's collectives and votes along a step of the epilogue

`succ_tcOrd_epi*`, `succ_vote_epi*`: the steps of `TcOrd.lean`'s statement from the
epilogue's sites, split by order (the file is split from `TcOrd.lean` for its check time). -/

/-! # Warpgroup 0's collectives and votes along a step of the block loop

`succ_tcOrd_loop*`, `succ_vote_loop*`: the steps of `TcOrd.lean`'s statement from the block
loop's sites, split by order (the file is split from `TcOrd.lean` for its check time). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

section
variable {d d' : D} {e : Event} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
  (hs : d.site ≠ .arrS) (hn : succ P L g w d e = some (some d')) {H : Nat → Nat}
  (ha : ArmOk d)
include hb hs hn ha

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_tcOrd_loopA
    (hr : d.site.reg = .loop ∧ d.site.ord < 18)
    {H : Nat → Nat} (_hH : H 0 = 0) :
    tcOrd w d' H = tcOrd w d H + if d.site.isTc then 1 else 0 := by
  w0_succ
  w0_num

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_vote_loopA
    (hr : d.site.reg = .loop ∧ d.site.ord < 18) (V : Nat → Bool) :
    VoteStep V d d' e := by
  w0_succ
  w0_vote

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_tcOrd_loopB
    (hr : d.site.reg = .loop ∧ 18 ≤ d.site.ord ∧ d.site.ord < 39)
    {H : Nat → Nat} (_hH : H 0 = 0) :
    tcOrd w d' H = tcOrd w d H + if d.site.isTc then 1 else 0 := by
  w0_succ
  w0_num

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_vote_loopB
    (hr : d.site.reg = .loop ∧ 18 ≤ d.site.ord ∧ d.site.ord < 39) (V : Nat → Bool) :
    VoteStep V d d' e := by
  w0_succ
  w0_vote

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_tcOrd_loopC
    (hr : d.site.reg = .loop ∧ 39 ≤ d.site.ord)
    {H : Nat → Nat} (_hH : H 0 = 0) :
    tcOrd w d' H = tcOrd w d H + if d.site.isTc then 1 else 0 := by
  w0_succ
  w0_num

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_vote_loopC
    (hr : d.site.reg = .loop ∧ 39 ≤ d.site.ord) (V : Nat → Bool) :
    VoteStep V d d' e := by
  w0_succ
  w0_vote

end
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

section
variable {d d' : D} {e : Event} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
  (hs : d.site ≠ .arrS) (hn : succ P L g w d e = some (some d')) {H : Nat → Nat}
  (ha : ArmOk d)
include hb hs hn ha

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_tcOrd_epiA
    (hr : d.site.reg = .epi ∧ d.site.ord < 45)
    {H : Nat → Nat} (_hH : H 0 = 0) :
    tcOrd w d' H = tcOrd w d H + if d.site.isTc then 1 else 0 := by
  w0_succ
  w0_num

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_vote_epiA
    (hr : d.site.reg = .epi ∧ d.site.ord < 45) (V : Nat → Bool) :
    VoteStep V d d' e := by
  w0_succ
  w0_vote

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_tcOrd_epiB
    (hr : d.site.reg = .epi ∧ 45 ≤ d.site.ord ∧ d.site.ord < 121)
    {H : Nat → Nat} (_hH : H 0 = 0) :
    tcOrd w d' H = tcOrd w d H + if d.site.isTc then 1 else 0 := by
  w0_succ
  w0_num

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_vote_epiB
    (hr : d.site.reg = .epi ∧ 45 ≤ d.site.ord ∧ d.site.ord < 121) (V : Nat → Bool) :
    VoteStep V d d' e := by
  w0_succ
  w0_vote

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_tcOrd_epiC
    (hr : d.site.reg = .epi ∧ 121 ≤ d.site.ord)
    {H : Nat → Nat} (_hH : H 0 = 0) :
    tcOrd w d' H = tcOrd w d H + if d.site.isTc then 1 else 0 := by
  w0_succ
  w0_num

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_vote_epiC
    (hr : d.site.reg = .epi ∧ 121 ≤ d.site.ord) (V : Nat → Bool) :
    VoteStep V d d' e := by
  w0_succ
  w0_vote

end
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- **A vote of the full mask is fired exactly at the vote site.** -/
theorem evK_vote {d : D} {e : Event} (hu : ∀ f, e.kind ≠ .ub f) (hev : EvK P L g w d e) :
    voteWith (2 ^ 32 - 1) e = decide (d.site = .vote) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  have hu' : ∀ f, kd ≠ .ub f := hu
  cases hc : voteWith (2 ^ 32 - 1) ⟨pc, kd⟩
  · cases s <;> simp only [decide_true] <;> try rfl
    simp only [EvK] at hev
    rcases hev with ⟨_, _, rfl⟩ | ⟨f, rfl⟩
    · simp at hc
    · exact absurd rfl (hu' _)
  · have hk : ∃ m q a b, kd = .voteMode q m a b ∨ ∃ c, kd = .vote m a c := by
      cases kd <;> simp [voteWith, voteClass] at hc ⊢
      exact ⟨.any⟩
    obtain ⟨m, q, a, b, hk | ⟨c, hk⟩⟩ := hk <;> subst hk <;>
      cases s <;>
      simp [EvK, TcLdEv, TcStEv, NcEv, ArrEv, PollEv, RdAt, WrAt, GWrAt, GenWrAt] at hev ⊢

/-- **A step off the block's end**: the collectives and the votes. -/
theorem succ_tc {d d' : D} {e : Event} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
    (hs : d.site ≠ .arrS) (hn : succ P L g w d e = some (some d')) (ha : ArmOk d)
    {H : Nat → Nat} (hH : H 0 = 0) (V : Nat → Bool) :
    (tcOrd w d' H = tcOrd w d H + if d.site.isTc then 1 else 0) ∧ VoteStep V d d' e := by
  rcases hr : d.site.reg
  · exact ⟨succ_tcOrd_setup hb hs hn ha hr hH, succ_vote_setup hb hs hn ha hr V⟩
  · rcases Nat.lt_or_ge d.site.ord 18 with h1 | h1
    · exact ⟨succ_tcOrd_loopA hb hs hn ha ⟨hr, h1⟩ hH, succ_vote_loopA hb hs hn ha ⟨hr, h1⟩ V⟩
    rcases Nat.lt_or_ge d.site.ord 39 with h2 | h2
    · exact ⟨succ_tcOrd_loopB hb hs hn ha ⟨hr, h1, h2⟩ hH,
        succ_vote_loopB hb hs hn ha ⟨hr, h1, h2⟩ V⟩
    · exact ⟨succ_tcOrd_loopC hb hs hn ha ⟨hr, h2⟩ hH, succ_vote_loopC hb hs hn ha ⟨hr, h2⟩ V⟩
  · rcases Nat.lt_or_ge d.site.ord 45 with h1 | h1
    · exact ⟨succ_tcOrd_epiA hb hs hn ha ⟨hr, h1⟩ hH, succ_vote_epiA hb hs hn ha ⟨hr, h1⟩ V⟩
    rcases Nat.lt_or_ge d.site.ord 121 with h2 | h2
    · exact ⟨succ_tcOrd_epiB hb hs hn ha ⟨hr, h1, h2⟩ hH,
        succ_vote_epiB hb hs hn ha ⟨hr, h1, h2⟩ V⟩
    · exact ⟨succ_tcOrd_epiC hb hs hn ha ⟨hr, h2⟩ hH, succ_vote_epiC hb hs hn ha ⟨hr, h2⟩ V⟩
  · exact ⟨succ_tcOrd_fin hb hs hn ha hr hH, succ_vote_fin hb hs hn ha hr V⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
