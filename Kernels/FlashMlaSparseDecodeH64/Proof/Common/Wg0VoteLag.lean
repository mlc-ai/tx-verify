-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0TcLag
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollW0
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteCmp
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Poll
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The votes of the lanes of warps 0 to 3

`VoteAt`: a thread state at the vote of warpgroup 0. The votes a lane has made are counted by
its state (`w0_tc`, `Wg0.vOrd`). A state at the vote has made fewer votes than the CTA has blocks
(`vote_cnt_lt`), a lane at its exit exactly as many (`vote_cnt_exit`), and a lane of the warp that
has made at most as many and is not at the vote with as many is at an earlier place
(`vote_lag`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g h y : Nat}

/-- **A thread state at the vote of warpgroup 0.** -/
def VoteAt (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) : Prop :=
  warpOf L g < 4 ∧ ∃ d n, σ = w0S P L g d n ∧ d.site = .vote

/-- The votes a lane has made, as the library counts them. -/
theorem vote_maskCount (X : Execution) (y : Nat) :
    Step.maskCount voteClass X y (2 ^ 32 - 1) = vCnt X y (X.tr y).length := by
  simp only [Step.maskCount, vCnt, List.take_length]
  rfl

/-- The reference facts of a state of warpgroup 0. -/
theorem w0_ref (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) (hy : y < L.threads)
    {i : Nat} {d : Wg0.Control.D} {n : Cls → Nat}
    (hs : Frame.stateAt (thread P L) X y i = some (some (w0S P L y d n))) :
    (∃ c, Wg0.RefCore L y d c) ∧ Wg0.LaunchOk P L y d := by
  rcases w0_bst hFw hnu hw hy hs with ⟨_, _, hx, -⟩ | ⟨d', n', hx, hC, hL, -⟩
  · cases hx
  · simp only [w0S, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
    obtain ⟨rfl, -⟩ := hx
    exact ⟨⟨_, hC⟩, hL⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X)
include hp hX hFw hnu

/-- **A state at the vote has made fewer votes than the CTA has blocks.** -/
theorem vote_cnt_lt (hw : warp L y < 4) (hy : y < L.threads) {d : Wg0.Control.D}
    {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X y (X.tr y).length = some (some (w0S P L y d n)))
    (hs : d.site = .vote) :
    Step.maskCount voteClass X y (2 ^ 32 - 1) < blocksOf P L (y / L.block) := by
  obtain ⟨-, hv, -, -⟩ := w0_tc hp hX hFw hw hy _ (noUbBefore_of_noUb hnu) _ hσ
  obtain ⟨⟨_, hC⟩, hL⟩ := w0_ref hFw hnu hw hy hσ
  have h1 := Wg0.vote_lt_rounds hC hs
  rw [Wg0.rounds_blocks hL (Wg0.lens_two (by rw [hs]; decide))] at h1
  rw [vote_maskCount, hv]
  exact h1

/-- **A lane at its exit has made one vote per block.** -/
theorem vote_cnt_exit (hw : warp L y < 4) (hy : y < L.threads) {k pc : Nat}
    {σ : (thread P L y).D} (hσ : Frame.stateAt (thread P L) X y k = some (some σ))
    (hex : X.get (y, k) = some ⟨pc, .exit⟩) :
    blocksOf P L (y / L.block) ≤ vCnt X y k := by
  obtain ⟨σ0, hσ0, -, -, hev, -⟩ := ev_at hp hX hFw hex (fun _ h => by cases h)
  rw [hσ] at hσ0
  cases hσ0
  rcases w0_bst hFw hnu hw hy hσ with ⟨d, n, rfl, hxd⟩ | ⟨d, n, rfl, hC, hL, -⟩
  · exact (start_noExit hxd hev rfl).elim
  · obtain ⟨-, hv, -⟩ := w0_tc hp hX hFw hw hy k (noUbBefore_of_noUb hnu) _ hσ
    obtain ⟨-, hK⟩ : Wg0.Ev P L y (warpW L y) d ⟨pc, .exit⟩ := hev
    have hs := Wg0.evK_exit hK rfl
    have hR := Wg0.rounds_blocks hL (by rw [hs]; decide)
    rw [hv, Wg0.vOrd_exit hs, hR]

/-- **The lag at the vote**: a lane of the warp that has made at most the lane's votes and is not
at a vote with as many has a state at an earlier place. -/
theorem vote_lag (hw : warp L g < 4) (hsw : SameWarp L g h) {d : Wg0.Control.D}
    {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some (w0S P L g d n)))
    (hs : d.site = .vote)
    (hle : Step.maskCount voteClass X h (2 ^ 32 - 1) ≤ Step.maskCount voteClass X g (2 ^ 32 - 1))
    (hnot : ¬ (Step.maskCount voteClass X h (2 ^ 32 - 1) =
      Step.maskCount voteClass X g (2 ^ 32 - 1) ∧ ∃ d', Frame.stateAt (thread P L) X h
        (X.tr h).length = some (some d') ∧ VoteAt P L h d'))
    (hne : Frame.stateAt (thread P L) X h (X.tr h).length ≠ none) :
    Sched.threadTime (timed P L) X h < time P L g (w0S P L g d n) := by
  have hg : g < L.threads := hsw.1.1
  have hh : h < L.threads := hsw.1.2.1
  obtain ⟨hwe, hWe⟩ := warpW_same hp hsw
  have hwh : warp L h < 4 := hwe ▸ hw
  obtain ⟨-, gv, -, -⟩ := w0_tc hp hX hFw hw hg _ (noUbBefore_of_noUb hnu) _ hσ
  obtain ⟨⟨_, hC⟩, hL⟩ := w0_ref hFw hnu hw hg hσ
  have hRd := Wg0.rounds_blocks hL (Wg0.lens_two (by rw [hs]; decide))
  rw [timed_eq]
  cases hst : Frame.stateAt (thread P L) X h (X.tr h).length with
  | none => exact absurd hst hne
  | some o =>
    cases o with
    | none =>
      simp only [Sched.threadTime, hst]
      rw [w0_time]
      simp only [wg0Org]
      omega
    | some σh =>
      rw [Sched.threadTime_of hst]
      show time P L h σh < time P L g (w0S P L g d n)
      rw [w0_time]
      rcases w0_bst hFw hnu hwh hh hst with ⟨s, n', rfl, hxs⟩ | ⟨s, n', rfl, hC', hL', -⟩
      · have := Startup.time_lt hxs
        simp only [time] at this ⊢
        simp only [wg0Org]
        omega
      · obtain ⟨-, hv, -, -⟩ := w0_tc hp hX hFw hwh hh _ (noUbBefore_of_noUb hnu) _ hst
        rw [w0_time]
        have hR' : s.site.reg ≠ .setup → Wg0.rounds s.l0 s.l1 = Wg0.rounds d.l0 d.l1 :=
          fun hr => by
            rw [Wg0.rounds_blocks hL' (Wg0.lens_two hr), hRd, hsw.1.2.2]
        rw [vote_maskCount, vote_maskCount, hv, gv] at hle
        have hlt := Wg0.vote_place_lt hC hC' hs hR' hle (fun ⟨h1, h2⟩ =>
          hnot ⟨by rw [vote_maskCount, vote_maskCount, hv, gv]; exact h1,
            _, hst, hwh, s, n', rfl, h2⟩)
        omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
