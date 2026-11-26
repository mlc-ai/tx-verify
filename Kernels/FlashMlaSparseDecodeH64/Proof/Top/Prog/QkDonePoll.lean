-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.LagQk

@[expose] public section

/-! # Progress class: warpgroup 0's failed poll of `qkDone` (pc 272)

A failed poll at pc 272 is, by the mbarrier rows of the execution that performs it, a
warpgroup-0 lane's poll of its CTA's `qkDone j` with the parity of its successful polls
(`MbarRow.Wg0Use.qkDone`). The channel blocks it (`qkDone_blk`: an undelivered commit
notification, or the CTA's MMA producer short of the use lags behind the waiter on the time table;
the reuse paths from the score ring, `qkReach`), the object's records being fault-free by safety,
and warpgroup 0's wait-step row `wg0_wait` steps it. Inputs: `Top.Inputs` (`mbar`, `init`,
`bar0`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **Warpgroup 0's failed poll of `qkDone` steps.** -/
theorem Prog.qkDonePoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.qkDoneSites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  simp only [Prog.qkDoneSites, List.mem_singleton] at hpc
  subst hpc
  obtain ⟨l, q, sc, hn⟩ := hf
  have hn' := hn
  obtain ⟨Y, hY, htk, he⟩ := hn'
  have hg := hn.lt
  rcases mbar_use (hIn.mbar hp Y hY (hF Y hY)) hg he rfl with ⟨hw, -⟩ | ⟨hw, h⟩ | ⟨hw, -⟩ |
    ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · simp only [StartupAt] at hw; omega
  · cases h with
    | qkDone _ hl hk =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, hq, -, -, rfl⟩ := hk
      rw [htk] at hl hq
      subst hl
      have hblk := qkDone_blk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw)
        (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw)
        (Sched.safe_noUb (hs.2 X hmax.1)) hw (Prog.fault_free hs hmax.1 _) hq hrel hn
      exact wg0_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel
        (by decide) hn hblk
    | lastStore hpc _ _ | coordReady hpc _ _ | coordFree hpc _ _ | soReady hpc _ _
    | svDone hpc _ _ => simp at hpc
  · simp only [MmaAt] at hw; omega
  · simp only [TmaAt] at hw; omega
  · simp only [IndexAt] at hw; omega
  · simp only [DequantAt] at hw; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
