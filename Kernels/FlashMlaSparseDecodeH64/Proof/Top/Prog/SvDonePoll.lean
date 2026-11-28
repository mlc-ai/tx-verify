-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.LagSv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0

@[expose] public section

/-! # Progress class: a failed poll of `svDone` (pcs 1184, 2684)

A failed poll at pc 1184 or 2684 is, by the mbarrier rows of the execution that performs it,
warpgroup 0's one poll of its CTA's `svDone` after its last block (`MbarRow.Wg0Use.svDone`) or a
dequant lane's poll of `svDone j` with the parity of its successful polls plus one
(`MbarRow.DequantUse.svWait`). The channel blocks it (`svDone_w0Blk`, `svDone_dqBlk`: an
undelivered commit notification, or the CTA's MMA producer short of the waited use lags behind
the waiter on the time table), the object's records being fault-free by safety, and the lane's
wait-step row (`wg0_wait`, `dequant_wait`) steps it. Inputs: `Top.Inputs` (`mbar`, `init`,
`bar0`; the dequantized buffer ring's proved counts `Inputs.dequant`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **A failed poll of `svDone` steps.** -/
theorem Prog.svDonePoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.svDoneSites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  obtain ⟨l, q, sc, hn⟩ := hf
  have hn' := hn
  obtain ⟨Y, hY, htk, he⟩ := hn'
  have hg := hn.lt
  have hub := Sched.safe_noUb (hs.2 X hmax.1)
  simp only [Prog.svDoneSites, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases mbar_use (hIn.mbar hp Y hY (hF Y hY)) hg he rfl with ⟨hw, -⟩ | ⟨hw, h⟩ | ⟨hw, -⟩ |
    ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, h⟩
  · simp only [StartupAt] at hw; omega
  · cases h with
    | svDone _ hl hk =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, -, -, -, rfl⟩ := hk
      rw [htk] at hl
      subst hl
      rcases hpc with rfl | rfl
      · exact wg0_wait hp hFw hmax hub hpd hrel (by decide) hn
          (svDone_w0Blk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw) (hIn.initRows hp X hmax.1 hFw)
            (hIn.bar0 hp X hmax.1 hFw) hub (Prog.fault_free hs hmax.1 _) hrel hn)
      · simp only [Wg0At] at hw; omega
    | lastStore hpc' _ _ | qkDone hpc' _ _ | coordReady hpc' _ _ | coordFree hpc' _ _
    | soReady hpc' _ _ => simp only at hpc'; omega
  · simp only [MmaAt] at hw; omega
  · simp only [TmaAt] at hw; omega
  · simp only [IndexAt] at hw; omega
  · cases h with
    | svWait _ hl hk =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, hq, -, -, rfl⟩ := hk
      have hb0 := bar0_before hp hY (hF Y hY) he (fun _ h => by cases h) (by simp only; omega)
      rw [htk] at hl hq hb0
      subst hl
      rcases hpc with rfl | rfl
      · simp only [DequantAt] at hw; omega
      · exact dequant_wait hp hFw hmax hub hpd hrel (by decide) hn
          (svDone_dqBlk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw) (hIn.initRows hp X hmax.1 hFw)
            (hIn.bar0 hp X hmax.1 hFw) (hIn.dequant hp X hmax.1 hFw) hub hb0
            (Prog.fault_free hs hmax.1 _) hq hrel hn)
    | rawWait hpc' _ _ | qWait hpc' _ _ _ | readyArrive hpc' _ _ | freeArrive hpc' _ _ =>
      simp only at hpc'; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
