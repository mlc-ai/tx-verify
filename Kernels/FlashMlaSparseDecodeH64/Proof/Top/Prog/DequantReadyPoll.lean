-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Lag

@[expose] public section

/-! # Progress class: the MMA lane's failed poll of `dequantReady` (pc 2012)

A failed poll at pc 2012 is, by the mbarrier rows of the execution that performs it, the MMA
lane's poll of its CTA's `dequantReady j` with the parity of its successful polls
(`MbarRow.MmaUse.kvWait`). The channel blocks it (`dequantReady_blk`: a dequant lane short of the
use lags behind the waiter on the time table), the object's records being fault-free by safety,
and the MMA lane's wait-step row `mma_wait` steps it. Inputs: `Top.Inputs` (`mbar`, `init`,
`bar0`; the ring's proved rows `Inputs.dequant`, `Inputs.drTime`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The MMA lane's failed poll of `dequantReady` steps.** -/
theorem Prog.dequantReadyPoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.dequantReadySites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  simp only [Prog.dequantReadySites, List.mem_singleton] at hpc
  subst hpc
  obtain ⟨l, q, sc, hn⟩ := hf
  have hn' := hn
  obtain ⟨Y, hY, htk, he⟩ := hn'
  have hg := hn.lt
  rcases mbar_use (hIn.mbar hp Y hY (hF Y hY)) hg he rfl with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, h⟩ |
    ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · simp only [StartupAt] at hw; omega
  · simp only [Wg0At] at hw; omega
  · cases h with
    | kvWait _ hl hk =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, hq, -, -, rfl⟩ := hk
      rw [htk] at hl hq
      subst hl
      have hblk := dequantReady_blk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw)
        (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw) (hIn.dequant hp X hmax.1 hFw)
        (hIn.drTime hp X hmax.1 hFw)
        (Sched.safe_noUb (hs.2 X hmax.1)) (Prog.fault_free hs hmax.1 _) hq hn
      exact mma_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel
        (by decide) hn hblk
    | qLoad hpc _ _ => simp [qLoadPcs] at hpc
    | qArrive hpc _ _ | qWait hpc _ _ _ | qCommit hpc _ _ | qCopyWait hpc _ _ _
    | qkCommit hpc _ _ | soWait hpc _ _ | svCommit hpc _ _ => simp at hpc
  · simp only [TmaAt] at hw; omega
  · simp only [IndexAt] at hw; omega
  · simp only [DequantAt] at hw; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
