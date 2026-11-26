-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.LagFree

@[expose] public section

/-! # Progress class: the TMA lane's failed poll of `rawFree` (pc 2245)

A failed poll at pc 2245 is, by the mbarrier rows of the execution that performs it, the TMA
lane's poll of its CTA's `rawFree j` with the parity of its successful polls plus one
(`MbarRow.TmaUse.freeWait`). The channel blocks it (`rawFree_blk`: a dequant lane short of the
use lags behind the waiter on the time table), the object's records being fault-free by safety,
and the TMA lane's wait-step row `tma_wait` steps it. Inputs: `Top.Inputs` (`mbar`, `init`,
`bar0`; the raw ring's proved counts `Inputs.raw`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The TMA lane's failed poll of `rawFree` steps.** -/
theorem Prog.rawFreePoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.rawFreeSites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  simp only [Prog.rawFreeSites, List.mem_singleton] at hpc
  subst hpc
  obtain ⟨l, q, sc, hn⟩ := hf
  have hn' := hn
  obtain ⟨Y, hY, htk, he⟩ := hn'
  have hg := hn.lt
  rcases mbar_use (hIn.mbar hp Y hY (hF Y hY)) hg he rfl with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩ |
    ⟨hw, h⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · simp only [StartupAt] at hw; omega
  · simp only [Wg0At] at hw; omega
  · simp only [MmaAt] at hw; omega
  · cases h with
    | freeWait _ hl hk =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, hq, -, -, rfl⟩ := hk
      rw [htk] at hl hq
      subst hl
      have hblk := rawFree_blk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw)
        (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw) (hIn.raw hp X hmax.1 hFw)
        (Sched.safe_noUb (hs.2 X hmax.1)) (Prog.fault_free hs hmax.1 _) hq hn
      exact tma_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel
        (by decide) hn hblk
    | rawLoad hpc _ _ => simp [rawLoadPcs] at hpc
    | qWait hpc _ _ _ | lastWait hpc _ _ _ | coordWait hpc _ _ | rawArrive hpc _ _
    | coordFree hpc _ _ => simp at hpc
  · simp only [IndexAt] at hw; omega
  · simp only [DequantAt] at hw; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
