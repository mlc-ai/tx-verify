-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Close.Lag

@[expose] public section

/-! # Progress class: the TMA lane's failed poll of `lastStoreDone` (pc 2209)

A failed poll at pc 2209 is, by the mbarrier rows of the execution that performs it, the TMA
lane's first poll of its CTA's `lastStoreDone` with parity 0 (`MbarRow.TmaUse.lastWait`). The
channel blocks it (`lastStore_blk`: a warpgroup-0 lane that has not arrived lags behind the
waiter on the time table), the object's records being fault-free by safety, and the TMA lane's
wait-step row `tma_wait` steps it. Inputs: `Top.Inputs` (`mbar`, `init`, `bar0`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The TMA lane's failed poll of `lastStoreDone` steps.** -/
theorem Prog.closePoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.closeSites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  simp only [Prog.closeSites, List.mem_singleton] at hpc
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
    | lastWait _ hl hk _ =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -, -, rfl⟩ := hk
      subst hl
      have hblk := lastStore_blk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw)
        (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw)
        (Sched.safe_noUb (hs.2 X hmax.1)) (Prog.fault_free hs hmax.1 _) hn
      exact tma_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel
        (by decide) hn hblk
    | rawLoad hpc _ _ => simp [rawLoadPcs] at hpc
    | qWait hpc _ _ _ | coordWait hpc _ _ | freeWait hpc _ _ | rawArrive hpc _ _
    | coordFree hpc _ _ => simp at hpc
  · simp only [IndexAt] at hw; omega
  · simp only [DequantAt] at hw; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
