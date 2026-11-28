-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.LagMma

@[expose] public section

/-! # Progress class: the MMA lane's failed poll of `qUtccp` (pc 1983)

A failed poll at pc 1983 is, by the mbarrier rows of the execution that performs it, the MMA
lane's poll of its CTA's `qUtccp` with parity 0 (`MbarRow.MmaUse.qCopyWait`), right after its own
commit. The channel blocks it (`qUtccp_mmaBlk`: the commit's notification is undelivered while
the object's phase is even), the object's records being fault-free by safety, and the MMA lane's
wait-step row `mma_wait` steps it. Inputs: `Top.Inputs` (`mbar`, `init`, `bar0`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The MMA lane's failed poll of `qUtccp` steps.** -/
theorem Prog.qUtccpMmaPoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.qUtccpMmaSites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  simp only [Prog.qUtccpMmaSites, List.mem_singleton] at hpc
  subst hpc
  obtain ⟨l, q, sc, hn⟩ := hf
  have hn' := hn
  obtain ⟨Y, hY, -, he⟩ := hn'
  have hg := hn.lt
  rcases mbar_use (hIn.mbar hp Y hY (hF Y hY)) hg he rfl with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, h⟩ |
    ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · simp only [StartupAt] at hw; omega
  · simp only [Wg0At] at hw; omega
  · cases h with
    | qCopyWait _ hl hk _ =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -, -, rfl⟩ := hk
      subst hl
      obtain ⟨hw4, hlo, hhi⟩ := hw
      have hblk := qUtccp_mmaBlk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw)
        (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw) (Prog.fault_free hs hmax.1 _)
        hw4 ⟨hlo, hhi⟩ hn
      exact mma_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel
        (by decide) hn hblk
    | qLoad hpc _ _ => simp [qLoadPcs] at hpc
    | qWait hpc _ _ _ | qArrive hpc _ _ | qCommit hpc _ _ | kvWait hpc _ _
    | qkCommit hpc _ _ | soWait hpc _ _ | svCommit hpc _ _ => simp at hpc
  · simp only [TmaAt] at hw; omega
  · simp only [IndexAt] at hw; omega
  · simp only [DequantAt] at hw; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
