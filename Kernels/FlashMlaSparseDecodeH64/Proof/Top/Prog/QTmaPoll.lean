-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect

@[expose] public section

/-! # Progress class: the failed poll of `qTma` (pc 1931)

A failed poll at pc 1931 is, by the mbarrier rows of the execution that performs it, the MMA
lane's poll of its CTA's `qTma` with parity 0 (`MbarRow.MmaUse.qWait`). The channel blocks it
(`qTma_blk`: an open tensor load), the object's records being fault-free by safety, and the MMA
lane's wait-step row `mma_wait` steps it. Inputs: `Top.Inputs` (`mbar`, `init`, `bar0`); one
MMA lane per CTA is `mmaOne`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- The records of an object of a safe launch's consistent execution are fault-free. -/
theorem Prog.fault_free (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (l : Loc) :
    ∀ r ∈ X.objects l, r.fault = none := by
  intro r hr
  cases hf : r.fault with
  | none => rfl
  | some f =>
    exact (hs.2 X hX (.inr (.inr (.inr (.inr (.inr (.inl (.inl ⟨l, r, hr, by simp [hf]⟩))))))))
      |>.elim

/-- **The failed poll of `qTma` steps.** -/
theorem Prog.qTmaPoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.qTmaSites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  simp only [Prog.qTmaSites, List.mem_singleton] at hpc
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
    | qWait _ hl hk _ =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -, -, rfl⟩ := hk
      subst hl
      obtain ⟨-, hblk⟩ := qTma_blk hp hmax.1 hFw (fun Y hY => hIn.mbar hp Y hY (hF Y hY))
        (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw) (mmaOne hp hmax.1 hFw)
        (Prog.fault_free hs hmax.1 _) hn
      exact mma_wait hp hFw hmax (Sched.safe_noUb (hs.2 X hmax.1)) hpd hrel
        (by decide) hn hblk
    | qLoad hpc _ _ => simp [qLoadPcs] at hpc
    | qArrive hpc _ _ | qCommit hpc _ _ | qCopyWait hpc _ _ _ | kvWait hpc _ _
    | qkCommit hpc _ _ | soWait hpc _ _ | svCommit hpc _ _ => simp at hpc
  · simp only [TmaAt] at hw; omega
  · simp only [IndexAt] at hw; omega
  · simp only [DequantAt] at hw; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
