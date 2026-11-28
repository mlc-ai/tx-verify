-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.LagReady
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Elect

@[expose] public section

/-! # Progress class: a dequant lane's failed poll of `rawReady` (pc 2677)

A failed poll at pc 2677 is, by the mbarrier rows of the execution that performs it, a dequant
lane's poll of its CTA's `rawReady j` with the parity of its successful polls
(`MbarRow.DequantUse.rawWait`). The channel blocks it (`rawReady_blk`: the CTA's TMA producer,
`tma_producer`, short of the use lags behind the waiter on the time table, or a tensor load is
open), the object's records being fault-free by safety and the lane past barrier 0
(`bar0_before`), and warpgroup 2's wait-step row `dequant_wait` steps it. Inputs: `Top.Inputs`
(`mbar`, `init`, `bar0`; the ring's proved rows `Inputs.raw`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **A dequant lane's failed poll of `rawReady` steps.** -/
theorem Prog.rawReadyPoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.rawReadySites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  simp only [Prog.rawReadySites, List.mem_singleton] at hpc
  subst hpc
  obtain ⟨l, q, sc, hn⟩ := hf
  have hn' := hn
  obtain ⟨Y, hY, htk, he⟩ := hn'
  have hg := hn.lt
  have hub := Sched.safe_noUb (hs.2 X hmax.1)
  rcases mbar_use (hIn.mbar hp Y hY (hF Y hY)) hg he rfl with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩ |
    ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, h⟩
  · simp only [StartupAt] at hw; omega
  · simp only [Wg0At] at hw; omega
  · simp only [MmaAt] at hw; omega
  · simp only [TmaAt] at hw; omega
  · simp only [IndexAt] at hw; omega
  · cases h with
    | rawWait _ hl hk =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, hq, -, -, rfl⟩ := hk
      have hb0 := bar0_before hp hY (hF Y hY) he (fun _ h => by cases h) (by simp)
      rw [htk] at hl hq hb0
      subst hl
      have hblk := rawReady_blk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw)
        (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw) (hIn.raw hp X hmax.1 hFw) hub
        (fun c hc => by
          obtain ⟨y, hyt, ⟨hyc, hyw, hpre⟩, hone⟩ := tma_producer hp hmax.1 hFw hub hc
          exact ⟨y, hyc, hyt, hyw, hone, hpre⟩)
        hb0 (Prog.fault_free hs hmax.1 _) hq hrel hn
      exact dequant_wait hp hFw hmax hub hpd hrel (by decide) hn hblk
    | qWait hpc _ _ _ | svWait hpc _ _ | readyArrive hpc _ _ | freeArrive hpc _ _ =>
      simp at hpc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
