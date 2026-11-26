-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.LagRest

@[expose] public section

/-! # Progress class: the TMA and dequant lanes' failed polls of `qUtccp` (pcs 2205, 2644)

A failed poll at pc 2205 or 2644 is, by the mbarrier rows of the execution that performs it, the
TMA lane's (`MbarRow.TmaUse.qWait`) or a dequant lane's (`MbarRow.DequantUse.qWait`) first poll
of its CTA's `qUtccp` with parity 0. The channel blocks it (`qUtccp_restBlk`: the MMA commit's
notification is undelivered, or the CTA's MMA producer has not committed and lags behind the
waiter on the time table), the object's records being fault-free by safety, and the lane's
wait-step row (`tma_wait`, `dequant_wait`) steps it. Inputs: `Top.Inputs` (`mbar`, `init`,
`bar0`; the waiters' slot facts `Inputs.query`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **A failed poll of `qUtccp` by the TMA or a dequant lane steps.** -/
theorem Prog.qUtccpRestPoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.qUtccpSites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  simp only [Prog.qUtccpSites, List.mem_cons, List.not_mem_nil, or_false] at hpc
  obtain ⟨l, q, sc, hn⟩ := hf
  have hn' := hn
  obtain ⟨Y, hY, -, he⟩ := hn'
  have hg := hn.lt
  have hub := Sched.safe_noUb (hs.2 X hmax.1)
  rcases mbar_use (hIn.mbar hp Y hY (hF Y hY)) hg he rfl with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩ |
    ⟨hw, h⟩ | ⟨hw, -⟩ | ⟨hw, h⟩
  · simp only [StartupAt] at hw; omega
  · simp only [Wg0At] at hw; omega
  · simp only [MmaAt] at hw; omega
  · cases h with
    | qWait hpc' hl hk _ =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -, -, rfl⟩ := hk
      subst hl
      simp only at hpc'
      subst hpc'
      exact tma_wait hp hFw hmax hub hpd hrel (by decide) hn
        (qUtccp_restBlk hp hmax.1 hFw (fun Y hY => hIn.mbar hp Y hY (hF Y hY))
          (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw)
          (hIn.query hp X hmax.1 hFw) hub (.inr (.inl ⟨hw, rfl⟩))
          (Prog.fault_free hs hmax.1 _) hrel hn)
    | rawLoad hpc' _ _ =>
      simp only at hpc'
      rcases hpc with rfl | rfl <;> simp [rawLoadPcs] at hpc'
    | lastWait hpc' _ _ _ | coordWait hpc' _ _ | freeWait hpc' _ _ | rawArrive hpc' _ _
    | coordFree hpc' _ _ => simp only at hpc'; omega
  · simp only [IndexAt] at hw; omega
  · cases h with
    | qWait hpc' hl hk _ =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -, -, rfl⟩ := hk
      subst hl
      simp only at hpc'
      subst hpc'
      exact dequant_wait hp hFw hmax hub hpd hrel (by decide) hn
        (qUtccp_restBlk hp hmax.1 hFw (fun Y hY => hIn.mbar hp Y hY (hF Y hY))
          (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw)
          (hIn.query hp X hmax.1 hFw) hub (.inr (.inr ⟨hw, rfl⟩))
          (Prog.fault_free hs hmax.1 _) hrel hn)
    | rawWait hpc' _ _ | svWait hpc' _ _ | readyArrive hpc' _ _ | freeArrive hpc' _ _ =>
      simp only at hpc'; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
