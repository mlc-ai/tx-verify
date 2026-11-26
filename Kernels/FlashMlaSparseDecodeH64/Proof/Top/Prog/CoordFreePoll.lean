-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Coord.LagFree

@[expose] public section

/-! # Progress class: an index lane's failed poll of `coordFree` (pcs 2446, 2534)

A failed poll at pc 2446 or 2534 is, by the mbarrier rows of the execution that performs it, an
index lane's poll of its CTA's `coordFree j` with the parity of its successful polls plus one
(`MbarRow.IndexUse.freeWait`). The channel blocks it (`coordFree_blk`: a consumer of the ring,
warpgroup 0's lane or the CTA's TMA producer, short of the use lags behind the waiter on the
time table; before the first successful poll the object is in phase 0), the object's records
being fault-free by safety, and the index lane's wait-step row (`index_wait`) steps it. Inputs:
`Top.Inputs` (`mbar`, `init`, `bar0`; the ring's proved counts `Inputs.coord`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **An index lane's failed poll of `coordFree` steps.** -/
theorem Prog.coordFreePoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.coordFreeSites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  simp only [Prog.coordFreeSites, List.mem_cons, List.not_mem_nil, or_false] at hpc
  obtain ⟨l, q, sc, hn⟩ := hf
  have hn' := hn
  obtain ⟨Y, hY, htk, he⟩ := hn'
  have hg := hn.lt
  have hub := Sched.safe_noUb (hs.2 X hmax.1)
  rcases mbar_use (hIn.mbar hp Y hY (hF Y hY)) hg he rfl with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩ |
    ⟨hw, -⟩ | ⟨hw, h⟩ | ⟨hw, -⟩
  · simp only [StartupAt] at hw; omega
  · simp only [Wg0At] at hw; omega
  · simp only [MmaAt] at hw; omega
  · simp only [TmaAt] at hw; omega
  · cases h with
    | freeWait hpc' hl hk =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, hq, -, -, rfl⟩ := hk
      rw [htk] at hl hq
      subst hl
      have hblk := coordFree_blk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw)
        (hIn.initRows hp X hmax.1 hFw) (hIn.bar0 hp X hmax.1 hFw) (hIn.coord hp X hmax.1 hFw)
        hub hpc' (Prog.fault_free hs hmax.1 _) hq hrel hn
      exact index_wait hp hFw hmax hub hpd hrel hw.2 hn hblk
    | readyArrive hpc' _ _ => simp only at hpc'; omega
  · simp only [DequantAt] at hw; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
