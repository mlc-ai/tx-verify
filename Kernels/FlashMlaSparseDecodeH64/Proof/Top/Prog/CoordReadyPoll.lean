-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Coord.LagReady

@[expose] public section

/-! # Progress class: a consumer's failed poll of `coordReady` (pcs 264, 2234)

A failed poll at pc 264 or 2234 is, by the mbarrier rows of the execution that performs it, a
warpgroup-0 lane's (`MbarRow.Wg0Use.coordReady`) or the TMA lane's (`MbarRow.TmaUse.coordWait`)
poll of its CTA's `coordReady j` with the parity of its successful polls. The channel blocks it
(`coordReady_blk`: an index lane short of the use lags behind the waiter on the time table), the
object's records being fault-free by safety, and the lane's wait-step row (`wg0_wait`,
`tma_wait`) steps it. Inputs: `Top.Inputs` (`mbar`, `init`, `bar0`; the ring's proved counts
`Inputs.coord`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **A consumer's failed poll of `coordReady` steps.** -/
theorem Prog.coordReadyPoll (hp : Pre P L m) (hIn : Top.Inputs P L m)
    (hF : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X) :
    Prog.PollSteps P L m Prog.coordReadySites := by
  intro hs X hmax hFw g pc hpc hpd hrel hf
  obtain ⟨l, q, sc, hn⟩ := hf
  have hn' := hn
  obtain ⟨Y, hY, htk, he⟩ := hn'
  have hg := hn.lt
  have hub := Sched.safe_noUb (hs.2 X hmax.1)
  have hblk := fun {pc : Nat} {s : Fin 4} (hc : pc = 264 ∧ warp L g < 4 ∨ pc = 2234)
      (hq : q = PTX.Flow.okPolls (loc L g (.coordReady s)) (X.tr g) % 2)
      (hn : Sched.NextEv L kernel Assumptions.all m X g
        ⟨pc, .wait (loc L g (.coordReady s)) q false true sc⟩) =>
    coordReady_blk hp hmax.1 hFw (hIn.mbar hp X hmax.1 hFw) (hIn.initRows hp X hmax.1 hFw)
      (hIn.bar0 hp X hmax.1 hFw) (hIn.coord hp X hmax.1 hFw) hub hc
      (Prog.fault_free hs hmax.1 _) hq hrel hn
  simp only [Prog.coordReadySites, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases mbar_use (hIn.mbar hp Y hY (hF Y hY)) hg he rfl with ⟨hw, -⟩ | ⟨hw, h⟩ | ⟨hw, -⟩ |
    ⟨hw, h⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · simp only [StartupAt] at hw; omega
  · cases h with
    | coordReady _ hl hk =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, hq, -, -, rfl⟩ := hk
      rw [htk] at hl hq
      subst hl
      rcases hpc with rfl | rfl
      · exact wg0_wait hp hFw hmax hub hpd hrel (by decide) hn
          (hblk (.inl ⟨rfl, hw.1⟩) hq hn)
      · simp only [Wg0At] at hw; omega
    | lastStore hpc' _ _ | qkDone hpc' _ _ | coordFree hpc' _ _ | soReady hpc' _ _
    | svDone hpc' _ _ => simp only at hpc'; omega
  · simp only [MmaAt] at hw; omega
  · cases h with
    | coordWait _ hl hk =>
      obtain ⟨ok, hk⟩ := hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨-, hq, -, -, rfl⟩ := hk
      rw [htk] at hl hq
      subst hl
      rcases hpc with rfl | rfl
      · simp only [TmaAt] at hw; omega
      · exact tma_wait hp hFw hmax hub hpd hrel (by decide) hn (hblk (.inr rfl) hq hn)
    | rawLoad hpc' _ _ =>
      simp only at hpc'
      rcases hpc with rfl | rfl <;> simp [rawLoadPcs] at hpc'
    | qWait hpc' _ _ _ | lastWait hpc' _ _ _ | freeWait hpc' _ _ | rawArrive hpc' _ _
    | coordFree hpc' _ _ => simp only at hpc'; omega
  · simp only [IndexAt] at hw; omega
  · simp only [DequantAt] at hw; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
