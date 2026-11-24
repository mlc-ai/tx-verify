-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueFirstPassTrace
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpStartup
public import Kernels.TmlFa4Fwd.Proof.NoCancellation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof Prologue

noncomputable section

private theorem firstPassOffset_eq (p : Params) (lane : Nat) :
    firstSchedulerWord p lane = firstPassOffset p lane := by
  by_cases h : lane ≤ p.batch
  · simp [firstSchedulerWord, firstPassOffset, h, Nat.not_lt_of_ge h]
  · simp [firstSchedulerWord, firstPassOffset, h, Nat.lt_of_not_ge h]

/-- Warp 13's actual startup reaches its first group decision under the full kernel assumptions. -/
theorem warp13FirstGroupCutoff {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13)
    (hProtected : ∀ lane < 32, lane ≤ p.batch → ∀ k < 4, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ((globalLoc (p.cuQBase + 4 * lane)).at k)) :
    Nonempty (FirstGroupCutoff p l Assumptions.all X g (g / l.block)
      (fun lane => schedulerStartupFrame p l (warpLane l g lane)) 10 0) := by
  let F := fun lane => schedulerStartupFrame p l (warpLane l g lane)
  obtain ⟨state, hOrdinal, hCheckpoint⟩ :=
    warp13FirstShuffle hp hX hComplete hg hw (fun _ _ => noCanceled hX) hProtected
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hBlockPos : 0 < l.block := by rw [hp.block]; decide
  have hCta : g / l.block < 2 ^ 31 :=
    lt_trans ((Nat.div_lt_iff_lt_mul hBlockPos).2 (show g < l.grid * l.block from hg)) hp.grid.2.2
  have hReg : ∀ lane, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs := by
    intro lane pair hm
    simp only [F, schedulerStartupFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [firstPassRegs, schedulerFrameRegs]
  have hCtaFact (lane : Nat) (hl : lane < 32) : (1072, b32 (g / l.block)) ∈ F lane := by
    have hw' := (Step.sameWarp_lane hBlock hg hl).1
    have h := hw'.1.2.2
    simp [F, schedulerStartupFrame, warpLane, h]
  apply firstPassThroughCutoff hp hX hg hCta
    (fun _ {s} hlo hhi => epilogue_out_all_eq_nil (t := s) (.inl ⟨by omega, by omega⟩))
    (fun lane _ => hReg lane) hCtaFact hOrdinal
    (fun lane hl => (hCheckpoint lane hl).2.1)
  intro lane hl
  have ht := (hCheckpoint lane hl).2.2
  have hLane := (Step.sameWarp_lane hBlock hg hl).2
  have hLaneReg : (1201, b32 lane) ∈ F lane := by
    unfold F schedulerStartupFrame
    change laneOf l (warpLane l g lane) = lane at hLane
    simp [hLane]
  have hSource : (if lane + 1 < 32 then lane + 1 else lane) =
      if lane < 31 then lane + 1 else lane := by
    split <;> split <;> omega
  rw [hSource, firstPassOffset_eq, firstPassOffset_eq] at ht
  have hs := ht.2.2.2.2
  exact ht.mono ⟨holds_mem hs.2.2.2 hLaneReg, hs⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
