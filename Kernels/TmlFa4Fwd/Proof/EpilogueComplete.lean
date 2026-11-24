-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueProgram
public import Kernels.TmlFa4Fwd.Proof.EpilogueSearchWarp

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof Prologue

noncomputable section

/-- The complete output-role trace exits in every lane. A CTA assigned work
also issues both stages of the output for its unique request and tile. -/
def Warp13ProgramResult (p : Params) (l : Launch) (X : Execution) (g : Nat) : Prop :=
  (g / l.block < tilePrefix p p.batch * p.heads → Warp13IssuedOutput p l X g (g / l.block)) ∧
    ∀ lane < 32, (X.tr (warpLane l g lane)).getLast? = some ⟨9205, .exit⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem warp13SearchTerminal {g first shuffles votes : Nat} (hg : g < l.threads)
    (hCTA : g / l.block < l.grid) (hFirst : first < p.batch)
    (hPast : tilePrefix p (min p.batch (first + 31)) * p.heads ≤ g / l.block)
    (hProtected : DrainCuQProtected p X)
    (cur : SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p (g / l.block) first lane
      (schedulerStartupFrame p l (warpLane l g lane))) shuffles votes) :
    Warp13ProgramResult p l X g ∧
      (g / l.block < tilePrefix p p.batch * p.heads → Thread.OutputLaterDrainCuQWords p l X g) := by
  let cta := g / l.block
  let F := fun lane => schedulerStartupFrame p l (warpLane l g lane)
  have hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs :=
    fun lane _ => schedulerStartupFramed p l (warpLane l g lane)
  have hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ F lane := by
    intro lane _
    simp [F, schedulerStartupFrame]
  have hWarp : ∀ lane < 32, (1062, b32 13) ∈ F lane := by
    intro lane _
    simp [F, schedulerStartupFrame]
  suffices all : ∀ fuel first shuffles, p.batch - first = fuel → first < p.batch →
      tilePrefix p (min p.batch (first + 31)) * p.heads ≤ cta →
      SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p cta first lane (F lane))
        shuffles votes → Warp13ProgramResult p l X g ∧
          (cta < tilePrefix p p.batch * p.heads → Thread.OutputLaterDrainCuQWords p l X g) by
    exact all _ first shuffles rfl hFirst hPast cur
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro first shuffles hFuel hFirst hPast cur
    rcases SchedulerWarpAt.searchGroup hp hX hg hCTA hFirst hF hBase hWarp hProtected cur with
      ⟨hclip, ⟨exhausted⟩⟩ | ⟨hMore, hContinue | hFound⟩
    · have hDone := hPast
      rw [Nat.min_eq_left hclip] at hDone
      refine ⟨⟨fun h => (Nat.not_lt_of_ge hDone h).elim, ?_⟩,
        fun h => (Nat.not_lt_of_ge hDone h).elim⟩
      intro lane hl
      have hTail := exhausted.exitWithoutTile hp lane hl
      have he := (List.take_append_drop (exhausted.pos lane) (X.tr (warpLane l g lane))).symm
      rw [hTail] at he
      rw [he]
      simp
    · obtain ⟨hLimit, ⟨continued⟩⟩ := hContinue
      exact ih (p.batch - (first + 31)) (by omega) (first + 31) (shuffles + 7)
        rfl hMore hLimit continued
    · obtain ⟨hLimit, ⟨found⟩⟩ := hFound
      have hLow : tilePrefix p (first + 31) * p.heads ≤ cta := by
        simpa only [Nat.min_eq_right (Nat.le_of_lt hMore)] using hPast
      obtain ⟨chosen⟩ := found.enterBatchSelection hp hMore hF
      have hEnd := warp13OutputOfInterval hp hX hg hLow hLimit hProtected chosen
      exact ⟨⟨fun _ => hEnd.1, hEnd.2.1⟩, fun _ => hEnd.2.2⟩

/-- For every completed consistent execution, warp 13 follows its decoded program
from startup through request selection, output issue when assigned work, drain lookups, and exit. -/
theorem warp13ProgramWithDrainWords (hComplete : Complete l X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 13) (hProtected : DrainCuQProtected p X) :
    Warp13ProgramResult p l X g ∧
      (g / l.block < tilePrefix p p.batch * p.heads → Thread.OutputLaterDrainCuQWords p l X g) := by
  let cta := g / l.block
  let limit := tilePrefix p (min p.batch 31) * p.heads
  by_cases hFirst : cta < limit
  · have h := warp13FirstIntervalOutput hp hX hComplete hg hw hFirst hProtected
    exact ⟨⟨fun _ => h.1, h.2.1⟩, fun _ => h.2.2⟩
  · obtain ⟨cur⟩ := warp13FirstGroupCutoff hp hX hComplete hg hw (fun lane _ => hProtected lane)
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    have hBlockPos : 0 < l.block := by rw [hp.block]; decide
    have hc : cta < l.grid := (Nat.div_lt_iff_lt_mul hBlockPos).2 hg
    have hFrame := fun lane (_ : lane < 32) => schedulerStartupFramed p l (warpLane l g lane)
    have hCta (lane : Nat) (hl : lane < 32) :
        (1072, b32 cta) ∈ schedulerStartupFrame p l (warpLane l g lane) := by
      have hIndex : warpLane l g lane / l.block = cta :=
        (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
      simp [schedulerStartupFrame, hIndex]
    have hPast := Nat.le_of_not_gt hFirst
    obtain ⟨next⟩ := cur.enterSearch hPast (hc.trans hp.grid.2.2) hFrame hCta
    exact warp13SearchTerminal hp hX hg hc hp.shape.1 (by simpa only [Nat.zero_add] using hPast)
      hProtected next

/-- For every completed consistent execution, warp 13 issues its assigned output and exits. -/
theorem warp13Program (hComplete : Complete l X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 13) (hProtected : DrainCuQProtected p X) : Warp13ProgramResult p l X g :=
  (warp13ProgramWithDrainWords hp hX hComplete hg hw hProtected).1

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
