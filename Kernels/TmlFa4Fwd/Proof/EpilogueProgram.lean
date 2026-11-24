-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueFirstPassEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainComplete

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof Prologue

noncomputable section

/-- Every lane's output issues and ready polls for the assigned request and tile. -/
def Warp13IssuedOutput (p : Params) (l : Launch) (X : Execution) (g cta : Nat) : Prop :=
  ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ cta ∧
    cta < tilePrefix p (batch + 1) * p.heads ∧
      let coords := assignedCoordinates p batch cta
      ∀ lane < 32, ∃ j written suffix,
        (X.tr (warpLane l g lane)).drop j = written ++ suffix ∧
        WritebackTrace p l (warpLane l g lane) batch coords.2 coords.1 (some (.ready 0))
          written none ∧
        written.filter (fun e => writebackSucceeded e.kind) =
          writebackRemaining p l (warpLane l g lane) batch coords.2 coords.1 (some (.ready 0))

/-- Warp 13's ABI registers are unchanged by the scheduler's request selection. -/
theorem schedulerStartupFramed (p : Params) (l : Launch) (g : Nat) :
    ∀ pair ∈ schedulerStartupFrame p l g, pair.1 ∈ schedulerFrameRegs := by
  intro pair hm
  simp only [schedulerStartupFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [schedulerFrameRegs]

/-- From a selected scheduler interval, the real warp issues the two stages of output,
including the polls and release events, then runs through the drain to its exit. -/
theorem warp13OutputOfInterval {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads)
    (hLow : tilePrefix p first * p.heads ≤ g / l.block)
    (hHigh : g / l.block < tilePrefix p (min p.batch (first + 31)) * p.heads)
    (hProtected : DrainCuQProtected p X)
    (chosen : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p (g / l.block) first
      lane (schedulerStartupFrame p l (warpLane l g lane))) shuffles votes) :
    Warp13IssuedOutput p l X g (g / l.block) ∧
      (∀ lane < 32, (X.tr (warpLane l g lane)).getLast? = some ⟨9205, .exit⟩) ∧
      Thread.OutputLaterDrainCuQWords p l X g := by
  let cta := g / l.block
  let F := fun lane => schedulerStartupFrame p l (warpLane l g lane)
  have hFrame : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs :=
    fun lane _ => schedulerStartupFramed p l (warpLane l g lane)
  obtain ⟨batch, hFirst, hGroup, hBatch, hLo, hHi, ⟨tileCursor⟩⟩ :=
    chosen.chooseTile hp hX hg hLow hHigh hFrame
  let coords := assignedCoordinates p batch cta
  obtain ⟨ready, _⟩ := tileCursor.enterWriteback hp hX hg hFirst hGroup hBatch hLo hHi
    hFrame (fun _ _ _ hm => hm)
    (fun endpoint => hProtected (batch + endpoint.val) (by have := endpoint.isLt; omega))
  obtain ⟨hTile, hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hRun lane hl :=
    (ready.continuation lane hl).after_local (ready.localSteps lane hl)
  have hAt lane hl := outputReady_writebackAt (ready.checkpoint lane hl)
  have hGuardFacts (lane : Nat) (hl : lane < 32) : Holds (ready.state lane).regs
      ([(307, .pred (decide (p.batch < lane))), (1201, b32 lane), (7506, b64 p.cuQBase),
        (268, .pred (!decide (laneHasRequest lane p.batch))), (7147, b32 p.batch),
        (7138, b32 p.heads)] ++ F lane) := by
    exact ((holds_append ..).mp (ready.checkpoint lane hl).2.2.2.2).2
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCTA : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hTotal : cta < tilePrefix p p.batch * p.heads := hHigh.trans_le
    (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left _ _)))
  refine ⟨⟨batch, hBatch, hLo, hHi, ?_⟩, ?_⟩
  · dsimp only
    intro lane hl
    let thread := warpLane l g lane
    have hRange {s : TState} (hs : WritebackPc s.pc) :
        out kernel Assumptions.all l thread s = out kernel [] l thread s :=
      epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)
    obtain ⟨written, suffix, last, _, hSplit, hTrace, _, _, hTail⟩ :=
      writebackFromFirstPollOfOutEq hp thread hRange hBatch hHead hTile (hAt lane hl) (hRun lane hl)
    cases last with
    | some _ => exact False.elim (Bool.noConfusion hTail.2)
    | none => exact ⟨ready.pos lane, written, suffix, hSplit, hTrace, hTrace.successful rfl⟩
  · refine drainCompleteFromWriteback hp hX hg hCTA hTotal hBatch hHead hTile ready.ordinals hAt
      (fun lane hl => (hGuardFacts lane hl).1) (fun lane hl => (hGuardFacts lane hl).2.1)
      (fun lane hl => (hGuardFacts lane hl).2.2.1) (fun lane hl => (hGuardFacts lane hl).2.2.2.1)
      ?_ hRun hProtected
    intro lane hl
    have hs := hGuardFacts lane hl
    have hf : Holds (ready.state lane).regs (F lane) := hs.2.2.2.2.2.2
    have hCtaLane : warpLane l g lane / l.block = cta :=
      (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
    exact ⟨hs.2.2.2.2.2.1, holds_mem hf (by simp [F, schedulerStartupFrame, hCtaLane]),
      holds_mem hf (by simp [F, schedulerStartupFrame]), hs.2.2.2.2.1, trivial⟩

/-- A covered first group takes the actual warp from startup through output issue and exit. -/
theorem warp13FirstIntervalOutput {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hComplete : Complete l X) {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13)
    (hFirst : g / l.block < tilePrefix p (min p.batch 31) * p.heads)
    (hProtected : DrainCuQProtected p X) :
    Warp13IssuedOutput p l X g (g / l.block) ∧
      (∀ lane < 32, (X.tr (warpLane l g lane)).getLast? = some ⟨9205, .exit⟩) ∧
      Thread.OutputLaterDrainCuQWords p l X g := by
  obtain ⟨cur⟩ := warp13FirstGroupCutoff hp hX hComplete hg hw (fun lane _ => hProtected lane)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hFrame := fun lane (_ : lane < 32) => schedulerStartupFramed p l (warpLane l g lane)
  have hCta (lane : Nat) (hl : lane < 32) :
      (1072, b32 (g / l.block)) ∈ schedulerStartupFrame p l (warpLane l g lane) := by
    have hIndex : warpLane l g lane / l.block = g / l.block :=
      (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
    simp [schedulerStartupFrame, hIndex]
  obtain ⟨atGroup⟩ := cur.enterSelection hp hFirst hFrame hCta
  have hLow : tilePrefix p 0 * p.heads ≤ g / l.block := by
    simp only [tilePrefix, Finset.range_zero, Finset.sum_empty, Nat.zero_mul, Nat.zero_le]
  exact warp13OutputOfInterval hp hX hg hLow (by simpa only [Nat.zero_add] using hFirst)
    hProtected atGroup

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
