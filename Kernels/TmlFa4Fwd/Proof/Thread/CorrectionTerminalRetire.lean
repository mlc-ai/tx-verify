-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalIndex
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalLoopSearch
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalDrainStart
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
import Kernels.TmlFa4Fwd.Flow.Code.Part120
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- An actual correction arrival at the allocator rendezvous and its lane continuation. -/
structure TerminalCorrectionArrived (l : Launch) (X : Execution) (g : Nat) where
  index : Nat
  state : TState
  ending : Option TState
  arrival : FinalAllocationArrival X (g,index) .arrive
  ready : At state 9205 []
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take (index+1)) (some state)
  remaining : Run kernel Assumptions.all l g state ((X.tr g).drop (index+1)) ending

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- The selected group completes its last warp operations and waits for the actual
output release before correction arrives at the allocator rendezvous. -/
theorem terminalCorrectionArrivesOfSelectedGroup (hMax : Maximal l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} (hg : g < l.threads) (hFirst : first < p.batch)
    (hLo : tilePrefix p first*p.heads ≤ g/l.block) (hHi : g/l.block < terminalCutoff p first)
    {ends : Nat → Option TState}
    (tails : ∀ lane < 32, Nonempty (LseTailReached p l X (warpLane l g lane) batch))
    (cur : SchedulerWarpReached l X g 9187
      (fun lane => terminalSelectedFrame p l (warpLane l g lane) first) shuffles votes ends)
    (hFree : let log := X.objects (Output.freeObject l (g/l.block) 1)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1) :
    ∀ lane < 32, Nonempty (TerminalCorrectionArrived l X (warpLane l g lane)) := by
  obtain ⟨n,hn,⟨ballot⟩⟩ := terminalSelectedGroupBallot hp hg hFirst hLo hHi tails cur
  obtain ⟨done⟩ := terminalIndexOfMaximal hp hMax hg hn
    (prefixWindow (groupLaneTiles p first) 32) (groupLaneTiles p first) ballot
  intro lane hl
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hWarp := (Step.sameWarp_lane hBlock hg hl).1
  let c := laneCursor done hl
  have hCta : warpLane l g lane/l.block = g/l.block := hWarp.1.2.2.symm
  have hReady :
      let log := X.objects (Output.freeObject l (warpLane l g lane/l.block) 1)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ 0%2 := by
    rw [hCta]
    obtain ⟨s,hs,hPhase⟩ := hFree
    exact ⟨s,hs,by rw [hPhase]; decide⟩
  obtain ⟨j,s,o,he,hs,hPast,hRest⟩ := finalArrivalOfTerminalFree hp hMax hWarp.1.2.1
    (show (0 : Nat) < 2 by decide) hReady c.positive c.bounded c.released
    c.checkpoint c.recorded c.remaining c.localSteps
  exact ⟨⟨j,s,o,he,hs,hPast,hRest⟩⟩

/-- The allocator deallocation releases the correction lane's actual exit. -/
theorem TerminalCorrectionArrived.exitOfDeallocation (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (c : TerminalCorrectionArrived l X g) {d : EvId}
    (hCta : g/l.block = d.1/l.block) (hDealloc : Deallocation X d) :
    Exited X g := by
  have hn : Next kernel Assumptions.all l g c.state c.state .exit := by
    refine ⟨.refl,?_⟩
    rw [epilogue_out_all_eq_nil (by unfold EpiloguePc; rw [c.ready.1]; decide),
      out_event c.ready.2.2.2.1 (by rw [c.ready.1]; exact Flow.code_9205) rfl rfl]
    rfl
  obtain ⟨_,_,he⟩ := c.arrival.decoded
  exact ⟨c.index+1,_,exitAtMaximalCursor hMax hg (by omega) (len_of_get he)
    c.recorded c.remaining hn
    (fun h => c.arrival.releasedOfDeallocation hp hMax.1 hCta h hDealloc),rfl⟩

/-- A correction warp at its first terminal exchange scans all request groups and
records the allocation rendezvous. -/
theorem terminalArrivalsAfterFirstExchange (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {n votes : Nat} {ends : Nat → Option TState}
    (down : SchedulerWarpReached l X g 9091
      (fun lane => (7082,b32 (drainCuQ p (shflSource .down lane 1 31).1)) ::
        terminalFirstFrame p l (warpLane l g lane)) n votes ends) (hCuQ : DrainCuQProtected p X)
    (tails : ∀ lane < 32, Nonempty (LseTailReached p l X (warpLane l g lane) batch))
    (hFree : let log := X.objects (Output.freeObject l (g/l.block) 1)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1) :
    ∀ lane < 32, Nonempty (TerminalCorrectionArrived l X (warpLane l g lane)) := by
  obtain ⟨counts⟩ := terminalFirstCountOfMaximal hp hg down
  obtain ⟨scan⟩ := terminalFirstUpScanOfMaximal hp hMax hg counts
  obtain ⟨total⟩ := terminalGroupTotalOfMaximal (first := 0) hp hMax hg false (by
    intro lane _ x hm
    simp only [terminalFirstCountFrame,RowDrainRole.roots,RowDrainRole.frame,
      RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
      List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide) scan
  have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hb))
  obtain ⟨first,_,hFirst,hLow,hHigh,⟨selected⟩⟩ :=
    terminalGroupSelectedOfMaximal hp hMax hCuQ hg hActive total
  exact terminalCorrectionArrivesOfSelectedGroup hp hMax hg hFirst hLow hHigh tails
    selected hFree

/-- The actual single-visit correction warp scans all request groups and
records the allocation rendezvous. -/
theorem terminalSingleVisitArrivalsOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hCuQ : DrainCuQProtected p X)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*i)).at k))
    (tails : ∀ lane < 32, Nonempty (LseTailReached p l X (warpLane l g lane) batch))
    (hFree : let log := X.objects (Output.freeObject l (g/l.block) 1)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1) :
    ∀ lane < 32, Nonempty (TerminalCorrectionArrived l X (warpLane l g lane)) := by
  obtain ⟨_,_,⟨down⟩⟩ := terminalFirstDownOfMaximal hp hMax hg hw hb hLo hHi hSingle
    hCuQ hUsedK tails
  exact terminalArrivalsAfterFirstExchange hp hMax hg hb hHi down hCuQ tails hFree

end PTX.Kernels.TmlFa4Fwd.Correction
