-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningOutputDrain
public import Kernels.TmlFa4Fwd.Proof.Progress.SingleVisitSoftmaxAllocation
public import Kernels.TmlFa4Fwd.Proof.Progress.SingleVisitMmaRetire
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalRetire
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxExitFromDeallocation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread

private theorem singleVisitCorrectionArrivalsOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    ∀ lane < 32, Nonempty (Correction.TerminalCorrectionArrived l X (warpLane l g lane)) := by
  obtain ⟨hCuQ,hUsedK⟩ := (hOutputs X hMax.1).metadataProtected hp
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hTails (lane : Nat) (hl : lane < 32) :
      Nonempty (Correction.LseTailReached p l X (warpLane l g lane) batch) := by
    let thread := warpLane l g lane
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hCta : thread/l.block = g/l.block := hSame.1.2.2.symm
    have hWarp : warpIndex l g = warpIndex l thread := hSame.2
    exact singleVisitCorrectionLseTailOfMaximal hp hMax hOutputs hSame.1.2.1
      (hWarp ▸ hw) hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSingle)
  let output := Thread.Output.outputLane l (g/l.block) 0
  have hCta : output/l.block = g/l.block := by
    dsimp only [output,Thread.Output.outputLane,Fin.val_zero,Nat.add_zero]
    rw [hp.block]
    omega
  have hOutput : output < l.threads :=
    (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).1 (hCta ▸ NamedBar.cta_lt hg)
  have hRole : warpIndex l output = 13 := by
    unfold warpIndex
    dsimp only [output,Thread.Output.outputLane,Fin.val_zero,Nat.add_zero]
    rw [hp.block]
    omega
  have hFree := singleVisitOutputFreePhaseOfMaximal hp hMax hOutputs hOutput hRole
    hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSingle) 1
  rw [hCta] at hFree
  exact Correction.terminalSingleVisitArrivalsOfMaximal hp hMax hg hw hb hLo hHi
    hSingle hCuQ hUsedK hTails hFree

/-- Both row roles and the allocator exit in an actual single-visit trace. -/
theorem singleVisitRowsAndMmaExitOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hc : cta < l.grid)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1) :
    ∀ g < l.threads, g/l.block = cta → warpIndex l g < 13 → Exited X g := by
  have hSoftmax (g : Nat) (hg : g < l.threads) (hw : warpIndex l g < 8)
      (hSame : g/l.block = cta) : ∃ j, FinalAllocationArrival X (g,j) .arrive := by
    have hSelf : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
    obtain ⟨j,he⟩ := singleVisitSoftmaxFinalArrivalsOfMaximal hp hMax hOutputs hg hw
      hb (hSame.symm ▸ hLo) (hSame.symm ▸ hHi) (hSame.symm ▸ hSingle)
      (laneOf l g) (Nat.mod_lt _ (by decide))
    exact ⟨j,by rwa [hSelf] at he⟩
  have hCorrection (g : Nat) (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
      (hSame : g/l.block = cta) : Nonempty (Correction.TerminalCorrectionArrived l X g) := by
    have hSelf : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
    have h := singleVisitCorrectionArrivalsOfMaximal hp hMax hOutputs hg hw hb
      (hSame.symm ▸ hLo) (hSame.symm ▸ hHi)
      (hSame.symm ▸ hSingle) (laneOf l g) (Nat.mod_lt _ (by decide))
    rwa [hSelf] at h
  have hRows (g : Nat) (hg : g < l.threads) (hw : warpIndex l g < 12) (hSame : g/l.block = cta) :
      ∃ j, FinalAllocationArrival X (g,j) .arrive := by
    by_cases h : warpIndex l g < 8
    · exact hSoftmax g hg h hSame
    · obtain ⟨c⟩ := hCorrection g hg ⟨by omega,hw⟩ hSame
      exact ⟨c.index,c.arrival⟩
  let alloc := cta*l.block+384
  have hAllocCta : alloc/l.block = cta := by dsimp only [alloc]; rw [hp.block]; omega
  have hAlloc : alloc < l.threads :=
    (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).1 (hAllocCta ▸ hc)
  have hAllocRole : warpIndex l alloc = 12 := by
    unfold warpIndex
    dsimp only [alloc]
    rw [hp.block]
    omega
  have hFrame := hOutputs X hMax.1
  obtain ⟨j,hDealloc⟩ := singleVisitMmaDeallocatesOfArrivals hp hMax hFrame hAlloc hAllocRole hb
    (hAllocCta.symm ▸ hLo) (hAllocCta.symm ▸ hHi) (hAllocCta.symm ▸ hSingle)
    (fun g hg hw hSame => hRows g hg hw (hSame.trans hAllocCta))
  intro g hg hSame hw
  have hCTA : g/l.block = (alloc,j).1/l.block := hSame.trans hAllocCta.symm
  by_cases hSoft : warpIndex l g < 8
  · exact Softmax.exitOfObservedDeallocation hp hMax hg hSoft hCTA hDealloc
  by_cases hCorr : warpIndex l g < 12
  · obtain ⟨c⟩ := hCorrection g hg ⟨by omega,hCorr⟩ hSame
    exact c.exitOfDeallocation hp hMax hg hCTA hDealloc
  have hRole : warpIndex l g = 12 := by omega
  exact singleVisitMmaExitsOfArrivals hp hMax hFrame hg hRole hb
    (hSame.symm ▸ hLo) (hSame.symm ▸ hHi) (hSame.symm ▸ hSingle)
    (fun g hg hw hEq => hRows g hg hw (hEq.trans hSame))

end PTX.Kernels.TmlFa4Fwd.Progress
