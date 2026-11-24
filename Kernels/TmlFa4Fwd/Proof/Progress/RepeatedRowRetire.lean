-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedSoftmaxAllocation
public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedCorrectionRetire
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaIdleRendezvous
import Kernels.TmlFa4Fwd.Proof.Progress.MmaAllocationExit
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocatorExit
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxExitFromDeallocation
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationTerminalExit
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread

/-- Both row roles and the allocator exit in a repeated tile after the terminal publications
and relinquish. -/
theorem repeatedRowsAndMmaExitOfTerminals
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hc : cta < l.grid)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch cta).1)
    (rows : TerminalProducerRows p l X cta (Mma.trips p batch (assignedCoordinates p batch cta).1))
    {issuer : Nat} (owner : issuer/l.block = cta) (issues : Mma.TerminalOutputIssues l X issuer)
    (relinquished : Mma.MmaWarpRelinquished l X cta) :
    ∀ g < l.threads, g/l.block = cta → warpIndex l g < 13 → Exited X g := by
  have hSoftmax (g : Nat) (hg : g < l.threads) (hw : warpIndex l g < 8)
      (hSame : g/l.block = cta) : ∃ j, FinalAllocationArrival X (g,j) .arrive := by
    have hSelf : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
    obtain ⟨j,he⟩ := repeatedSoftmaxArrivalsOfRows hp hMax hOutputs hg hw
      hb (hSame.symm ▸ hLo) (hSame.symm ▸ hHi) (hSame.symm ▸ multiple)
      (hSame.symm ▸ rows) (owner.trans hSame.symm) issues
      (laneOf l g) (Nat.mod_lt _ (by decide))
    exact ⟨j,by rwa [hSelf] at he⟩
  have hCorrection (g : Nat) (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
      (hSame : g/l.block = cta) : Nonempty (Correction.TerminalCorrectionArrived l X g) := by
    have hSelf : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
    have h := repeatedCorrectionArrivalsOfRows hp hMax hOutputs hg hw hb
      (hSame.symm ▸ hLo) (hSame.symm ▸ hHi)
      (hSame.symm ▸ multiple) (hSame.symm ▸ TerminalProducerRows.publications hp hMax rows)
      (owner.trans hSame.symm) issues (laneOf l g) (Nat.mod_lt _ (by decide))
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
  have allocatorExit (g : Nat) (hg : g < l.threads) (hw : warpIndex l g = 12)
      (hc : g/l.block = cta) : ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit :=
    mmaExitsOfRelinquishAndArrivals hp hMax hg hw (hFrame.metadataProtected hp).1
      (hc.symm ▸ relinquished) (fun h hh wh hcta => hRows h hh wh (hcta.trans hc))
  obtain ⟨i,⟨site,kind⟩,hi,hKind⟩ := allocatorExit alloc hAlloc hAllocRole hAllocCta
  change kind = .exit at hKind
  subst kind
  obtain ⟨j,_,hj⟩ := mmaDeallocBeforeExit hp hMax.1 hAllocRole hi
  have hDealloc := Deallocation.ofKind hj rfl
  intro g hg hSame hw
  have hCTA : g/l.block = (alloc,j).1/l.block := hSame.trans hAllocCta.symm
  by_cases hSoft : warpIndex l g < 8
  · exact Softmax.exitOfObservedDeallocation hp hMax hg hSoft hCTA hDealloc
  by_cases hCorr : warpIndex l g < 12
  · obtain ⟨c⟩ := hCorrection g hg ⟨by omega,hCorr⟩ hSame
    exact c.exitOfDeallocation hp hMax hg hCTA hDealloc
  have hRole : warpIndex l g = 12 := by omega
  exact allocatorExit g hg hRole hSame

end PTX.Kernels.TmlFa4Fwd.Progress
