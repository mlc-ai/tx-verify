-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCuQProgress
public import Lemmas.Step.WarpShuffleProgress
import Lemmas.Flow.WarpScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma (firstSchedulerPos descriptorShufflePos firstDownTemplate)

noncomputable section

private theorem schedulerShuffleIssued {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X) :
    ∃ recv ok, X.get (g, firstSchedulerPos p (laneOf l g)) =
      some ⟨1941, .shfl .down (b32 (drainCuQ p (laneOf l g))) 1 31 recv ok⟩ ∧
      X.ShflK (g, firstSchedulerPos p (laneOf l g)) 4 := by
  apply Step.shfl_occurs_of_maximal hMax (by rw [hp.block]) hg
    (fun h => firstSchedulerPos p (laneOf l h))
    (fun h => b32 (drainCuQ p (laneOf l h))) (fun _ => 1) (fun _ => 31)
  · intro h hs
    have hw' : warpIndex l h = 12 := hs.2.symm.trans hw
    obtain ⟨_, _, _, he, _, _, _, _⟩ :=
      TmlFa4Fwd.Mma.schedulerAbiAtDescriptorWithOrdinal hp hMax hs.1.2.1 hw'
    exact .inl (fun hNil => by
      have hLen := len_of_get he
      rw [hNil, List.length_nil] at hLen
      omega)
  · intro h hs
    have hw' : warpIndex l h = 12 := hs.2.symm.trans hw
    obtain ⟨t, u, o, hBound, hCount, hReady, hu, hRun, hl, hTail⟩ :=
      schedulerDownCursor hp hMax hs.1.2.1 hw' hProtected
    exact ⟨t, u, o, (fun v _ => next (setReg u 2456 v)),
      hBound, hCount, hReady, hu.1, hRun, hTail, hl, firstDownTemplate hp hu⟩
  · intro ev h
    exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl (noNewRead_appendLanes h)

/-- The first MMA scheduler shuffle has exchanged each lane's protected launch CuQ word
or its inactive-lane zero with the matching source lane. -/
theorem initialSchedulerShuffled {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .shfl .down
      (b32 (drainCuQ p (laneOf l g))) 1 31
      (b32 (drainCuQ p (shflSource .down (laneOf l g) 1 31).1))
      (shflSource .down (laneOf l g) 1 31).2 ∧ X.ShflK (g,j) 4 := by
  obtain ⟨recv, ok, he, hK⟩ := schedulerShuffleIssued hp hMax hg hw hProtected
  let src := (shflSource .down (laneOf l g) 1 31).1
  let owner := warpLane l g src
  have hl : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hSrc : src < 32 := Step.shflSource_lt .down hl _ _
  obtain ⟨hs, hLane⟩ := Step.sameWarp_lane (by rw [hp.block]) hg hSrc
  have hw' : warpIndex l owner = 12 := hs.2.symm.trans hw
  obtain ⟨other, flag, hf, hKs⟩ := schedulerShuffleIssued hp hMax hs.1.2.1 hw' hProtected
  obtain ⟨hRecv, hOk⟩ := shfl_source_value hMax.1 he hK hf hKs
    (ShflK.not_exited hMax.1 hs.1.2.1 hKs)
  exact ⟨_, _, he, by rw [hRecv, hOk, hLane], hK⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
