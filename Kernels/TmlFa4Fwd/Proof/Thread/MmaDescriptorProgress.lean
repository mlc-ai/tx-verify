-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationReadProgress
public import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.MmaDescriptorStartup
import Lemmas.Step.WarpShfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma (allocationBarrierPos startupQLow startupQWord
  startupQShuffle localRun descriptorShufflePos descriptorSendBeforeEvent
  shuffleAfterAllocation)

noncomputable section

private theorem descriptorNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState}
    (ht : At t 1912 [(1062, b32 12), (2535, b32 l.sharedBase)]) :
    ∃ u, u.pc = 1916 ∧ Next kernel Assumptions.all l g t u
      (.shfl .idx (b32 (startupQLow l)) 0 31 (fun v _ => next (setReg u 2450 v))) := by
  have hBase := ht.2.2.2.2.2.1
  obtain ⟨u, hLocal, hu⟩ := startupQWord hp g t (ht.mono ⟨hBase, trivial⟩)
  have hRun := localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hLocal
  exact ⟨u, hu.1, run_rtg hRun, startupQShuffle hp hu⟩

private theorem descriptorCursorPos (l : Launch) (g : Nat) :
    allocationBarrierPos l g + 2 = descriptorShufflePos (laneOf l g) := by
  unfold allocationBarrierPos descriptorShufflePos
  split <;> decide

private theorem descriptorAtNonempty {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hLen : descriptorShufflePos (laneOf l g) < (X.tr g).length) :
    ∃ recv ok, X.get (g, descriptorShufflePos (laneOf l g)) =
      some ⟨1916, .shfl .idx (b32 (startupQLow l)) 0 31 recv ok⟩ := by
  obtain ⟨t, o, _, ht, _, hTail⟩ := allocatorReadsResultPrefix hp hMax hg hw
  rw [descriptorCursorPos] at hTail
  obtain ⟨u, hPc, hn⟩ := descriptorNext hp ht
  obtain ⟨_, _, he, ⟨recv, ok, rfl, _⟩, _⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp hNil))
  exact ⟨recv, ok, hPc ▸ he⟩

/-- Every maximal allocator warp broadcasts its initial Q descriptor in all lanes. -/
theorem initialDescriptorShuffled {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) :
    ∃ j e recv ok, X.get (g, j) = some e ∧
      e.kind = .shfl .idx (b32 (startupQLow l)) 0 31 recv ok ∧ X.ShflK (g, j) 3 := by
  let pos := descriptorShufflePos (laneOf l g)
  have hlo (h : Nat) (hs : SameWarp l g h) :
      descriptorShufflePos (laneOf l h) ≤ (X.tr h).length := by
    have hw' : warpIndex l h = 12 := hs.2.symm.trans hw
    obtain ⟨_, _, he, _, _, _⟩ := allocatorReadsResultPrefix hp hMax hs.1.2.1 hw'
    rw [← descriptorCursorPos]
    exact len_of_get he
  have hgSame : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
  have hPositive : pos < (X.tr g).length := by
    by_contra! hLow
    have hEq : pos = (X.tr g).length := Nat.le_antisymm (hlo g hgSame) hLow
    have hWarp (h : Nat) (hs : SameWarp l g h) :
        descriptorShufflePos (laneOf l h) = (X.tr h).length := by
      apply Nat.le_antisymm (hlo h hs)
      by_contra! hLong
      have hw' : warpIndex l h = 12 := hs.2.symm.trans hw
      obtain ⟨recv, ok, he⟩ := descriptorAtNonempty hp hMax hs.1.2.1 hw' hLong
      obtain ⟨_, _, _, _, _, hSend, hK, _, _⟩ := descriptorSendBeforeEvent hp hMax.1 he hw'
        (show 1911 < 1916 by decide) (by intro f h; cases h)
      rcases Step.shfl_lane_of_ready hMax.1 hSend hK (sameWarp_symm hs) with
        ⟨j, hk⟩ | ⟨j, site, hExit, _⟩
      · obtain ⟨⟨site, mode, v, x, y, data, valid, hSeen⟩, _⟩ := id hk
        have hLate := shuffleAfterAllocation hp hMax.1 hw hSeen hk
        obtain ⟨_, _, _, _, _, hFound, _, _, _⟩ := descriptorSendBeforeEvent hp hMax.1
          hSeen hw hLate (by intro f h; cases h)
        have hBound : pos < (X.tr g).length := len_of_get hFound
        omega
      · obtain ⟨t, _, _, _, hPrefix, _⟩ := allocatorReadsResultPrefix hp hMax hg hw
        have hRun : Run kernel Assumptions.all l g {} (X.tr g) (some t) := by
          rw [descriptorCursorPos] at hPrefix
          exact (List.take_of_length_le hLow) ▸ hPrefix
        exact hRun.no_exit hExit
    apply hMax.not_grows
    apply Step.shfl_counted_extension hMax.1 (by rw [hp.block]) (fun _ => b32 (startupQLow l))
      (fun _ => 0) (fun _ => 31) hg (pc := 1916) (m := .idx)
    · intro h hs
      exact .inl (fun hNil => by
        have hLen := hlo h hs
        rw [hNil, List.length_nil] at hLen
        unfold descriptorShufflePos at hLen
        split at hLen <;> omega)
    · intro h hs
      have hw' : warpIndex l h = 12 := hs.2.symm.trans hw
      obtain ⟨_, _, he, _, _, _⟩ := allocatorReadsResultPrefix hp hMax hs.1.2.1 hw'
      exact releasedIfLast he (by intro h; cases h) ((descriptorCursorPos l h).trans (hWarp h hs))
    · intro h hs recv ok
      have hw' : warpIndex l h = 12 := hs.2.symm.trans hw
      obtain ⟨t, _, _, ht, hPrefix, _⟩ := allocatorReadsResultPrefix hp hMax hs.1.2.1 hw'
      have hEq' := (descriptorCursorPos l h).trans (hWarp h hs)
      obtain ⟨u, hPc, hn⟩ := descriptorNext hp ht
      have hr : Run kernel Assumptions.all l h {} (X.tr h) (some t) := by
        simpa [hEq'] using hPrefix
      exact ⟨t, u, _, hr, hn.steps, _, hn.stop, recv, ok, by rw [hPc], rfl⟩
    · intro ev h
      exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes h)
  obtain ⟨recv, ok, he⟩ := descriptorAtNonempty hp hMax hg hw hPositive
  obtain ⟨_, r, valid, _, _, hSend, hK, _, _⟩ := descriptorSendBeforeEvent hp hMax.1 he hw
    (show 1911 < 1916 by decide) (by intro f h; cases h)
  exact ⟨_, _, r, valid, hSend, rfl, hK⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
