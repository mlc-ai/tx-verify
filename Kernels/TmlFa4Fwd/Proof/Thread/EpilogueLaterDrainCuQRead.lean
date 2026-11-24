-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputLaterDrainCuQReadClass
public import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputLaterDrainCuQReadClass

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof Epilogue

noncomputable section

/-- All subsequent output-drain lookups in the warp address launch words. -/
def OutputLaterDrainCuQWords (p : Params) (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ lane < 32, ∀ j a bytes,
    OutputLaterDrainCuQRead X (warpLane l g lane, j) a bytes →
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4}

private theorem laterDrainBranchFloor :
    (kernel.code.drop 3032).all (fun i => staysPastEvent 3032 i.op) = true := by
  decide +kernel

/-- The first drain's recorded down shuffle precedes every subsequent lookup. -/
theorem OutputLaterDrainCuQRead.afterFirstShuffle {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g start j : Nat} {e : Event} {a : Acc} {bytes : List (Option Byte)}
    (hFirst : X.get (g, start) = some e) (hSite : e.pc = 2990)
    (hRead : OutputLaterDrainCuQRead X (g, j) a bytes) : start < j := by
  have hSeg : Assumptions.swExp2Sites.all (fun site =>
      match PTX.Assumption.cuteExp2.matchAt kernel site with
      | some seg => decide (3032 ≤ seg.stop)
      | none => false) = true := by decide +kernel
  exact traceOrderOfPcFloor hX laterDrainBranchFloor hSeg hFirst hRead.get_eq
    (by rw [hSite]; decide) (show 3032 ≤ 3043 by decide)

/-- The decoded suffix after the drain search cannot revisit a later lookup. -/
theorem noLaterCuQAfterSearch {l : Launch} {X : Execution} {g pos j : Nat}
    {t : TState} (ht : t.pc = 3086)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none)
    (hj : pos ≤ j) {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g, j) = some ⟨3043, .rd a bytes⟩) : False := by
  have hCode : (kernel.code.drop 3086).all
      (fun ins => Thread.staysPastEvent 3086 ins.op) = true := by decide +kernel
  have hSeg : Assumptions.swExp2Sites.all (fun site =>
      match PTX.Assumption.cuteExp2.matchAt kernel site with
      | some seg => decide (3086 ≤ seg.stop)
      | none => false) = true := by decide +kernel
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
  have hMem : (⟨3043, .rd a bytes⟩ : Event) ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := j - pos)
    rw [List.getElem?_drop, Nat.add_sub_of_le hj]
    exact he
  have hFloor := Thread.eventTailEventsOfSegmentFloor hCode (fun site _ hm seg hMatch => by
    have h := List.all_eq_true.mp hSeg site hm
    rw [hMatch] at h
    exact of_decide_eq_true h) hWalk ht.ge _ hMem
  exact (by decide : ¬ 3086 ≤ 3043) hFloor

end
end PTX.Kernels.TmlFa4Fwd.Thread
