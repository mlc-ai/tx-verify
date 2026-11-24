-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailPvProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaDescriptorAbi
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Epilogue Prologue

private theorem tailLowerStep {l : Launch} {g : Nat} {t u : TState} {e : Option Event}
    (h : 1904 ≤ t.pc) (hs : WStep kernel Assumptions.all l g t e u) : 1904 ≤ u.pc :=
  Thread.eventTailStepOfAudit
    (by set_option maxRecDepth 100000 in kernel_rfl) (by kernel_rfl) h hs

private theorem tailUpperStep {l : Launch} {g : Nat} {t u : TState} {e : Option Event}
    (h : 2768 ≤ t.pc) (hs : WStep kernel Assumptions.all l g t e u) : 2768 ≤ u.pc :=
  Thread.eventTailStepOfAudit
    (by set_option maxRecDepth 100000 in kernel_rfl) (by kernel_rfl) h hs

private theorem outputBaseStep {l : Launch} {g : Nat} {t u : TState} {e : Option Event}
    (hLo : 1904 ≤ t.pc) (hHi : t.pc < 2768) (hs : WStep kernel Assumptions.all l g t e u) :
    u.regs 6495 = t.regs 6495 := by
  refine mmaStepReg hLo hHi (fun i hi => ?_) hs
  have hAll : ((kernel.code.drop 1904).take 864).all (fun i => !(mmaWrites i.op).contains 6495) =
      true := by set_option maxRecDepth 100000 in kernel_rfl
  have hGet : ((kernel.code.drop 1904).take 864)[t.pc-1904]? = some i := by
    rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]
    exact hi
  simpa using List.all_eq_true.mp hAll i (List.mem_of_getElem? hGet)

private theorem upperFloorOfReach {l : Launch} {g : Nat} {a u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g a events u) (ha : 2768 ≤ a.pc) : 2768 ≤ u.pc := by
  induction h with
  | refl => exact ha
  | tau hStep _ ih => exact ih (tailUpperStep ha (.inl ⟨rfl,hStep⟩))
  | event hStep _ ih => exact ih (tailUpperStep ha (.inr ⟨_,rfl,hStep⟩))

private theorem outputBaseStable {l : Launch} {g : Nat} {t u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g t events u) (hLo : 1904 ≤ t.pc)
    (hHi : u.pc < 2768) : u.regs 6495 = t.regs 6495 := by
  induction h with
  | refl => rfl
  | @tau a b _ _ hStep hTail ih =>
    let w : WStep kernel Assumptions.all l g a none b := .inl ⟨rfl,hStep⟩
    have ha : a.pc < 2768 := Nat.lt_of_not_ge fun bad =>
      (Nat.not_le_of_lt hHi) (upperFloorOfReach (.tau hStep hTail) bad)
    exact (ih (tailLowerStep hLo w) hHi).trans (outputBaseStep hLo ha w)
  | @event a b _ _ _ hStep hTail ih =>
    let w := (.inr ⟨_,rfl,hStep⟩ : WStep kernel Assumptions.all l g a (some _) b)
    have ha : a.pc < 2768 := Nat.lt_of_not_ge fun bad =>
      (Nat.not_le_of_lt hHi) (upperFloorOfReach (.event hStep hTail) bad)
    exact (ih (tailLowerStep hLo w) hHi).trans (outputBaseStep hLo ha w)

/-- The returned opening tail election retains the stage-zero completion barrier base
from the earlier actual descriptor startup. -/
theorem OpeningTailFirstPvElected.outputBase {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {ends : Nat → Option TState} (c : OpeningTailFirstPvElected l X g shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    (c.cursor.state lane).regs 6495 = some (b32 (l.sharedBase+144)) := by
  let thread := warpLane l g lane
  have hSame := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  obtain ⟨t,_,_,he,_,ht,hRecorded,_⟩ :=
    schedulerAbiAtDescriptorWithOrdinal hp hMax hSame.1.2.1 (hSame.2.symm.trans hw)
  obtain ⟨_,hElect⟩ := c.elected lane hl
  have hPrior := Thread.traceOrderOfPcFloor hMax.1 (floor := 1917)
    (by set_option maxRecDepth 100000 in kernel_rfl) (by kernel_rfl) he hElect
    (by change 1916 < 1917; decide) (by change 1917 ≤ 2562; decide)
  change descriptorShufflePos (laneOf l thread) < c.cursor.pos lane - 1 at hPrior
  let n := descriptorShufflePos (laneOf l thread)+1
  have hBound : n ≤ c.cursor.pos lane := by
    change descriptorShufflePos (laneOf l thread)+1 ≤ c.cursor.pos lane
    omega
  let pre := (X.tr thread).take (c.cursor.pos lane)
  have hSplit := List.take_append_drop n pre
  rw [show pre.take n = (X.tr thread).take n from by
    dsimp [pre]; rw [List.take_take,Nat.min_eq_left hBound]] at hSplit
  have hPrefix : Run kernel Assumptions.all l thread {} pre (some (c.cursor.before lane)) :=
    c.cursor.recorded lane hl
  rw [← hSplit] at hPrefix
  have hRest := hRecorded.after_returned_prefix hPrefix
  have hReach := hRest.returning_reach.append (TraceReach.of_local (c.cursor.localSteps lane hl))
  have hBase : t.regs 6495 = some (b32 (l.sharedBase+144)) :=
    holds_mem ht.2.2.2.2 (by simp [entryFacts,startupFacts])
  exact (outputBaseStable hReach (by rw [ht.1]; decide)
    (by rw [(c.cursor.checkpoint lane hl).1]; decide)).trans hBase

end PTX.Kernels.TmlFa4Fwd.Mma
