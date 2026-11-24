-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Base
public import Lemmas.Flow.LocalLoop

@[expose] public section

/-! The broadcast of the Q descriptor and the entry to the item loop: the first item's Q poll
on the leader CTA; on the odd CTA the item loop, which performs no event, then the end; the end
directly when the cluster has no item. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The first item's state (also the registers on entry to the item loop). -/
abbrev d0 (base : Value) (pro : Nat → Value) : D := ⟨.qWait 0, 0, 0, base, pro⟩

/-- The odd CTA's registers in its item loop, before the test of item `j`: the first item's
values, with the item counter at item `j` and the test's predicate. -/
def valueOdd (L : Launch) (g : Nat) (base : Value) (pro : Nat → Value) (j r : Nat) : Value :=
  ([(3916, b32 (work L g j)), (136, .pred (decide (work L g j < totOf L)))].lookup r).getD
    (valueOf L g (d0 base pro) r)

/-- The facts at the odd CTA's loop test of item `j + 1`. -/
abbrev oddFacts (L : Launch) (g : Nat) (base : Value) (pro : Nat → Value) (j : Nat) :
    List (Nat × Value) :=
  Flow.factsFrom (Flow.live Flow.bra_1115) (valueOdd L g base pro (j + 1))

/-- From the broadcast to the first test (no item). -/
theorem seg_noItem {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (base : Value) (pro : Nat → Value) (i t : Nat) :
    Seg kernel asms L g 18 (Site.shflQ.pc + 1)
      ((860, b32 (qLo L false)) :: facts L g ⟨.shflQ, i, t, base, pro⟩)
      Flow.bra_569 (factsAt L g Flow.bra_569 (d0 base pro)) := by
  intro t h
  mma_seg_s h hpre hg [land16383, lor65536, qLo]

/-- From the test for no item to the selection of the trip count's rounding (`sk` is a
multiple of 128, so the rounding predicate is false). -/
theorem seg_toCeil {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (base : Value) (pro : Nat → Value) :
    Seg kernel asms L g 8 (Flow.bra_569 + 1) (factsAt L g Flow.bra_569 (d0 base pro))
      (Flow.bra_569 + 9) (factsAt L g (Flow.bra_569 + 9) (d0 base pro)) := by
  intro t h
  mma_seg_s h hpre hg

/-- From the rounding to the test for the odd CTA. -/
theorem seg_toTest {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (base : Value) (pro : Nat → Value) :
    Seg kernel asms L g 16 (Flow.bra_569 + 9) (factsAt L g (Flow.bra_569 + 9) (d0 base pro))
      Flow.bra_594 (factsAt L g Flow.bra_594 (d0 base pro)) := by
  intro t h
  mma_seg_s h hpre hg [kvPar, kvSlot, kvUse, pPar]

/-- The odd CTA enters its item loop: the counter steps to item 1 and is tested. -/
theorem seg_oddEntry {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (base : Value) (pro : Nat → Value) (hw : work L g 0 < totOf L) :
    Seg kernel asms L g 2 (Flow.bra_1115 - 2) (factsAt L g Flow.bra_594 (d0 base pro))
      Flow.bra_1115 (oddFacts L g base pro 0) := by
  intro t h
  rw [work_zero] at hw
  mma_seg_s h hpre hg [valueOdd, work_succ, work_zero]

/-- One pass of the odd CTA's item loop: back to the test of the odd CTA, then the counter
steps to the next item and is tested. -/
theorem seg_oddA {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (base : Value) (pro : Nat → Value) (k : Nat) :
    Seg kernel asms L g 1 (Flow.bra_594 - 1) (oddFacts L g base pro k)
      Flow.bra_594 (Flow.factsFrom (Flow.live Flow.bra_594) (valueOdd L g base pro (k + 1))) := by
  intro t h
  mma_seg_s h hpre hg [valueOdd]

theorem seg_oddB {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (base : Value) (pro : Nat → Value) (k : Nat)
    (hw : work L g (k + 1) < totOf L) :
    Seg kernel asms L g 2 (Flow.bra_1115 - 2)
      (Flow.factsFrom (Flow.live Flow.bra_594) (valueOdd L g base pro (k + 1)))
      Flow.bra_1115 (oddFacts L g base pro (k + 1)) := by
  intro t h
  rw [work_succ] at hw
  mma_seg_s h hpre hg [valueOdd, work_succ]

/-- The odd CTA leaves its item loop. -/
theorem seg_oddExit {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (base : Value) (pro : Nat → Value) (k : Nat) :
    Seg kernel asms L g 0 Flow.tmemRelinquish_0 (oddFacts L g base pro k)
      Site.relinquish.pc (facts L g ⟨.relinquish, 0, 0, base, pro⟩) := by
  intro t h
  mma_seg_s h hpre hg [valueOdd]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
