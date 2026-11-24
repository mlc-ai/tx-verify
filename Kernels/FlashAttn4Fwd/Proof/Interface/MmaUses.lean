-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaSmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaSteps

@[expose] public section

/-! # What the thread layer exports for the ring uses the MMAs read

The MMA thread runs, for every score tile `u` (global over its items; `u / n` is the item and
`u % n` the visit, `n = kvBlocks P`), the eight QK MMAs of each stage `st` on Q stage `st` and
the K block of KV ring use `2 u`, and the eight PV MMAs of each stage on the V block of KV ring
use `2 u + 1` (the loader's order: per item the visits `n - 1, …, 0`, K before V). KV ring use
`w` is held in slot `w % 6`; the MMA thread commits once to a slot's empty barrier per use, after
the use's MMAs, and once to Q stage `st`'s empty barrier per item, after the item's QK MMAs of
the stage. So before an MMA its commits to the empty barrier of the slot it reads count the
earlier uses of the slot (`ringCommits`).

The fields are facts of the MMA thread, from its run invariant (`Mma.Counts`: the tile and use
counters, one block of eight MMAs per tile and stage, the commits of the ring uses) and the
constants of its MMA sites (`Mma.qVals`, `Mma.asmVals`):

* **QK uses** (`qk`): QK MMA `j = qkStep` of stage `st` and score tile `u = sCommits` reads
  K step `j` of Q stage `st` and of the K block of an even KV slot `sl` (the descriptors of
  `MmaSmemFacts.qk` at that step); before it the thread committed `u / n` times to the Q stage's
  empty barrier and `c` times to the slot's, with `6 c + sl = 2 u`.
* **PV uses** (`pv`): PV MMA `j = pvStep` of stage `st` and tile `u` (`pPolls = u + 1`) reads K
  step `j` of the V block of an odd KV slot `sl` (the descriptor of `MmaSmemFacts.pv` at that
  step); before it the thread committed `c` times to the slot's empty barrier, with
  `6 c + sl = 2 u + 1`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- Commits of thread `g` to ring barrier `b` of its CTA before its event `k`. -/
def ringCommits (L : Launch) (X : Execution) (g : Nat) (b : FBar) (k : Nat) : Nat :=
  ((X.tr g).take k).countP (commitsTo (b.loc L (ctaOf L g)))

/-- The thread layer's facts for the ring uses and K steps the MMAs read. -/
structure MmaUseFacts (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- QK MMA `qkStep` of stage `st` and score tile `u = sCommits` reads that K step of Q stage
  `st` and of an even KV slot `sl`, after `u / n` commits to the Q stage's empty barrier and
  `c` commits to the slot's, `6 c + sl = 2 u`. -/
  qk : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    {st : Nat} (hst : st < 2), X.MmaIssue i d s acc mask → X.MmaCell i cell → InS st cell →
      ∃ sl : Fin 6, sl.val % 2 = 0 ∧
        s.a = kMajorDesc (qStepStart L ⟨st, hst⟩ (qkStep L X i.1 st i.2)) ∧
        s.b = kMajorDesc (kStepStart L sl (qkStep L X i.1 st i.2)) ∧
        ringCommits L X i.1 (.qEmpty ⟨st, hst⟩) i.2 = sCommits L X i.1 st i.2 / kvBlocks P ∧
        6 * ringCommits L X i.1 (.kvEmpty sl) i.2 + sl.val = 2 * sCommits L X i.1 st i.2
  /-- PV MMA `pvStep` of stage `st` and tile `u` (`pPolls = u + 1`) reads that K step of an odd
  KV slot `sl`, after `c` commits to the slot's empty barrier, `6 c + sl = 2 u + 1`. -/
  pv : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    {st : Nat}, st < 2 → X.MmaIssue i d s acc mask → X.MmaCell i cell → InO st cell →
      ∃ sl : Fin 6, sl.val % 2 = 1 ∧
        s.b = mnMajorDesc (vStepStart L sl (pvStep L X i.1 st i.2)) ∧
        6 * ringCommits L X i.1 (.kvEmpty sl) i.2 + sl.val =
          2 * (pPolls L X i.1 st i.2 - 1) + 1

end
end PTX.Kernels.FlashAttn4Fwd.Proof
