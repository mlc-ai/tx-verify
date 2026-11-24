-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlot
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX Correction Loader

/-- Only the second output stage can read a byte staged over a cache vector.
The overlapping copy belongs to one of the first two cache slots in that CTA. -/
theorem cacheOverlap {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue copy : EvId} {address x y k : Nat} {spec : TensorStore.Spec} {s : AsyncCopy.Spec}
    {loc : Loc} (hIssue : X.TensorStoreIssue issue address spec)
    (hRead : TensorStore.readLoc spec x y k = some loc)
    (hCopy : X.Copy copy s) (hCover : s.dst.Covers loc) :
    Thread.Output.ReadyAcquire l X issue 1 ∧ copy.1 / l.block = issue.1 / l.block ∧
      ∃ (slot : Fin 2) (pair : Fin 16) (upper : Bool),
        s.dst = {loc := ⟨.shared, copy.1 / l.block,
          kvCopyAddress l.sharedBase slot (copy.1 % l.block) pair upper⟩, size := 16} := by
  obtain ⟨stage, box, hReady, hx, hy, hk, hLoc⟩ := Thread.Output.actualReadySlot hp hX hIssue hRead
  let g := Thread.Output.sourceLane l issue y
  have hSlot : (outputElementAccess l g stage box x y).Covers loc :=
    hLoc.symm ▸ Acc.covers_at hk
  have hReadRange := Thread.Output.elementStageRange hx hy hSlot
  obtain ⟨_, slot, pair, upper, hDst⟩ := Thread.Loader.copyDestination hp hX hCopy
  have hLower := hCover.2.2.1
  rw [hDst] at hLower
  change kvCopyAddress l.sharedBase slot (copy.1 % l.block) pair upper ≤ loc.addr at hLower
  have hCopyRange := kvCopyAddress_div_1024 hp.shared.1 slot
    (copy.1 % l.block) pair upper
  have hCopyBase : l.sharedBase + 68608 + 32768 * slot.val ≤ loc.addr := by
    have hAlign := hp.shared.1
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] at hCopyRange <;> omega
  have hStage : stage = 1 := Fin.ext (by have := stage.isLt; change stage.val = 1; omega)
  subst stage
  have hCache : slot.val < 2 := by omega
  have hOwner : g / l.block = issue.1 / l.block := by
    unfold g Thread.Output.sourceLane
    rw [hp.block]
    omega
  have hSame : s.dst.loc.cta = g / l.block := hCover.2.1.symm.trans hSlot.2.1
  rw [hDst] at hSame
  exact ⟨hReady, hSame.trans hOwner, ⟨slot.val, hCache⟩, pair, upper, hDst⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
