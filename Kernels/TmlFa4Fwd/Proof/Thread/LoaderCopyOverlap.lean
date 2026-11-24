-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.LoaderCopyFootprint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy Prologue
open PTX.Kernels.TmlFa4Fwd.Loader
  (actualCopyAtInLoader loaderCopyPcInPacket packetCopyCoordinates packetPlanePc kvCopyVectorsApart)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Ordinary cache copies are issued only by one of the loader warps. -/
theorem copyLoaderWarp {i : EvId} {s : Spec} (hCopy : X.Copy i s) : 14 ≤ warpIndex l i.1 := by
  obtain ⟨pc, hGet⟩ := hCopy
  obtain ⟨hLo, hHi, hCopyPc⟩ := actualCopyAtInLoader hX hGet
  obtain ⟨site, hStart, hEnd⟩ := loaderCopyPcInPacket hLo hHi hCopyPc
  obtain ⟨pair, upper, rfl⟩ := packetCopyCoordinates site hStart hEnd hCopyPc
  have hNotHint : packetPlanePc site pair upper ∉ registerHintSites := by
    fin_cases site <;> fin_cases pair <;> cases upper <;> decide
  have hRole := roleBodyPcOfEvent hp hX hGet
    (show 173 < packetPlanePc site pair upper by omega) hNotHint
  change roleBodyPc (warpIndex l i.1) (packetPlanePc site pair upper) at hRole
  unfold roleBodyPc at hRole
  rcases hRole with hExit | hBody
  · omega
  · split_ifs at hBody <;> omega

/-- Every actual ordinary copy identifies its CTA-local loader lane, including
a vector issued before its group commits. -/
theorem copyProducer {i : EvId} {s : Spec} (hCopy : X.Copy i s) :
    ∃ lane : Fin 64, i.1 = producer l (i.1 / l.block) lane := by
  have hWarp := copyLoaderWarp hp hX hCopy
  have hLow : 448 ≤ i.1 % l.block := by unfold warpIndex at hWarp; omega
  have hUpper : i.1 % l.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  let lane : Fin 64 := ⟨i.1 % l.block - 448, by omega⟩
  refine ⟨lane, ?_⟩
  change i.1 = i.1 / l.block * l.block + 448 + (i.1 % l.block - 448)
  rw [Nat.mul_comm _ l.block]
  have hDiv := Nat.mod_add_div i.1 l.block
  omega

/-- Two actual copies sharing a byte must use the same loader lane, slot,
vector pair and plane. No publication is needed for this address agreement. -/
theorem overlappingCopiesSameDestination {i j : EvId} {s t : Spec} {loc : Loc} (hCopy : X.Copy i s)
    (hOther : X.Copy j t) (hA : s.dst.Covers loc) (hB : t.dst.Covers loc)
    : i.1 = j.1 ∧ s.dst = t.dst := by
  obtain ⟨_, slot, pair, upper, hDst⟩ := copyDestination hp hX hCopy
  obtain ⟨_, slot', pair', upper', hDst'⟩ := copyDestination hp hX hOther
  rw [hDst] at hA
  rw [hDst'] at hB
  obtain ⟨lane, hi⟩ := copyProducer hp hX hCopy
  obtain ⟨lane', hj⟩ := copyProducer hp hX hOther
  have hDiff : ¬ (slot.val ≠ slot'.val ∨
      (i.1 % l.block) % 64 ≠ (j.1 % l.block) % 64 ∨ pair.val ≠ pair'.val ∨ upper ≠ upper') := by
    intro hNe
    have hApart := kvCopyVectorsApart hp.shared.1 pair.isLt pair'.isLt hNe
    obtain ⟨_, _, hLo, hHi⟩ := hA
    obtain ⟨_, _, hLo', hHi'⟩ := hB
    dsimp at hLo hHi hLo' hHi'
    rcases hApart with h | h <;> omega
  push Not at hDiff
  obtain ⟨hSlot, hLane, hPair, hUpper⟩ := hDiff
  have hLanes : lane = lane' := Fin.ext (by
    rw [hi, hj, producerLaneMod hp, producerLaneMod hp] at hLane
    exact hLane)
  have hCta : i.1 / l.block = j.1 / l.block := hA.2.1.symm.trans hB.2.1
  have hThread : i.1 = j.1 := by
    calc
      i.1 = producer l (i.1 / l.block) lane := hi
      _ = producer l (j.1 / l.block) lane' := by rw [hCta, hLanes]
      _ = j.1 := hj.symm
  refine ⟨hThread, ?_⟩
  rw [hDst, hDst', hThread, Fin.ext hSlot, Fin.ext hPair, hUpper]

/-- Two overlapping issued vectors cannot belong to the same async group. -/
theorem overlappingCopiesSeparateGroups {i j : EvId} {s t : Spec} {loc : Loc} (hCopy : X.Copy i s)
    (hOther : X.Copy j t) (hA : s.dst.Covers loc) (hB : t.dst.Covers loc)
    : ¬ SameAsyncGroup X i j ∧ ¬ SameAsyncGroup X j i :=
  ⟨fun h => PTX.Kernels.TmlFa4Fwd.Loader.sameGroupCopyDestinationsApart hp hX h hCopy hOther
      ⟨loc, hA, hB⟩,
    fun h => PTX.Kernels.TmlFa4Fwd.Loader.sameGroupCopyDestinationsApart hp hX h hOther hCopy
      ⟨loc, hB, hA⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
