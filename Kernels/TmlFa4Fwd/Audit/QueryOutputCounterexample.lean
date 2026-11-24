-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.SpecWitness
public import Kernels.TmlFa4Fwd.Assumptions.WellFormed
public import Kernels.TmlFa4Fwd.Proof.Safety.QueryOutputOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.LseAddressRange
import Kernels.TmlFa4Fwd.Proof.Thread.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Audit
open PTX Epilogue Correction

private theorem outputDestinationAboveBase {s : TensorStore.Spec}
    {x y k : Nat} {loc : Loc} (h : TensorStore.writeLoc s x y k = some loc) :
    s.descriptor.base ≤ loc.addr := by
  obtain ⟨slot, _, hSlot⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨address, hAddress, rfl⟩ := Option.map_eq_some_iff.mp hSlot
  unfold TensorBox.globalAddress TensorTransfer.globalAddress TensorAddress.lookup at hAddress
  split at hAddress
  · cases hAddress
    simp only [TensorAddress.byteAddress, TensorDescriptor.geometry]
    omega
  · cases hAddress

/-- The high-address audit layouts protect every CuQ byte even in a partial execution. -/
theorem cuQProtectedOfHighOutputBases {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : p.cuQBase + 4*p.batch + 3 < 137438953472)
    (hBase : p.lseBase = 274877906944) (hStride : p.lseStride = 274877906944)
    (hOutput : 137438953472 ≤ p.oMap.base) : DrainCuQProtected p X := by
  intro i hi k hk w a bytes hw hCover
  have hGlobal : a.loc.space = .global := hCover.1.symm
  have hCover' : a.loc.addr ≤ p.cuQBase + 4 * i + k := hCover.2.2.1
  have hLow : 137438953472 ≤ a.loc.addr := by
    rcases Thread.globalWriteSource hX hw.intent hGlobal with
      ⟨_, _, _, he⟩ | ⟨j, x, y, byte, addr, spec, _, hIssue, hAt, _⟩
    · exact Thread.Correction.lseWriteAddressLower hp hX
        hBase hStride he hGlobal
    · have hDescriptor := (OutputWarp.storeDescriptor hp hX hIssue).2
      have hDst := outputDestinationAboveBase hAt
      rcases spec with ⟨⟨outer, descriptor, origin, base, rows⟩, reduction⟩
      change (⟨outer, descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
        ⟨3, p.oMap⟩ at hDescriptor
      cases hDescriptor
      exact hOutput.trans hDst
  omega

private theorem isolatedCuQProtected {m : Mem0} {X : Execution}
    (hp : Pre isolatedParams isolatedLaunch m)
    (hX : Consistent isolatedLaunch kernel Assumptions.all m X) :
    DrainCuQProtected isolatedParams X := by
  apply cuQProtectedOfHighOutputBases hp hX _ isolatedAddresses.2.1 isolatedAddresses.2.2.1
    isolatedAddresses.2.2.2
  rw [isolatedAddresses.1, isolatedSchedule.2.1]
  decide

private theorem isolatedOutputFrame {m : Mem0} {X : Execution}
    (hp : Pre isolatedParams isolatedLaunch m)
    (hX : Consistent isolatedLaunch kernel Assumptions.all m X) :
    OutputFootprint isolatedParams X :=
  (outputIntentFootprint hp hX).performed

private theorem isolatedActiveZero :
    0 < isolatedLaunch.grid ∧
      0 < tilePrefix isolatedParams isolatedParams.batch * isolatedParams.heads := by
  obtain ⟨hGrid, hBatch, hHeads, hFirst, hSecond⟩ := isolatedSchedule
  constructor
  · rw [hGrid]; decide
  · simp [tilePrefix, requestTiles, Finset.sum_range_succ, hBatch, hHeads, hFirst, hSecond]

/-- The original proxy and completion order left this mixed-footprint access pair unordered
on a legal isolated launch. This audit uses the base relation before the operand handoff. -/
theorem isolatedLegacyQueryOutputConflict {m : Mem0} {X : Execution}
    (hp : Pre isolatedParams isolatedLaunch m)
    (hX : Consistent isolatedLaunch kernel Assumptions.all m X)
    (hDone : Complete isolatedLaunch X) :
    Safety.LegacyQueryOutputConflict isolatedLaunch X :=
  Safety.queryOutputLegacyConflictOfComplete hp hX hDone (isolatedOutputFrame hp hX)
    isolatedActiveZero.1 isolatedActiveZero.2

/-- The original Q/output reuse pair is ordered at each byte of the first output element. -/
theorem isolatedQueryOutputOrdered {m : Mem0} {X : Execution}
    (hp : Pre isolatedParams isolatedLaunch m)
    (hX : Consistent isolatedLaunch kernel Assumptions.all m X)
    (hDone : Complete isolatedLaunch X) {offset : Nat} (hOffset : offset < 4) :
    ∃ input writer spec x y k loc,
      Safety.QueryOutputReuse isolatedParams isolatedLaunch X input writer spec 0 0 ∧
      loc = (outputElementAccess isolatedLaunch writer.1 0 0 0 0).loc.at offset ∧
      TensorCopy.writeLoc spec x y k = some loc ∧
      X.AsyncPresent input (.write (.load x y k)) ∧
      ByteCausality isolatedLaunch X loc
        (.async input (.write (.load x y k))) (.thread writer) := by
  obtain ⟨input, writer, spec, x, y, k, loc, reuse, atOffset, address, _, present, order, _⟩ :=
    Safety.queryOutputByteOrderOfComplete hp hX hDone (isolatedOutputFrame hp hX)
      isolatedActiveZero.1 isolatedActiveZero.2 hOffset
  exact ⟨input, writer, spec, x, y, k, loc, reuse, atOffset, address, present, order⟩

end PTX.Kernels.TmlFa4Fwd.Audit
