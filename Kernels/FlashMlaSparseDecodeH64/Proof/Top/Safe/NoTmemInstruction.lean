-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaResults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvAElem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaCollector
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Foot
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Issue
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers

@[expose] public section

/-! # ERR-TC-MMA: MMA and copy instances are valid

The safety class of Core's `Unsafe` this file owns (`TcMma.InstructionUnsafe`).
`Safe.W0TraceValid` is the validity of warpgroup 0's trace, proved by `Safe.w0TraceValid`;
`Safe.completed` (`Top/Safe/Completed.lean`) proves the completed MMAs' values from it, and
`Safe.noTmemInstruction` proves the class from those. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The validity of warpgroup 0's trace**, proved by `Safe.w0TraceValid` (the joint
induction `Safe.w0Joint`). -/
structure Safe.W0TraceValid (P : Params) (L : Launch) (mem0 : Mem0) : Prop where
  /-- The words of warpgroup 0's loop are valid (`W0Trace`, `Iface/W0Epi.lean`): the rescale
  stores' words (`w0_rescale_step`) are then numbers when the accumulator words they scale are. -/
  w0Trace : ∀ X, Consistent L kernel Assumptions.all mem0 X → Follow P L X → ¬ HasUb X →
    ∀ g, MbarRow.warp L g < 4 → W0Trace P X g

/-- **Every MMA issue passes its checks**: an MMA event is the MMA warp's (`TmRace.mma_on`) and
its row states its descriptors. -/
theorem Safe.issueShape (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) : TcMma.IssueShape L i d s mask := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨-, ⟨⟨-, hlo, hhi⟩, -⟩, -⟩ := TmRace.mma_on hX (tmem_rows hp hX hFw) he
  exact mma_issueShape hp hX hFw he ⟨hlo, hhi⟩

/-- **Every copy issue passes its checks.** -/
theorem Safe.copySafe (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {i : EvId} {c : TcCopy.Spec} (hi : X.CpIssue i c) : TcMma.CopySafe c := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  rcases TmRace.tc_role (tmem_rows hp hX hFw) hg he rfl with ⟨-, hW⟩ | ⟨⟨-, hlo, hhi⟩, hM⟩ |
    ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · exact mma_cpSafe hp hX hFw he ⟨hlo, hhi⟩
  · cases hc'

/-- **ERR-TC-MMA**: MMA and copy instances are valid. -/
theorem Safe.noTmemInstruction (hp : Pre P L mem0) {X : Execution}
    (hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask →
      TcMma.CompletedValues L Assumptions.all X i)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ TcMma.InstructionUnsafe L Assumptions.all X :=
  fun hU => hU ⟨fun _ _ _ _ _ hi => ⟨Safe.issueShape hp hX hFw hi,
    hCV _ _ _ _ _ hi⟩, fun _ _ hi => Safe.copySafe hp hX hFw hi,
    collectorSafe_mma hX⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
