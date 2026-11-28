-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Guarded
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode
public import Lemmas.Flow.WriteBytes

@[expose] public section

/-! # A covering write has a byte at every place it covers

Every write of the decoded program writes as many bytes as its access is wide (a static scan,
`sizedWrite`); the asynchronous writes are the tensor loads' and stores' single bytes (the program
makes no atomic, no bulk copy and no cancellation request). The form is tml-fa4's
(`Protocol/Operands.lean`'s `wbyte_of_write`), restated on this kernel's program: the second half
of `Step.StoreDone.VisibleReadSources`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

private theorem sizedCode :
    kernel.code.all (fun i => !writeOp i.op || sizedWrite i.op) = true := by
  decide +kernel

/-- **A covering write has a byte at the place.** -/
theorem wbyte_of_write (hX : Consistent l kernel A m X) {w : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte} {lc : Loc} (hw : X.MemWrites w a bs) (hc : a.Covers lc) :
    ∃ v, wbyte a bs lc = some v := by
  have hlen : bs.length = a.size → ∃ v, wbyte a bs lc = some v := fun h => by
    obtain ⟨-, -, h1, h2⟩ := hc
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  apply hlen
  rcases w with ⟨g, k⟩ | ⟨i, part⟩
  · rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    · rcases get_source hX he with ⟨_, hu⟩ | ⟨t, ins, o, -, hcode, hf⟩
      · cases hu
      have h := List.all_eq_true.mp sizedCode ins (List.mem_of_getElem? hcode)
      rw [fires_write_op hf rfl] at h
      exact fires_write_length hf rfl (by simpa using h)
    · exact (noAtomicEvent hX he).elim
  · cases part
    case async.writeStore x y z =>
      obtain ⟨_, _, b, -, -, -, -, hs, rfl, -⟩ := hw
      rw [hs]; rfl
    case async.writeLoad x y z =>
      obtain ⟨_, _, b, -, -, -, -, hs, rfl, -⟩ := hw
      rw [hs]; rfl
    case async.writeCopy =>
      obtain ⟨s, hcp, -⟩ := hw
      exact (noCopy hX hcp).elim
    case async.writeElem j =>
      obtain ⟨s, hcp, -⟩ := hw
      exact (noCopy hX hcp).elim
    case async.writeCta =>
      obtain ⟨s, _, hi, -⟩ := hw
      exact (noClcIssue hX hi).elim
    all_goals exact hw.elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
