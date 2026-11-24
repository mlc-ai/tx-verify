-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.WriteBytes

public section

/-! # Defined bytes of actual writes to shared memory -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.OutputStoreFacts

open PTX PTX.Flow

set_option maxRecDepth 100000 in
private theorem sized_writes :
    OpPcsFast kernel.code (fun op => !sizedWrite op) [] = true := by
  decide +kernel

private theorem thread_write_length {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {a : Acc} {bs : List Byte} (hw : X.Writes i a bs) :
    bs.length = a.size := by
  obtain ⟨_, he⟩ := hw
  rcases Flow.get_source hX he with ⟨_, hk⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hk
  · apply fires_write_length hf rfl
    cases hs : sizedWrite ins.op
    · exact (List.not_mem_nil (OpPcsFast.mem sized_writes hc (by simp [hs]))).elim
    · rfl

/-- Every actual shared-memory writer defines the byte it covers. -/
theorem covered_byte {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {l : Loc}
    (hw : X.MemWrites w a bs) (hc : a.Covers l) (hshared : l.space = .shared) :
    ∃ value, wbyte a bs l = some value := by
  have hlen : bs.length = a.size := by
    rcases Wg2.raw_read_competing_kinds hX hw hc hshared with ⟨_, _, ht⟩ | ⟨_, _, _, _, rfl⟩
    · exact thread_write_length hX ht
    · obtain ⟨_, _, _, _, _, _, _, hsize, rfl, _⟩ := hw
      simpa only [List.length_singleton] using hsize.symm
  have hr : l.addr - a.loc.addr < bs.length := by
    unfold Acc.Covers Loc.InRange at hc
    omega
  exact ⟨bs[l.addr - a.loc.addr], List.getElem?_eq_getElem hr⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.OutputStoreFacts
