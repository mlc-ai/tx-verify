-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.BaseWEarly
public import Kernels.InklingRelDecode.Proof2.Lib.WriteCta
public import Lemmas.Flow.CommitTarget

@[expose] public section

/-!
# A thread's shared writes are in its own CTA, whatever its machine follows

Every shared-memory write of an instruction of the code is in the thread's own CTA
(`code_write_cta`, `BaseWDyn.lean`). So is every shared-memory write event of a thread, also at an
event its machine no longer follows: such an event is still fired from a thread state at an
instruction of the code (`Code.fired_op`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A thread's shared-memory write is in its own CTA**, at any event of its trace. -/
theorem thread_write_cta (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {dst : Acc}
    {bs : List Byte} (hw : X.MemWrites (.thread (g, k)) dst bs)
    (hsp : dst.loc.space = .shared) : dst.loc.cta = g / L.block := by
  obtain ⟨pc, hget⟩ : ∃ pc, X.get (g, k) = some ⟨pc, .wr dst bs⟩ := by
    rcases hw with ⟨pc, hh⟩ | ⟨old, pc, hh⟩
    · exact ⟨pc, hh⟩
    · exact absurd hh (no_rmw hX)
  rcases Frame.fired hS hX hget with ⟨σ, o, -, hF⟩ | ⟨-, pc', f, h⟩
  · rcases Code.fired_op hF with ⟨pc', f, h⟩ | ⟨t, ins, hc, hf⟩
    · cases h
    · exact code_write_cta hc hf hsp
  · cases h

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
