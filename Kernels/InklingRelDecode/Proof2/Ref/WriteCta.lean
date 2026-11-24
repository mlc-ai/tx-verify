-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Common.Sound
public import Kernels.InklingRelDecode.Proof2.Lib.WriteCta
public import Lemmas.Flow.CommitTarget
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.NotBulk
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Every thread write is a store into its own CTA when it is shared

The kernel has no atomic (`no_rmw`), so a thread's memory write is a store, and a store of the
code into shared memory is in the thread's own CTA (`Proof2/Lib/WriteCta.lean`,
`code_write_cta`). An event of a thread is fired from a thread state at an instruction of the
code whether or not its machine follows it (`Code.fired_op`), so this holds at every event of
every thread (`thread_write_cta`), with no following and no source. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem kernel_noAtomic : kernel.code.all (fun ins => !atomicOp ins.op) = true := by
  decide +kernel

/-- The kernel has no atomic: no event is a read-modify-write. -/
theorem no_rmw (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {pc : Nat} {a : Acc}
    {old : List (Option Byte)} {new : Option (List Byte)} :
    X.get i ≠ some ⟨pc, .rmw a old new⟩ :=
  fun he => no_kind_of_code hX atomicOp (fun k => ∃ a o n, k = .rmw a o n)
    (fun _ ⟨_, _, _, h⟩ => by cases h) (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk)
    kernel_noAtomic he ⟨_, _, _, rfl⟩

/-- **A thread's memory write is a store, and in shared memory it is in its own CTA.** -/
theorem thread_write_cta (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k : Nat} {dst : Acc} {bs : List Byte} (hw : X.MemWrites (.thread (g, k)) dst bs) :
    (∃ pc, X.get (g, k) = some ⟨pc, .wr dst bs⟩) ∧
      (dst.loc.space = .shared → dst.loc.cta = g / L.block) := by
  obtain ⟨pc, hget⟩ : ∃ pc, X.get (g, k) = some ⟨pc, .wr dst bs⟩ := by
    rcases hw with ⟨pc, hh⟩ | ⟨old, pc, hh⟩
    · exact ⟨pc, hh⟩
    · exact absurd hh (no_rmw hX)
  refine ⟨⟨pc, hget⟩, fun hsp => ?_⟩
  rcases Frame.fired (C := thread Q L) (fun g hg => thread_sound hp hg) hX hget with
    ⟨σ, o, -, hF⟩ | ⟨-, pc', f, h⟩
  · rcases Code.fired_op hF with ⟨pc', f, h⟩ | ⟨t, ins, hc, hf⟩
    · cases h
    · exact Proof.Interface.code_write_cta hc hf hsp
  · cases h

end
end PTX.Kernels.InklingRelDecode.Proof2
