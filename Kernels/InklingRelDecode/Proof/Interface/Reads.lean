-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Facts

@[expose] public section

/-!
# What the input reads return

No write of an execution covers a byte of an input (`ThreadFacts.write_in_arrays` with
`Pre.outputsApart`), so a read of an input byte returns the byte of the launch
(`Consistent.launch_byte`): `read_launch_byte`. Every address in `Params.reads` is an initialized
launch byte (`reads_mem0`); its value is the one `Pre.qInput`, `relInput`, `kvInput`, `cuInput`,
`seqInput`, `btInput` give (`P.q`, `P.rel`, `P.kv`, `P.qStart`, `P.seqK`, `P.page`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every address the kernel reads is an initialized launch byte.** -/
theorem reads_mem0 (hpre : Pre Q L mem0) {a : Nat} (h : Q.reads a) :
    ∃ c, mem0 ⟨.global, 0, a⟩ = some (some c) := by
  rcases h with ⟨r, hr, t, ht, hh, hhd, d, hd, b, hb, rfl⟩ |
    ⟨r, hr, t, ht, hh, hhd, c, hc, b, hb, rfl⟩ |
    ⟨r, hr, s, hs, kvh, hk, i, hi, c, hc, b, hb, rfl⟩ | ⟨r, hr, k, hk, rfl⟩ |
    ⟨r, hr, k, hk, rfl⟩ | ⟨r, hr, s, hs, k, hk, rfl⟩
  · exact ⟨_, hpre.qInput r hr t ht hh hhd d hd b hb⟩
  · exact ⟨_, hpre.relInput r hr t ht hh hhd c hc b hb⟩
  · exact ⟨_, hpre.kvInput r hr s hs kvh hk i hi c hc b hb⟩
  · exact ⟨_, hpre.cuInput r hr k hk⟩
  · exact ⟨_, hpre.seqInput r hr k hk⟩
  · exact ⟨_, hpre.btInput r hr s hs k hk⟩

/-- **A read of an input byte returns the launch byte**: no write of the execution covers it. -/
theorem read_launch_byte (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {e : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)}
    (hr : X.MemReads e a bs) (hsp : a.loc.space = .global) (hcta : a.loc.cta = 0) {k : Nat}
    (hk : k < a.size)
    (hrd : Q.reads (a.loc.at k).addr) :
    ∃ c, mem0 (a.loc.at k) = some (some c) ∧ bs[k]? = some (some c) := by
  have hloc : (a.loc.at k).space = .global := hsp
  have heq : a.loc.at k = ⟨.global, 0, (a.loc.at k).addr⟩ := by
    simp only [Loc.at, hsp, hcta]
  obtain ⟨c, hc⟩ : ∃ c, mem0 (a.loc.at k) = some (some c) := by
    obtain ⟨c, hc⟩ := reads_mem0 hpre hrd
    exact ⟨c, by rw [heq]; exact hc⟩
  refine ⟨c, hc, hX.launch_byte hr hk ?_ hc⟩
  intro w a' bs' hw hcov
  have hsp' : a'.loc.space = .global := hcov.1.symm.trans hloc
  have hap := hpre.outputsApart _ hrd
  rcases hf.write_in_arrays hw hsp' hcov with h | h
  · exact hap.1 h
  · exact hap.2 h

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
