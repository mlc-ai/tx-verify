-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions.DeadPack
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Audit
open PTX Assumptions

/-- Every selected move is followed by the unpack that discards the high half, and the combined
word is dead immediately after this unpack. -/
theorem deadPack_discards {site dst lo hi : Nat} (h : deadPackWords site = some (dst, lo, hi)) :
    kernel.code[site]? = some ⟨none, .move ⟨.pack, .int .b 64, [some dst], [.reg lo, .reg hi]⟩⟩ ∧
    (∃ d, kernel.code[site + 1]? =
      some ⟨none, .move ⟨.unpack, .int .b 64, [some d, none], [.reg dst]⟩⟩) ∧
    dst ∉ Flow.live (site + 2) := by
  unfold deadPackWords at h
  split at h
  · cases h
    exact ⟨Flow.code_208, ⟨951, Flow.code_209⟩, by decide +kernel⟩
  · cases h
    exact ⟨Flow.code_712, ⟨1716, Flow.code_713⟩, by decide +kernel⟩
  · contradiction


/-- The fallback pack reads the low operand without reading the unwritten register. -/
theorem deadPack_uses_low {L : Launch} {g : Nat} {t : TState} {dst lo hi : Nat}
    {v : Value} (hs : deadPackWords t.pc = some (dst, lo, hi))
    (hlo : t.regs lo = some v) (hv : v.bytes = 4) :
    deadPackRule L g t (.move ⟨.pack, .int .b 64, [some dst], [.reg lo, .reg hi]⟩) =
      some (.ok (next (setReg t dst (joinValue v (.bits 32 0))))) := by
  simp [deadPackRule, hs, readValue, readReg, hlo, hv, bind, Except.bind, pure, Except.pure]

end PTX.Kernels.FlashMlaSparseDecodeH64.Audit
