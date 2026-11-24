-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions.SharedBits
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Audit
open PTX Assumptions

/-- Each selected xor writes the next generic output staging pointer. -/
theorem sharedSwizzleXor_matches (k : Fin 8) :
    sharedSwizzleXorSites.contains (117 + 4 * k.val) = true ∧
    kernel.code[117 + 4 * k.val]? = some ⟨none,
      .int ⟨.xor, .int .b 64, false, [some (2992 + k.val)],
        [.reg (3116 + 3 * k.val), .reg (3114 + 3 * k.val)]⟩⟩ := by
  fin_cases k <;> constructor <;> kernel_rfl

/-- Each vector store addresses the same generic pointer register with its tile's displacement. -/
theorem stageStore_usesSwizzle (j : Fin 4) (k : Fin 8) :
    (match kernel.code[[1331, 1491, 1649, 1806].getD j.val 0 + k.val]? with
      | some ⟨none, .mem m⟩ =>
        m.kind == .store && m.space.isNone && m.elem == .int .b 32 && m.vec == 4 &&
          m.addr.base == .reg (2992 + k.val) 64 &&
          m.addr.off == ([0, 8192, 32768, 40960] : List Int).getD j.val 0
      | _ => false) = true := by
  fin_cases j <;> fin_cases k <;> kernel_rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Audit
