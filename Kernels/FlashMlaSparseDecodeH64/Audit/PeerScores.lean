-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions.PeerScores
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Audit

open PTX Assumptions

/-- Each selected widening, shift and merge has the modeled destination and ordered operands.
The two remaining operations of each group are ordinary Core pack and store. -/
theorem peerPack_matches (i : Fin 80) :
    match peerPack (394 + i.val) with
    | none => True
    | some p => kernel.code[394 + i.val]? = some ⟨none, p.op⟩ := by
  fin_cases i <;> first | exact True.intro | kernel_rfl

/-- The final ordinary pack and store use the sixteen bytes in source-score order. -/
theorem peerPack_stores (j : Fin 8) :
    kernel.code[402 + 10 * j.val]? = some ⟨none,
      .move ⟨.pack, .int .b 128, [some (4031 + j.val)],
        [.reg (3183 + 8 * j.val), .reg (3184 + 8 * j.val)]⟩⟩ ∧
    kernel.code[403 + 10 * j.val]? = some ⟨none, .mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 128,
        addr := ⟨.reg (988 + j.val) 32, 0⟩, srcs := [.reg (4031 + j.val)] }⟩ := by
  fin_cases j <;> constructor <;> kernel_rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Audit
