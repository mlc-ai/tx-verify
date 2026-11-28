-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Cnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab

@[expose] public section

/-! # The `rd` class of the TMA role

The role's class `rd` is the coordinate reads `tmaRd` (a read at a pc of the role). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX

/-- The `rd` class of the role is the TMA coordinate reads. -/
theorem cls_rd (e : Event) : cls .rd e = tmaRd e := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | wait l q ok a sc => cases ok <;> simp [cls, kindOf, inRole, tmaRd]
  | _ => simp [cls, kindOf, inRole, tmaRd]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
