-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemACell
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot

@[expose] public section

/-! # Every A byte of a QK MMA has a Tensor Memory cell

QK MMA `k` (A at column `256 + 8 k`, M 64, `.ws`, 128 rows of 32 bytes) has for each byte
`index < 4096` of its A operand the cell of `qk_aCell_cell` and byte `index % 4` of its word. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmemRow
open PTX

/-- **The A cell of byte `index < 4096` of a QK MMA exists**, with byte position `index % 4`. -/
theorem qk_aCell_ex {L : Launch} {g : Nat} {s : TcMma.OperandSpec} {k index : Nat}
    (hk : k < 16) (hs : MmaOps L g s (some (256 + 8 * k)) qkIdesc) (hi : index < 4096) :
    ∃ cell, TcMma.aCell s index = some (cell, index % 4) := by
  obtain ⟨ha, hd, -⟩ := hs
  have hq := qk_desc
  have ho := qk_desc_ok
  rw [hd] at hq ho
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hq ho
  obtain ⟨hm, hn, hg, hh, hb, hw, hrows⟩ := hq
  obtain ⟨hv, -, -⟩ := ho
  have h1 : (256 + 8 * k) % 2 ^ 16 = 256 + 8 * k := Nat.mod_eq_of_lt (by omega)
  have h2 : (256 + 8 * k) / 2 ^ 16 = 0 := Nat.div_eq_of_lt (by omega)
  simp only [TcMma.aCell, ha, Option.bind_some, hw, hm, hg, hh, hrows, Nat.div_one, h1, h2]
  split
  · exact ⟨_, by
      have : index % 32 % 4 = index % 4 := by omega
      rw [this]⟩
  · rename_i hn
    exfalso
    apply hn
    have hws : s.descriptor.ws = true := by rw [MmaFoot.qkD_eq hd]; rfl
    exact ⟨hv, by omega, by omega, .inr (.inr ⟨hws, by omega, trivial⟩)⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmemRow
