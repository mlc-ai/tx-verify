-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
public import Lemmas.Tcgen05.MmaFinishTmemA

@[expose] public section

/-! # No MMA writes a cell another MMA reads as operand A

The QK MMA `k` reads its A cells in columns `[256 + 8 k, 264 + 8 k)` (`qk_aCell`), below 384,
and the PV MMAs read A from shared memory. The cells an MMA writes (`writer_cases`) are in
columns `[400, 464)` (a QK MMA) or below 256 (a PV MMA), so no MMA's result cell is an A cell:
`TcMma.ATmemApart`, the premise of the MMA completions (`Sched.mma_steps_cpQ`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace TmRace

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An A cell of an MMA is in columns `[256, 384)`.** -/
theorem aCell_range (hX : Consistent L kernel Assumptions.all m X)
    (hR : TmemRows P L X) {e : EvId} {cell : TcMma.Cell} (ha : X.MmaACell e cell) :
    256 ≤ cell.column ∧ cell.column < 384 := by
  obtain ⟨d, s, acc, mask, index, b, ⟨pc, he⟩, hac⟩ := ha
  have hg := Frame.lt_of_get hX he
  rcases tc_role hR hg he rfl with ⟨-, hW⟩ | ⟨-, hM⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, -, h, hops⟩ |
      ⟨_, _, k, -, -, h, -, hops⟩ <;> cases h
    · obtain ⟨-, h1, h2⟩ := TmemRow.qk_aCell hk hops hac
      omega
    · obtain ⟨haT, -⟩ := hops
      simp [TcMma.aCell, haT] at hac
  · cases hc'

/-- **No MMA writes a cell another MMA reads as operand A.** -/
theorem mma_aApart (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hR : TmemRows P L X) : TcMma.ATmemApart X := by
  intro j d s acc mask hj index cell pos hac w d' s' acc' mask' row col hw _ hwc
  obtain ⟨hlo, hhi⟩ := aCell_range hX hR ⟨d, s, acc, mask, index, pos, hj, hac⟩
  obtain ⟨hc, h⟩ := writer_cases hp hX hR (x := w) (cell := cell)
    (.inl ⟨d', s', acc', mask', row, col, hw, hwc⟩)
  obtain ⟨pc, hget⟩ := hw
  rcases h with ⟨k, ⟨pc', s'', hk, hg, -⟩, h1, h2⟩ | ⟨b, ⟨pc', s'', a'', hg, -⟩, hb, -, h1, h2⟩ |
    ⟨k, ⟨pc', c, hk, hg, -⟩, -⟩ | ⟨⟨pc', a, vals, hg, -⟩, -⟩
  · omega
  · omega
  · rw [hget] at hg
    cases hg
  · rw [hget] at hg
    cases hg

end TmRace

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
