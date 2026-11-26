-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemLoad
public import Lemmas.Tmem.AccessCp

@[expose] public section

/-! # Every Tensor Memory access is of its thread's CTA, below column 512

From the Tensor Memory rows only (`TmemRows`), the kernel's accesses meet
`Tmem.AccessCp.AccessInfoCp` (`access_info`):

* a write (an MMA's result cell, a copy's cell, a store's cell) is in the writer's CTA, below
  column 464 (`write_info`, from `writer_cases`);
* an accumulator read is a write of the same MMA (`acc_write`);
* an A read of QK MMA `k` is in the issuing CTA, in columns `[256 + 8 k, 264 + 8 k)`
  (`qk_aCell`); a PV MMA reads A from shared memory;
* a load of warpgroup 0 is `32x32b` at the score columns `400 + 32 k` (`k < 2`) or the chunk
  columns `64 c` (`c < 4`), of at most 64 registers (`ldLen`), so its cells are in the loading
  CTA below column `432 + 64` (`dataCell`);
* the kernel fires no shift (`no_shift_of_code`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace TmRace

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hR : TmemRows P L X)
include hp hX hR

/-- **A written cell is in the writer's CTA, below column 512.** -/
theorem write_info {x : EvId} {cell : TcMma.Cell} (hw : TcMma.TmemWrite L X x cell) :
    cell.cta = x.1 / L.block ∧ cell.column < 512 := by
  obtain ⟨hc, h⟩ := writer_cases hp hX hR hw
  refine ⟨hc, ?_⟩
  rcases h with ⟨_, -, -, h⟩ | ⟨_, -, hb, -, -, h⟩ | ⟨k, ⟨_, _, hk, -⟩, -, h⟩ | ⟨-, h, -⟩ <;>
    omega

/-- **An A cell of an MMA is in the issuing CTA, below column 512.** -/
theorem aCell_info {e : EvId} {cell : TcMma.Cell} (ha : X.MmaACell e cell) :
    cell.cta = e.1 / L.block ∧ cell.column < 512 := by
  obtain ⟨d, s, acc, mask, index, b, ⟨pc, he⟩, hac⟩ := ha
  have hg := Frame.lt_of_get hX he
  rcases tc_role hR hg he rfl with ⟨-, hW⟩ | ⟨-, hM⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, -, h, hops⟩ |
      ⟨_, _, k, -, -, h, -, hops⟩ <;> cases h
    · obtain ⟨hcr, -, h2⟩ := TmemRow.qk_aCell hk hops hac
      obtain ⟨hlo, hhi⟩ := ops_cta hp hg (.inl rfl) hops
      refine ⟨?_, by omega⟩
      rcases hcr with h | h <;> rw [h]
      · exact hlo
      · exact hhi
    · obtain ⟨haT, -⟩ := hops
      simp [TcMma.aCell, haT] at hac
  · cases hc'

/-- **A loaded cell is in the loading CTA, below column 512.** -/
theorem load_info {e : EvId} {j : Nat} {cell : TcMma.Cell} (hl : TcMma.LoadCell L X e j cell) :
    cell.cta = e.1 / L.block ∧ cell.column < 512 := by
  obtain ⟨a, vals, sh, ⟨pc, he⟩, hj, rfl⟩ := hl
  have hg := Frame.lt_of_get hX he
  have hn := ldLen hp hX he rfl
  rcases tc_role hR hg he rfl with ⟨hat, hW⟩ | ⟨-, hM⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨k, _, h⟩ | ⟨c, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;>
      cases h
    · have hk := k.isLt
      obtain ⟨h1, -, h2⟩ := dataCell hp hat.1 (a := 400 + 32 * k.val) (j := j) (by omega)
      exact ⟨h1, by omega⟩
    · have hc := c.isLt
      obtain ⟨h1, -, h2⟩ := dataCell hp hat.1 (a := 64 * c.val) (j := j) (by omega)
      exact ⟨h1, by omega⟩
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, -, -, h, -⟩ |
      ⟨_, _, _, -, -, h, -⟩ <;> cases h
  · cases hc'

/-- **Every Tensor Memory access is a launched thread's MMA, copy, load or store, of a cell of
its CTA below column 512; no shift is issued.** -/
theorem access_info : Tmem.AccessCp.AccessInfoCp L X := by
  refine ⟨fun {e cell} ha => ?_, fun i s ⟨pc, he⟩ => no_shift_of_code hX code_noShift he s rfl⟩
  rcases ha with (hm | hm | hm) | ⟨j, hl⟩ | hs | hc | ⟨s, ⟨pc, he⟩, -⟩ | ⟨s, ⟨pc, he⟩, -⟩
  · obtain ⟨hc, hcol⟩ := write_info hp hX hR (.inl hm)
    obtain ⟨d, s, acc, mask, row, col, ⟨pc, he⟩, -⟩ := hm
    exact ⟨Frame.lt_of_get hX he, hc, hcol, .inl ⟨_, _, _, _, pc, he⟩⟩
  · obtain ⟨hc, hcol⟩ := write_info hp hX hR (acc_write hX hR hm)
    obtain ⟨d, s, mask, row, col, ⟨pc, he⟩, -⟩ := hm
    exact ⟨Frame.lt_of_get hX he, hc, hcol, .inl ⟨_, _, _, _, pc, he⟩⟩
  · obtain ⟨hc, hcol⟩ := aCell_info hp hX hR hm
    obtain ⟨d, s, acc, mask, index, b, ⟨pc, he⟩, -⟩ := hm
    exact ⟨Frame.lt_of_get hX he, hc, hcol, .inl ⟨_, _, _, _, pc, he⟩⟩
  · obtain ⟨hc, hcol⟩ := load_info hp hX hR hl
    obtain ⟨a, vals, sh, ⟨pc, he⟩, -⟩ := hl
    exact ⟨Frame.lt_of_get hX he, hc, hcol, .inr (.inr (.inl ⟨a, vals, sh, pc, he⟩))⟩
  · obtain ⟨hc, hcol⟩ := write_info hp hX hR (.inr (.inl hs))
    obtain ⟨a, vals, sh, j, ⟨pc, he⟩, -⟩ := hs
    exact ⟨Frame.lt_of_get hX he, hc, hcol, .inr (.inr (.inr ⟨a, vals, sh, pc, he⟩))⟩
  · obtain ⟨hcc, hcol⟩ := write_info hp hX hR (.inr (.inr (.inl hc)))
    obtain ⟨c, cta, index, lane, ⟨pc, he⟩, -⟩ := hc
    exact ⟨Frame.lt_of_get hX he, hcc, hcol, .inr (.inl ⟨c, pc, he⟩)⟩
  · exact absurd rfl (no_shift_of_code hX code_noShift he s)
  · exact absurd rfl (no_shift_of_code hX code_noShift he s)

end

end TmRace

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
