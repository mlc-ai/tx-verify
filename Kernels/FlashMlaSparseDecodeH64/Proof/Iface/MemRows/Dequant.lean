-- SPDX-License-Identifier: Apache-2.0
-- iface: MemRow.Dequant producer=D status=row-proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant

@[expose] public section

/-! # Warpgroup 2: memory classification row

Every memory event of a lane of warpgroup 2 (warps 8–11) at a pc of its code (2606–3610) is one
of (`MemRow.Dequant`, proved by `memRow_dequant`, `Dequant/Export/Mem.lean`):

* a non-coherent global read (the two length reads, pcs 2620 and 2630);
* a shared read lying in a raw buffer `raw b` of the lane's CTA (the scale vectors and the raw
  words of the lane's four rows of the slot's block);
* a 16-byte shared write at exactly `dequant b`'s chunk `dqChunk i r s` (`i` the lane's index in
  its warpgroup, `r` the row, `s` the step): the 32 chunks of a lane and the chunks of different
  lanes are pairwise disjoint (`dqChunk_inj`, `dqChunk_al`), and all lie in `dequant b`
  (`dqChunk_lt`).

**What the row does not say** (the control machine does not give it): the read's slot `b` is not
related to the write's (both are the block's slot `j % 2`; the row quantifies `b` per event); the
length reads' addresses (the parameter pointers plus `4 · ctaid.y`) are not stated; and no value:
the bytes read and written are havocked by the control machine (the data registers are not
tracked), so the written chunk's relation to the words read needs the data thread machine. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

noncomputable section

namespace MemRow

/-- Lane `i`'s 16-byte column in a dequantized tile (`%r58`): row group `i / 8`, swizzled by the
lane's index `i % 8` within its group. -/
def dqCol (i : Nat) : Nat := i / 8 % 8 * 128 + i / 64 % 2 * 1024 + (i / 8 % 8 ^^^ i % 8) * 16

/-- Chunk `s` of row `r` of lane `i`, from the tile's first byte (`chunkW`). -/
def dqChunk (i r s : Nat) : Nat := dqCol i + 2048 * r + 8192 * s

/-- The columns of the 128 lanes are distinct, 16-aligned and below 2048. -/
theorem dqCol_table :
    ∀ i < 128, dqCol i % 16 = 0 ∧ dqCol i < 2048 ∧ ∀ i' < 128, dqCol i = dqCol i' → i = i' := by
  decide +kernel

theorem dqChunk_al {i r s : Nat} (hi : i < 128) : dqChunk i r s % 16 = 0 := by
  have := (dqCol_table i hi).1
  unfold dqChunk
  omega

theorem dqChunk_lt {i r s : Nat} (hi : i < 128) (hr : r < 4) (hs : s < 8) :
    dqChunk i r s + 16 ≤ 65536 := by
  have := (dqCol_table i hi).1
  have := (dqCol_table i hi).2.1
  unfold dqChunk
  omega

/-- **The chunks of a warpgroup are pairwise distinct** (so, 16-aligned, disjoint). -/
theorem dqChunk_inj {i i' r r' s s' : Nat} (hi : i < 128) (hi' : i' < 128) (hr : r < 4)
    (hr' : r' < 4) (h : dqChunk i r s = dqChunk i' r' s') : i = i' ∧ r = r' ∧ s = s' := by
  obtain ⟨-, h1, h2⟩ := dqCol_table i hi
  have h1' := (dqCol_table i' hi').2.1
  unfold dqChunk at h
  have hc : dqCol i = dqCol i' := by omega
  exact ⟨h2 i' hi' hc, by omega, by omega⟩

end MemRow

/-- **Row `MemRow.Dequant`**: a memory event of a lane of warpgroup 2 at a pc of its code is a
non-coherent read, a shared read in a raw buffer of its CTA, or a 16-byte write of one of its
chunks in a dequantized tile of its CTA. -/
def MemRow.Dequant (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → DequantAt L g e.pc →
    MemRow.MemEvent e →
    (∃ a bs, e.kind = .nc a bs) ∨
    (∃ (a : Acc) (bs : List (Option Byte)) (b : Fin 2), e.kind = .rd a bs ∧
      MemRow.SharedIn L (g / L.block) (.raw b) a) ∨
    ∃ (a : Acc) (bs : List Byte) (b : Fin 2) (r : Fin 4) (s : Fin 8), e.kind = .wr a bs ∧
      MemRow.WsAcc L (g / L.block) ((Region.dequant b).lo + MemRow.dqChunk (g % 128) r s) 16 a

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
