-- SPDX-License-Identifier: Apache-2.0
-- iface: MemRow.Mma producer=C status=row-proved domain=consistent ahead=1
-- iface: MemRow.MmaFoot producer=C status=row-proved domain=consistent
-- iface: MemRow.MmaLoad producer=C status=row-proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma

@[expose] public section

/-! # The MMA warp: memory classification row

The MMA warp's code (pcs 1850–2161) makes no shared access of its own (its operands are read by
the `tcgen05` instructions, which are no memory events here); its memory events are the two
length reads, non-coherent global reads (`Mma/Ev.lean`): `MemRow.Mma`, proved by `memRow_mma`
(`Mma/Export/Mem.lean`). The reads' addresses are not stated.

Its `tcgen05` operations read shared memory asynchronously (`Execution.MmaFootprint`): every
operand byte of an MMA and every source byte of a copy lies in the issuing CTA's dequantized
tile of a stage (the K/V operands, and the query tile in stage 0's bytes) or in the P tile
(`MemRow.MmaFoot`, proved by `memRow_mmaFoot`). Its eight tensor loads of the query write the
query tile, stage 0's dequantized bytes (`MemRow.MmaLoad`, proved by `memRow_mmaLoad`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

noncomputable section

/-- **Row `MemRow.Mma`**: a memory event of the MMA warp is a non-coherent read. -/
def MemRow.Mma (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → MmaAt L g e.pc →
    MemRow.MemEvent e → ∃ a bs, e.kind = .nc a bs

/-- **Row `MemRow.MmaFoot`**: a shared byte an MMA or copy of the MMA warp reads lies in a
dequantized tile or the P tile of the issuing CTA. -/
def MemRow.MmaFoot (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → MmaAt L g e.pc →
    ∀ {isB : Bool} {idx : Nat} {l : Loc}, X.MmaFootprint (g, k) isB idx l →
      (∃ b, MemRow.LocIn L (g / L.block) (.dequant b) l) ∨
        MemRow.LocIn L (g / L.block) .pExchange l

/-- **Row `MemRow.MmaLoad`**: a tensor load of the MMA warp reads through the query map
(`Pre.mapQBind`), and a shared byte it writes lies in the issuing CTA's stage-0 dequantized tile
(the query tile). -/
def MemRow.MmaLoad (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → MmaAt L g e.pc →
    ∀ {a : Nat} {s : TensorCopy.Spec}, e.kind = .tensorIssue a s →
      (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
        ⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass⟩ ∧
      ∀ {x y b : Nat} {l : Loc}, TensorCopy.writeLoc s x y b = some l →
        MemRow.LocIn L (g / L.block) (.dequant 0) l

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
