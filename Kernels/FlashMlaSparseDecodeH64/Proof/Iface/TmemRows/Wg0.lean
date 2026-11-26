-- SPDX-License-Identifier: Apache-2.0
-- iface: TmemRow.Wg0 producer=W1 status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0

@[expose] public section

/-! # Warpgroup 0: Tensor Memory row

Warpgroup 0's code (pcs 103–1841) has these `tcgen05` sites (checked on the code by `wg0_sites`):
the fences `after_thread_sync` at 275, 711, 1187 and `before_thread_sync` at 287, 1119; the four
score loads (278, 280, 283, 285) at columns 400 and 432 and their wait (286); per chunk `c < 4`
the rescale arm's load, wait, store and wait at column `64 c` and the output's load and wait at
column `64 c`; the deallocation at 1840, which only warp 0 reaches. All loads and stores are
`32x32b`. The row states the RECORDED events (`Wg0/Ev.lean`, from Core's templates): a load
`.ld a vals .s32x32b` with `a` its first column, a store `.st a vals .s32x32b`, the deallocation
`.resource .one dst act` (its operands are the moved constants 0 and 512, `dealloc_operands`;
the event's request is owed, `Top/Inputs.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace TmemRow

/-- **Static check**: the `tcgen05` sites of pcs 103–1841. -/
theorem wg0_sites : regionOk kernel.code 103 1842
    ([(275, .fenceA), (711, .fenceA), (1187, .fenceA), (287, .fenceB), (1119, .fenceB),
      (278, .ld), (280, .ld), (283, .ld), (285, .ld), (286, .waitLd), (1840, .dealloc)] ++
     ([716, 817, 918, 1019, 1201, 1361, 1519, 1676].map (·, Tag.ld)) ++
     ([717, 818, 919, 1020, 1202, 1362, 1520, 1677].map (·, Tag.waitLd)) ++
     ([814, 915, 1016, 1117].map (·, Tag.st)) ++
     ([815, 916, 1017, 1118].map (·, Tag.waitSt))) = true := by
  decide +kernel

end TmemRow

/-- The `tcgen05` events of warpgroup 0: fences, waits, `32x32b` loads at the score columns
`400 + 32 k` and at the chunk columns `64 c`, stores at `64 c`, the deallocation at 1840. -/
def TmemRow.Wg0Tc (e : Event) : Prop :=
  e.kind = .tc .fenceAfter ∨ e.kind = .tc .fenceBefore ∨ e.kind = .tc .waitLd ∨
    e.kind = .tc .waitSt ∨
    (∃ (k : Fin 2) (vals : List Value), e.kind = .tc (.ld (400 + 32 * k.val) vals .s32x32b)) ∨
    (∃ (c : Fin 4) (vals : List Value), e.kind = .tc (.ld (64 * c.val) vals .s32x32b)) ∨
    (∃ (c : Fin 4) (vals : List Value), e.kind = .tc (.st (64 * c.val) vals .s32x32b)) ∨
    (e.pc = 1840 ∧ ∃ dst act, e.kind = .tc (.resource .one dst act))

/-- **Row `TmemRow.Wg0`**: a `tcgen05` event of warpgroup 0 is one of `Wg0Tc`. -/
def TmemRow.Wg0 (_P : Params) (L : Launch) (X : Execution) : Prop :=
  TmemRow.TcRow L X (Wg0At L) fun _ e => TmemRow.Wg0Tc e

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
