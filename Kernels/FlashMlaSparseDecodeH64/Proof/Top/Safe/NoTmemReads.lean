-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemWrites

@[expose] public section

/-! # ERR-TMEM-RACE (MMA reads): MMA reads are ordered with writes

The safety class of Core's `Unsafe` this file owns (`TcMma.ReadsUnsafe`), proved from the
PV/rescale order of the writes class (`Safe.pvStore`) and nothing else (`TmRace.reads_safe`):
an accumulator read is a write of the same MMA, ordered as the writes are; an A read of QK MMA
`k` reads only copy `k`'s cells, written before it in the MMA lane's program order (the
pipelined copy→A-read pair); the kernel fires no shift. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-TMEM-RACE (MMA reads)**: MMA reads are ordered with writes. -/
theorem Safe.noTmemReads (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ TcMma.ReadsUnsafe L X := fun hu =>
  hu (TmRace.reads_safe hp hX hFw (tmem_rows hp hX hFw) (mmaOne hp hX hFw)
    (Safe.pvStore hp hIn hX hFw))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
