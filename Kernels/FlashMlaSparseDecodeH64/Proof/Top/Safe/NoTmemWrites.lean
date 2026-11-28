-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.PvStore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs

@[expose] public section

/-! # ERR-TMEM-RACE (two writes): Tensor Memory writes are ordered

The safety class of Core's `Unsafe` this file owns (`TcMma.WritesUnsafe`). By column class
(`TmRace.writes_safe`, `Protocol/TmemRace/Order.lean`): QK and PV MMAs of one D column are the
one MMA lane's, pipelined in program order; each copy fires once; warpgroup 0's stores of one
lane are one thread's, pipelined. What is still open (`Safe.NoTmemWrites.Rest`) is the
cross-role order of a PV MMA and a rescale store of warpgroup 0 in columns `[0, 256)`
(`TmRace.PvStoreOrder`), which `Top/Safe/NoTmemReads.lean` uses too. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The PV/rescale order** of a followed execution, from the shared inputs. -/
theorem Safe.pvStore (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    TmRace.PvStoreOrder L X :=
  TmRace.pvStore_order hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
    (hIn.bar0 hp X hX hFw) (tmem_rows hp hX hFw)

/-- **ERR-TMEM-RACE (two writes)**: Tensor Memory writes are ordered. -/
theorem Safe.noTmemWrites (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ TcMma.WritesUnsafe L X := fun hu =>
  hu (TmRace.writes_safe hp hX hFw (tmem_rows hp hX hFw) (mmaOne hp hX hFw)
    (Safe.pvStore hp hIn hX hFw))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
