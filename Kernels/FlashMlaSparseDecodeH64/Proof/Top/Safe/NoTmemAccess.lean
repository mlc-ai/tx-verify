-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemResource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Access
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Alloc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Dealloc

@[expose] public section

/-! # ERR-TMEM-ACCESS: Tensor Memory accesses are allocated and in the warp's lanes

The safety class of Core's `Unsafe` this file owns (`Tmem.Pair.AccessUnsafe`), by
`Tmem.AccessCp.no_access_unsafe_cp` (`Lemmas/Tmem/AccessCp.lean`) for the allocating warp 0:

* `Tmem1Facts L X 0`: the `cta_group::1` facts of warp 0 (`Safe.tmemOne`);
* `AccessInfoCp`: every access is a launched thread's MMA, copy, load or store of a cell of its
  CTA below column 512, and no shift is issued (`TmRace.access_info`,
  `Protocol/TmemRace/Access.lean`, from the Tensor Memory rows);
* the allocation by lane 0 of warp 0 (pc 91) happens before every access (through `bar.sync 0`
  at pc 97: `TmRace.alloc_before`, `Protocol/TmemRace/Alloc.lean`);
* the deallocation's orders (`TmRace.dealloc_ldst`, `TmRace.dealloc_async`,
  `Protocol/TmemRace/Dealloc.lean`): every load and store is waited for before the deallocation
  (pc 1840, after barrier 12), and every MMA and copy is done (by the commit that warpgroup 0's
  poll of `svDone` at pc 1184 observes) before it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-TMEM-ACCESS**: Tensor Memory accesses are allocated and in the warp's lanes. -/
theorem Safe.noTmemAccess (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ Tmem.Pair.AccessUnsafe L X :=
  Tmem.AccessCp.no_access_unsafe_cp hX (Safe.tmemOne hp hIn hX hFw)
    (TmRace.access_info hp hX (tmem_rows hp hX hFw))
    ⟨fun hop => TmRace.alloc_before hp hX hFw (hIn.bar0 hp X hX hFw) hop,
      fun hd hc => TmRace.dealloc_ldst hp hX hFw (hIn.bar hp X hX hFw) hd hc⟩
    (TmRace.dealloc_async hp hX hFw (hIn.bar hp X hX hFw) (hIn.mbar hp X hX hFw)
      (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
