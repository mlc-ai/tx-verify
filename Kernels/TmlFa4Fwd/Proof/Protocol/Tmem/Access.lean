-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Core.Tmem.TmemPairAccess
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AllocBefore
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.LdstDealloc
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Dealloc
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Info
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Word

@[expose] public section

/-! # ERR-TMEM-ACCESS-LIFETIME

`noTmemAccess`: every Tensor Memory access is inside the MMA warp's allocation of its CTA and
completes before its deallocation (`Tmem.Access.no_access_unsafe` with warp 12), from the MMA warp's
three operations on column 0 (`tmem1Facts`), the access facts `Tmem.Access.AccessInfo` (`tmem_info`:
every access is a launched thread's MMA, `tcgen05.ld` or `tcgen05.st` of a cell of its CTA below
column 512, and no `tcgen05.cp` or `shift` is issued), the allocation hand-off
(`alloc_before`: every access follows lane 0 of warp 12's allocation, through barrier 2's first
rendezvous), the deallocation hand-off (`ldst_dealloc`: every load and store is finished by its
`wait` before the deallocation, through barrier 2's second rendezvous) and the MMA completions
(`mma_done`: every MMA is done before the deallocation, observed through the CTA's final commit by
a correction lane's poll before that rendezvous). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Kernels.TmlFa4Fwd

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-TMEM-ACCESS-LIFETIME.** -/
theorem noTmemAccess (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (hFw : Follow p l X) :
    ¬ Tmem.Pair.AccessUnsafe l X :=
  Tmem.Access.no_access_unsafe hX (tmem1Facts hp hX hFw) (tmem_info hp hX hFw)
    ⟨fun hk => alloc_before hp hX hFw hk,
      fun hd hc => ldst_dealloc hp hX hFw hd hc⟩ (mma_done hp hX hFw)

end PTX.Kernels.TmlFa4Fwd.Proof.Top
