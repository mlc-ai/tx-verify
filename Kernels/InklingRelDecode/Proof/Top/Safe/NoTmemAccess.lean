-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccessInfo
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AllocBefore
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdstBefore
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AsyncDone

@[expose] public section

/-! # ERR-TMEM-ACCESS: Tensor Memory accesses are allocated and in the warp's lanes

By `Tmem.AccessCp.no_access_unsafe_cp` for the allocating warp 0: the `cta_group::1` facts
(`Export.tmem_facts`); every access is a launched thread's MMA, load or store of a cell of its CTA
below column 512 (`Tmem.access_info`); lane 0 of warp 0 allocates before every access
(`Tmem.alloc_before`); every load and store is waited for before every deallocation
(`Tmem.ldst_before_dealloc`, through the final `bar.sync 0` of the data lanes), and every MMA is
done before it (`Tmem.async_done`, through the final commit observed by the epilogue's poll). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noTmemAccess (hp : Pre Q L m) {X : Execution} (base : Iface.BaseRead L X)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (_hu : ¬HasUb X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) :
    ¬ Tmem.Pair.AccessUnsafe L X :=
  Tmem.AccessCp.no_access_unsafe_cp hX (Export.tmem_facts hp hX hf base)
    (Tmem.access_info hp hX hf base)
    ⟨fun hop => Tmem.alloc_before hp hX hf hop,
      fun hd hc => Tmem.ldst_before_dealloc hp hX hf safe base hd hc⟩
    (Tmem.async_done hp hX hf rows init base)

end PTX.Kernels.InklingRelDecode.Proof.Top
