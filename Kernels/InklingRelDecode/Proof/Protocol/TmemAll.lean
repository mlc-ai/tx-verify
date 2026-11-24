-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.TmemAccess
public import Kernels.InklingRelDecode.Proof.Protocol.TmemTc
public import Kernels.InklingRelDecode.Proof2.Lib.TmemAlloc

@[expose] public section

/-!
# The Tensor Memory protocol fields (`cta_group::1`): umbrella

`TmemAlloc` (`Tmem1Facts`, `no_resource_unsafe`, `no_release_unsafe`: `Safety.Protocol.tmemResource`
and `tmemRelease`), `TmemAccess` (`no_access_unsafe`: `tmemAccess`; `mmaDoneDealloc_of`).
-/
