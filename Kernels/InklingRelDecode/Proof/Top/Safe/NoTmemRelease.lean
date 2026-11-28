-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Tmem

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noTmemRelease (hp : Pre Q L m) {X : Execution} (base : Iface.BaseRead L X)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    ¬ Tmem.Pair.ReleaseUnsafe L X :=
  Tmem.One.no_release_unsafe hX (Export.tmem_facts hp hX hf base)

end PTX.Kernels.InklingRelDecode.Proof.Top
