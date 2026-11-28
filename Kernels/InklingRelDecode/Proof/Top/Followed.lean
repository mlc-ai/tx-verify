-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Followed
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem followed (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) : Follow Q L X :=
  Export.followed hp hX (fun h => Protocol.Shared.role_bytes hp hX h)
    (fun h site => Protocol.Shared.published_counts hp hX h site)

end PTX.Kernels.InklingRelDecode.Proof.Top
