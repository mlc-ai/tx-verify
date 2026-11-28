-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.FollowProof

namespace PTX.Kernels.InklingRelDecode.Proof.Export

/-- The glued machine follows all lanes when the worker loads read the
published bytes. The shared-memory protocol proves both trace facts. -/
public theorem followed {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (roles : RoleBytes L X)
    (counts : CountBytes Q L X) : Follow Q L X := follow_reads hp hX roles counts

end PTX.Kernels.InklingRelDecode.Proof.Export
