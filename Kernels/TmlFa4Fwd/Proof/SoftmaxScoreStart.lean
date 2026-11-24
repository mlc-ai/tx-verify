-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxWaits
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmem

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

def qkWaitSite : Round → Fin 10
  | .first => 1
  | .biased => 4
  | .unbiased => 7

end
end PTX.Kernels.TmlFa4Fwd.Softmax
