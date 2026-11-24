-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Kernels.FlashKdaFwd.Ptx
public import Kernels.FlashKdaFwd.Data.Prefix

/-! The complete tile-prefix kernel decodes to the 173 typed instructions in the cache. -/
@[expose] public section
namespace FlashKda.Prefix
open PTX

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
theorem decode_eq :
    Decode.kernelIn Generated.FlashKdaFwd.module.globals
      Generated.FlashKdaFwd.module.functions[0]! = .ok Decoded.kernel := by
  rfl

end FlashKda.Prefix
