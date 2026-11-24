-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Transfers
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Transfers
set_option maxHeartbeats 0
set_option maxRecDepth 60000

theorem decodes_3584 : (slice 3584 128).isSome = true := by rfl

theorem decodes_3712 : (slice 3712 123).isSome = true := by rfl

end FlashKda.Packed.Transfers
