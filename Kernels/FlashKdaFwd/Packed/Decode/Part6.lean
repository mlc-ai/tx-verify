-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Transfers
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Transfers
set_option maxHeartbeats 0
set_option maxRecDepth 60000

theorem decodes_3072 : (slice 3072 128).isSome = true := by rfl

theorem decodes_3200 : (slice 3200 128).isSome = true := by rfl

theorem decodes_3328 : (slice 3328 128).isSome = true := by rfl

theorem decodes_3456 : (slice 3456 128).isSome = true := by rfl

end FlashKda.Packed.Transfers
