-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Transfers
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Transfers
set_option maxHeartbeats 0
set_option maxRecDepth 60000

theorem decodes_1024 : (slice 1024 128).isSome = true := by rfl

theorem decodes_1152 : (slice 1152 128).isSome = true := by rfl

theorem decodes_1280 : (slice 1280 128).isSome = true := by rfl

theorem decodes_1408 : (slice 1408 128).isSome = true := by rfl

end FlashKda.Packed.Transfers
