-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Transfers
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Transfers
set_option maxHeartbeats 0
set_option maxRecDepth 60000

theorem decodes_2048 : (slice 2048 128).isSome = true := by rfl

theorem decodes_2176 : (slice 2176 128).isSome = true := by rfl

theorem decodes_2304 : (slice 2304 128).isSome = true := by rfl

theorem decodes_2432 : (slice 2432 128).isSome = true := by rfl

end FlashKda.Packed.Transfers
