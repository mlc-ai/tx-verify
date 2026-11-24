-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Transfers
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Transfers
set_option maxHeartbeats 0
set_option maxRecDepth 60000

theorem decodes_1536 : (slice 1536 128).isSome = true := by rfl

theorem decodes_1664 : (slice 1664 128).isSome = true := by rfl

theorem decodes_1792 : (slice 1792 128).isSome = true := by rfl

theorem decodes_1920 : (slice 1920 128).isSome = true := by rfl

end FlashKda.Packed.Transfers
