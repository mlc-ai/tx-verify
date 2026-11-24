-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Transfers
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Transfers
set_option maxHeartbeats 0
set_option maxRecDepth 60000

theorem decodes_2560 : (slice 2560 128).isSome = true := by rfl

theorem decodes_2688 : (slice 2688 128).isSome = true := by rfl

theorem decodes_2816 : (slice 2816 128).isSome = true := by rfl

theorem decodes_2944 : (slice 2944 128).isSome = true := by rfl

end FlashKda.Packed.Transfers
