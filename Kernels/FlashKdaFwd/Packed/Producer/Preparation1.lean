-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.PreparationRegion
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
set_option maxRecDepth 60000
set_option maxHeartbeats 0

theorem preparation_896 : preparationWindow 896 128 = some true := by
  kernel_rfl

theorem preparation_1024 : preparationWindow 1024 128 = some true := by
  kernel_rfl

theorem preparation_1152 : preparationWindow 1152 128 = some true := by
  kernel_rfl

theorem preparation_1280 : preparationWindow 1280 122 = some true := by
  kernel_rfl

end FlashKda.Packed.ProducerControl
