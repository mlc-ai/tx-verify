-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.PreparationRegion
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
set_option maxRecDepth 60000
set_option maxHeartbeats 0

theorem preparation_315 : preparationWindow 315 5 = some true := by
  kernel_rfl

theorem preparation_320 : preparationWindow 320 1 = some true := by
  unfold preparationWindow
  rw [Prologue.readHeadCount]
  rfl

theorem preparation_321 : preparationWindow 321 63 = some true := by
  kernel_rfl

theorem preparation_384 : preparationWindow 384 128 = some true := by
  kernel_rfl

theorem preparation_512 : preparationWindow 512 128 = some true := by
  kernel_rfl

theorem preparation_640 : preparationWindow 640 128 = some true := by
  kernel_rfl

theorem preparation_768 : preparationWindow 768 128 = some true := by
  kernel_rfl

end FlashKda.Packed.ProducerControl
