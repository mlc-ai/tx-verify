-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.ProducerControl
import all Kernels.FlashKdaFwd.Packed.Decode.Scalars
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
set_option maxHeartbeats 0
set_option maxRecDepth 60000

theorem window_1792 : window 1792 90 = some true := by kernel_rfl

theorem window_1882 : window 1882 1 = some true := by
  unfold window
  rw [Prologue.scalarSite 1882 false "%r1785" 12 2091 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
  rfl

theorem window_1883 : window 1883 37 = some true := by kernel_rfl

theorem window_1920 : window 1920 128 = some true := by kernel_rfl

theorem window_2048 : window 2048 68 = some true := by kernel_rfl

theorem window_2116 : window 2116 1 = some true := by
  unfold window
  rw [Prologue.scalarSite 2116 false "%r1786" 12 2092 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
  rfl

theorem window_2117 : window 2117 59 = some true := by kernel_rfl

theorem window_2176 : window 2176 128 = some true := by kernel_rfl

theorem window_2304 : window 2304 128 = some true := by kernel_rfl

theorem window_2432 : window 2432 128 = some true := by kernel_rfl

theorem window_2560 : window 2560 128 = some true := by kernel_rfl

theorem window_2688 : window 2688 128 = some true := by kernel_rfl

end FlashKda.Packed.ProducerControl
