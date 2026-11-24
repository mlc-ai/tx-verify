-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.ProducerControl
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
set_option maxHeartbeats 0
set_option maxRecDepth 60000

theorem window_0 : window 0 13 = some true := by
  unfold window
  rw [Prologue.sites]
  rfl

theorem window_13 : window 13 115 = some true := by kernel_rfl

theorem window_128 : window 128 128 = some true := by kernel_rfl

theorem window_256 : window 256 64 = some true := by kernel_rfl

theorem window_320 : window 320 1 = some true := by unfold window; rw [Prologue.readHeadCount]; rfl

theorem window_321 : window 321 63 = some true := by kernel_rfl

theorem window_384 : window 384 128 = some true := by kernel_rfl

theorem window_512 : window 512 128 = some true := by kernel_rfl

theorem window_640 : window 640 128 = some true := by kernel_rfl

end FlashKda.Packed.ProducerControl
