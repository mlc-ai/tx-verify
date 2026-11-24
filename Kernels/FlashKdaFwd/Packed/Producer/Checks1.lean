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

theorem window_768 : window 768 128 = some true := by kernel_rfl

theorem window_896 : window 896 128 = some true := by kernel_rfl

theorem window_1024 : window 1024 128 = some true := by kernel_rfl

theorem window_1152 : window 1152 128 = some true := by kernel_rfl

theorem window_1280 : window 1280 128 = some true := by kernel_rfl

theorem window_1408 : window 1408 3 = some true := by kernel_rfl

theorem window_1411 : window 1411 1 = some true := by
  unfold window
  rw [Prologue.scalarSite 1411 false "%r1790" 16 2096 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
  rfl

theorem window_1412 : window 1412 23 = some true := by kernel_rfl

theorem window_1435 : window 1435 1 = some true := by
  unfold window
  rw [Prologue.scalarSite 1435 false "%r1784" 12 2090 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
  rfl

theorem window_1436 : window 1436 100 = some true := by kernel_rfl

theorem window_1536 : window 1536 128 = some true := by kernel_rfl

theorem window_1664 : window 1664 128 = some true := by kernel_rfl

end FlashKda.Packed.ProducerControl
