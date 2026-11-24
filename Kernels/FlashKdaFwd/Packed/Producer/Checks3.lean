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

theorem window_2816 : window 2816 128 = some true := by kernel_rfl

theorem window_2944 : window 2944 52 = some true := by kernel_rfl

theorem window_2996 : window 2996 1 = some true := by
  unfold window
  rw [Prologue.scalarSite 2996 false "%r1788" 13 2094 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
  rfl

theorem window_2997 : window 2997 1 = some true := by
  unfold window
  rw [Prologue.scalarSite 2997 true "%rd1165" 11 3411 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
  rfl

theorem window_2998 : window 2998 74 = some true := by kernel_rfl

theorem window_3072 : window 3072 128 = some true := by kernel_rfl

theorem window_3200 : window 3200 128 = some true := by kernel_rfl

theorem window_3328 : window 3328 128 = some true := by kernel_rfl

theorem window_3456 : window 3456 128 = some true := by kernel_rfl

theorem window_3584 : window 3584 128 = some true := by kernel_rfl

theorem window_3712 : window 3712 65 = some true := by kernel_rfl

theorem window_3777 : window 3777 1 = some true := by
  unfold window
  rw [Prologue.scalarSite 3777 false "%r1789" 13 2095 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
  rfl

theorem window_3778 : window 3778 57 = some true := by kernel_rfl

end FlashKda.Packed.ProducerControl
