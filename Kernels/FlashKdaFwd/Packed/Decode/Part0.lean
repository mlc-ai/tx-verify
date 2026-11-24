-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Transfers
public import Kernels.FlashKdaFwd.Packed.Prologue
public import Tactics.KernelRfl
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Transfers
set_option maxHeartbeats 0
set_option maxRecDepth 60000

theorem decodes_0 : (slice 0 128).isSome = true := by
  apply join (pc := 0) (n := 13) (k := 115) (by decide)
  · rw [Prologue.sites]; rfl
  · kernel_rfl

theorem decodes_128 : (slice 128 128).isSome = true := by kernel_rfl

theorem decodes_256 : (slice 256 128).isSome = true := by
  apply join (pc := 256) (n := 64) (k := 64) (by decide)
  · kernel_rfl
  · apply join (pc := 320) (n := 1) (k := 63) (by decide)
    · rw [Prologue.readHeadCount]; rfl
    · kernel_rfl

theorem decodes_384 : (slice 384 128).isSome = true := by kernel_rfl

end FlashKda.Packed.Transfers
