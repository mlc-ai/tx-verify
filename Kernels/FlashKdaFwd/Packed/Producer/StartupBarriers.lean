-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.ProducerControl
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX

def startupBarriers : List Nat := [85,110,379]

def startupSync : Instr := ⟨none,.barSync (.imm 0) true⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 60000 in
theorem barrier_site {cut : Nat} (member : cut ∈ startupBarriers) :
    kernel.code[cut]? = some startupSync := by
  simp [startupBarriers] at member
  rcases member with rfl | rfl | rfl
  · exact fetch (pc := 85) (i := 0) (n := 1) (by decide) (by decide)
      (show Transfers.slice 85 1 = some [startupSync] by kernel_rfl)
  · exact fetch (pc := 110) (i := 0) (n := 1) (by decide) (by decide)
      (show Transfers.slice 110 1 = some [startupSync] by kernel_rfl)
  · exact fetch (pc := 379) (i := 0) (n := 1) (by decide) (by decide)
      (show Transfers.slice 379 1 = some [startupSync] by kernel_rfl)

end FlashKda.Packed.ProducerControl
