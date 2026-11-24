-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma

noncomputable section

/-- Each of the four warps in a softmax stage owns 32 consecutive score rows. -/
def tmemRow (l : Launch) (g : Nat) : Fin 128 :=
  ⟨laneBase l g + laneOf l g, tmem_thread_lane_lt l g⟩

def pvQuarter (step : Fin 8) : Fin 4 :=
  ⟨step.val / 2, by have := step.isLt; omega⟩

/-- A PV A byte is the byte of the exact P store from its source softmax lane. The first
three x16 stores cover PV fragments 0–5 and the tail store covers fragments 6–7. -/
theorem pvFromProbability {l : Launch} {g : Nat} {s : OperandSpec}
    (hd : s.descriptor = pvDescriptor) (hCta : s.lowCta = g / l.block)
    (stage : Fin 2) (step : Fin 8) (byte : Fin 32)
    (hAddress : s.aTmem = some (probabilityColumn stage + 8 * step.val)) :
    aCell s (32 * (tmemRow l g).val + byte.val) =
      some (tcDataCell l g .s32x32b (probabilityAddress l g stage (pvQuarter step))
        (8 * (step.val % 2) + byte.val / 4), byte.val % 4) := by
  have h := pvACell hd stage step (tmemRow l g) byte hAddress
  have hCol : probabilityColumn stage + 16 * (pvQuarter step).val < 512 := by
    have := scoreColumn_range stage
    have := (pvQuarter step).isLt
    unfold probabilityColumn
    omega
  rw [probabilityAddress, tcDataCell_warp32 l g _ hCol]
  simpa only [hCta, tmemRow, (pvASegment stage step byte).1, pvQuarter, Nat.add_assoc] using h

end
end PTX.Kernels.TmlFa4Fwd.Softmax
