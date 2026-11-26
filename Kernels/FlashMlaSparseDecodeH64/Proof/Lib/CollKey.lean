-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotWarpColl
public import Lemmas.Kernel.Progress.WarpCollPair

@[expose] public section

/-! # The key of a warp and the warp collective instructions -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {L : Launch}

/-- The key of a thread's warp. -/
def warpKey (L : Launch) (g : Nat) : Nat × Nat := (g / L.block, g % L.block / 32)

/-- An election instruction (its mask is a register, so it has no immediate static part). -/
def electOp : Op → Bool
  | .warp w => decide (w.kind = .elect)
  | _ => false

/-- An instruction that is a warp collective of the code: a shuffle or a warp barrier with
immediate operands, or an election (whose static part is the full mask,
`startup_elect`, `mma_atElect`, `tma_atElect`, `Wg0.Ev`). -/
def CollIns (ins : Instr) : Prop := (opShape ins.op).isSome = true ∨ electOp ins.op = true

theorem warpKey_eq {g h : Nat} (hs : SameWarp L g h) : warpKey L g = warpKey L h := by
  simp only [warpKey]; rw [hs.1.2.2, hs.2]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
