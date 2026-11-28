-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow

noncomputable section

/-- Within one iteration the QK half precedes the PV half. -/
def Site.position : Site → Nat
  | .qkBar => 0 | .kvWait => 1 | .qkShfl => 2 | .qkBar2 | .qkSkip => 3 | .qkElect => 4
  | .qk j => 5 + j.val | .qkCommit => 13
  | .pvBar => 14 | .pWait => 15 | .pvShfl => 16 | .pvBar2 | .pvSkip => 17 | .pvElect => 18
  | .pv j => 19 + j.val | .pvCommit1 => 27 | .pvCommit2 => 28
  | _ => 0

def measure (d : D) : Nat :=
  let top := 30 * (2 ^ 32 + 2)
  match d.site with
  | .setMaxReg => top + 2 | .ldNum => top + 1 | .bar0 => 30 * (d.limit + 1) + 29
  | .finBar => 5 | .finElect => 4 | .finCommit => 3 | .bar1 => 2 | .setMaxRegInc => 1
  | .dispatch => 0
  | s => 30 * (d.limit + 1 - d.i) + (28 - s.position)

theorem low_lt (v : Value) : low v < 2 ^ 32 := by
  simp only [low, truncBits, BitVec.toNat_ofNat]
  omega

theorem measure_bound (d : D) : measure d ≤ 30 * (2 ^ 32 + 2) + 2 := by
  obtain ⟨s,i,v⟩ := d
  have := low_lt v
  cases s <;> simp only [measure, D.limit, Site.position] <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
