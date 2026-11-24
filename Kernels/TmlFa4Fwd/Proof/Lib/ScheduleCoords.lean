-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Schedule

@[expose] public section

/-! # The scheduler's coordinates of a work item -/

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX

noncomputable section

def sectionHead (tiles width work : Nat) : Nat := work / (width * tiles) * width

theorem sectionHead_lt {tiles heads width work : Nat} (hWork : work < tiles * heads) :
    sectionHead tiles width work < heads := by
  have hu := Nat.div_mul_le_self work (width * tiles)
  have hc : sectionHead tiles width work * tiles ≤ work := by
    simpa only [sectionHead, Nat.mul_assoc] using hu
  by_contra! h
  have H := Nat.mul_le_mul_right tiles h
  rw [Nat.mul_comm heads] at H
  omega

def sectionStride (tiles heads width work : Nat) : Nat :=
  min width (heads - sectionHead tiles width work)

/-- The request-relative section mapping implemented by the scalar scheduler. -/
def assignedCoordinates (p : Params) (batch item : Nat) : Nat × Nat :=
  sectionCoords (requestTiles p batch) p.heads (sectionWidth (requestTiles p batch) p.heads)
    (item - tilePrefix p batch * p.heads)

/-- The scheduler's coordinates of a CTA's work item are in range. -/
theorem assignedCoordinates_valid {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {batch item : Nat} (hLo : tilePrefix p batch * p.heads ≤ item)
    (hHi : item < tilePrefix p (batch + 1) * p.heads) :
    256 * (assignedCoordinates p batch item).1 < p.qLength batch ∧
      (assignedCoordinates p batch item).2 < p.heads := by
  have hHeads : 0 < p.heads := by
    unfold Params.heads
    have := hp.shape.2.2.1
    omega
  have hIn : item - tilePrefix p batch * p.heads < requestTiles p batch * p.heads := by
    rw [tilePrefix_succ, Nat.add_mul] at hHi
    omega
  have hPos := sectionItem_coords (sectionWidth_pos (tiles := requestTiles p batch) hHeads) hIn
  exact ⟨Nat.mul_comm _ _ ▸ requestTile_has_row hPos.1, hPos.2.1⟩

/-- Clearing the low byte of a 32-bit value rounds it down to a multiple of 256. -/
theorem lowByteMask {x : Nat} (hx : x < 2 ^ 32) :
    x &&& 4294967040 = x / 256 * 256 := by
  have hDiv : (x &&& 4294967040) / 256 = x / 256 := by
    rw [show 256 = 2 ^ 8 from rfl, Nat.and_div_two_pow]
    change x / 256 &&& (2 ^ 24 - 1) = x / 256
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
  have hMod : (x &&& 4294967040) % 256 = 0 := by
    rw [show 256 = 2 ^ 8 from rfl, Nat.and_mod_two_pow]
    simp
  omega

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
