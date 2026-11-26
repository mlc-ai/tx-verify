-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Interface

@[expose] public section

/-! # The Compute phase: site kinds and the thread-dependent parts of the addresses

Vocabulary for the tables of the phase (`Tables.lean`, generated) and its invariant
(`Inv.lean`).

* `SK`: the kind of the site of a position of a tile, with the site's ordinal among the sites
  of its kind in the thread machine. A warp matrix load (`ldmatrix`) is two events and two
  sites: the read of the lane's 16-byte row (`ld`) and the matrix event (`ldMx`); a warp matrix
  store (`stmatrix`) is the matrix event (`st`) and the write of the row (`stWr`). The second
  site of each carries the bytes of the first event, so `SK.At k s` ("the site `s` is of kind
  `k`") is a predicate and not an equation.
* The parts of the shared addresses that depend on the thread's index `tid g` in its block
  (below 128 for a compute thread; `tid g % 32` is the lane, `tid g / 32` the warp), each named
  after the register that holds it:
  - `laneOff g = 16 * lane`: the lane's row in a 512-byte piece of an input array (`%r1637`);
  - `warpOff g = 1024 * warp`: the warp's part of `v` and of the output stage (`%r1639`);
  - `pairOff g` (`%r1629`) and `accOff g` (`%r1631`): the lane's first row in the bfloat16 state
    copy `state_acc` (rows of 16 bytes; the lanes of a block own disjoint rows);
  - `krOff g`: the lane's row of `k_restored`, which is read transposed (`%r1705`);
  - `gtOff g = 4 * (lane / 4)`: the lane's entry of the FP32 decay factors `g_total` (`%r1707`).
* `gate P g`: the position of the tile's first gate logit in the 32-element buffer `beta` of
  the input stage: the global index of the sequence's first token in the `[heads, tokens]`
  array, modulo 8 (the buffer is loaded from that index rounded down to a multiple of 8; the
  first token of a tile is a multiple of 16 after the sequence's, so the position does not
  depend on the tile). `gateOff P g` is the byte offset of the lane's logit pair (`%r1641`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

/-! ### Site kinds -/

/-- The kind of the site of a position of a tile, with the site's ordinal. -/
inductive SK where
  /-- An `mbarrier.try_wait` (a poll). -/
  | wait (j : Fin 10)
  /-- The row read of an `ldmatrix` (its first event). -/
  | ld (j : Fin 44)
  /-- The matrix event of an `ldmatrix` (its second event). -/
  | ldMx (j : Fin 44)
  /-- An `mma.sync`. -/
  | mma (j : Fin 104)
  /-- A `movmatrix`. -/
  | mv (j : Fin 16)
  /-- The matrix event of an `stmatrix` (its first event). -/
  | st (j : Fin 18)
  /-- The row write of an `stmatrix` (its second event). -/
  | stWr (j : Fin 18)
  /-- A scalar load. -/
  | load (j : Fin 178)
  /-- A `bar.sync`. -/
  | bar (j : Fin 10)
  /-- A `fence.proxy.async`. -/
  | fence (j : Fin 4)
  /-- An `mbarrier.arrive`. -/
  | arrive (j : Fin 7)
  deriving DecidableEq

/-- The site `s` of the thread machine is of kind `k`. -/
def SK.At : SK → Site → Prop
  | .wait j, s => s = .mbarWait j
  | .ld j, s => s = .matrixLoad j
  | .ldMx j, s => ∃ row, s = .matrixLoadMx j row
  | .mma j, s => s = .warpMma j
  | .mv j, s => s = .matrixMove j
  | .st j, s => s = .matrixStore j
  | .stWr j, s => ∃ row, s = .matrixStoreWr j row
  | .load j, s => s = .load j
  | .bar j, s => s = .bar j
  | .fence j, s => s = .fenceProxy j
  | .arrive j, s => s = .mbarArrive j

/-! ### The thread-dependent parts of the addresses -/

/-- The lane's row in a 512-byte piece: `16 * lane`. -/
def laneOff (g : Nat) : Nat := 16 * (tid g % 32)

/-- The warp's 1024 bytes of `v` and of the output stage: `1024 * warp`. -/
def warpOff (g : Nat) : Nat := 1024 * (tid g / 32)

/-- Half the offset of the lane's first row of `state_acc` inside its warp's part. -/
def pairOff (g : Nat) : Nat := 8 * (tid g % 8) + 64 * (tid g / 16 % 2) + 1024 * (tid g / 8 % 2)

/-- The offset of the lane's first row of `state_acc`. -/
def accOff (g : Nat) : Nat :=
  512 * (tid g / 32) + 16 * (tid g % 8) + 128 * (tid g / 16 % 2) + 2048 * (tid g / 8 % 2)

/-- The lane's row of a piece of `k_restored`, which is read transposed. -/
def krOff (g : Nat) : Nat := 16 * (tid g % 8) + 256 * (tid g / 8 % 2) + 128 * (tid g / 16 % 2)

/-- The lane's entry of the FP32 decay factors: `4 * (lane / 4)`. -/
def gtOff (g : Nat) : Nat := 4 * (tid g / 4 % 8)

/-- The position of a tile's first gate logit in the 32-element buffer of its input stage. -/
def gate (P : Params) (g : Nat) : Nat :=
  (P.total * headOf P g + firstToken P.length (seqOf P g)) % 8

/-- The byte offset of the lane's pair of gate logits in the buffer. -/
def gateOff (P : Params) (g : Nat) : Nat := 2 * (gate P g + tid g / 4 % 8)

theorem laneOff_le (g : Nat) : laneOff g ≤ 496 := by unfold laneOff; omega
theorem warpOff_le {g : Nat} (h : tid g < 128) : warpOff g ≤ 3072 := by unfold warpOff; omega
theorem pairOff_le (g : Nat) : pairOff g ≤ 1144 := by unfold pairOff; omega
theorem accOff_le {g : Nat} (h : tid g < 128) : accOff g ≤ 3824 := by unfold accOff; omega
theorem krOff_le (g : Nat) : krOff g ≤ 496 := by unfold krOff; omega
theorem gtOff_le (g : Nat) : gtOff g ≤ 28 := by unfold gtOff; omega
theorem gate_lt (P : Params) (g : Nat) : gate P g < 8 := Nat.mod_lt _ (by decide)
theorem gateOff_le (P : Params) (g : Nat) : gateOff P g ≤ 28 := by
  have := gate_lt P g
  unfold gateOff; omega

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
