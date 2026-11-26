-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots

@[expose] public section

/-! # The index warp's local time

The role's states in the order of its events (`place`). The state does not hold its block
number (the ring's slot and parity only), so the block is read from the counts: block `i` is the
sum of the arrivals on the four slots of `valid_coord_ready` (`blockOf`; under the reference
invariant it is the invariant's block, `blockOf_eq`). The two length loads are at places 0 and 1
(glued 103 and 104, below the loops); a site of block `i` is at
`ixBlk0 + stride * i + ord s + min el 1` (`Lib/Slots.lean`: glued `frame i + ord + min el 1`):
the first index pair 0–1, the extra cache's first pair 2–3, the next pair 4–5, the wait on
`valid_coord_free` at `ixWait = 6`, the shuffles 7, 8, the coordinate pair's store 9–10, the
validity byte 11, the arrival on `valid_coord_ready` at `ixArr = 12`. The CTA barrier is at
glued `endSlot` (`endAt`, for at most `2 ^ 26 + 3` blocks, `endAt_eq`) and the exit after it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

/-- **The block of the counts**: the arrivals on the four slots of `valid_coord_ready`. -/
def blockOf (L : Launch) (g : Nat) (n : Cnt → Nat) : Nat :=
  n (.arrive (MbarRow.loc L g (.coordReady 0))) + n (.arrive (MbarRow.loc L g (.coordReady 1))) +
    n (.arrive (MbarRow.loc L g (.coordReady 2))) + n (.arrive (MbarRow.loc L g (.coordReady 3)))

/-- A site's order in its block. -/
def ord : IxSite → Nat
  | .pre => 0
  | .xpre => 2
  | .pf | .xpf => 4
  | .wA | .wB => 6
  | .sA1 | .sB1 => 7
  | .sA2 | .sB2 => 8
  | .stA | .stB => 9
  | .bA | .bB => 11
  | .arrA | .arrB => 12
  | .lenA | .lenB | .bar | .exit => 0

/-- The local place of the CTA barrier: glued `endSlot`. -/
def ixEndPlace : Nat := endSlot - ixOrg

/-- The barrier's place after block `i`: `ixEndPlace`, or past the block if it is later. -/
def endAt (i : Nat) : Nat := max ixEndPlace (ixBlk0 + stride * i + ixSpan)

/-- The place of site `s` at element `el` in block `i`. -/
def placeAt (i : Nat) (s : IxSite) (el : Nat) : Nat :=
  match s with
  | .lenA => 0
  | .lenB => 1
  | .bar => endAt i
  | .exit => endAt i + 1
  | s => ixBlk0 + stride * i + ord s + min el 1

/-- **The place of a state** with counts `n`: its site's in the block of the counts. -/
def place (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Nat :=
  placeAt (blockOf L g n) d.site d.el

/-- **The local time of a state**: its place. -/
def time (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Nat := place L g d n

/-- **Under the reference invariant the block of the counts is the invariant's block.** -/
theorem blockOf_eq {n : Cnt → Nat} {i : Nat}
    (hc : RingCounts L g n i 0) : blockOf L g n = i := by
  unfold blockOf
  rw [(hc 0).2, (hc 1).2, (hc 2).2, (hc 3).2]
  exact ring_sum i

/-- **The barrier is at `ixEndPlace`** (glued `endSlot`) for at most `2 ^ 26 + 3` blocks. -/
theorem endAt_eq {i : Nat} (h : i ≤ blockCap + 3) : endAt i = ixEndPlace := by
  simp only [endAt, ixEndPlace, endSlot, ixOrg, ixBlk0, loopBase, ixOff, stride, ixSpan,
    blockCap] at h ⊢
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
