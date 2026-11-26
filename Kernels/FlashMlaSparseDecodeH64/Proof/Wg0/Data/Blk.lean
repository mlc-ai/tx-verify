-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.Facts

@[expose] public section

/-! # The reads of one block of warpgroup 0's loop

The values the block loop reads, as the events deliver them ("reads as"): the two halves of the
score words (Tensor Memory loads into `loRegs` = `%r2428`–`%r2459` and `hiRegs` =
`%r2460`–`%r2491`), the valid-mask word, the peer elements (the two elements of peer load `k`,
`pw k`), the peer's row maximum, the rescale vote's result (`vt`) and the words of the current
rescale chunk; and the statistics the block starts from: the running maximum `m` (`%r2492`), the
running sum `l` (`%r2497`) and the true running maximum `mx` (`%r2427`); and the sink word `sk`
(`%r2422`: `-inf` unless the sink's load, pc 156, set it); and the epilogue's read of the
peer lane's row sum (`pe`, `%r1270`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX

/-- The reads of one block. -/
structure Blk where
  lo : List Value := []
  hi : List Value := []
  mw : Value := .pred false
  pw : Nat → Value × Value := fun _ => (.pred false, .pred false)
  pm : Value := .pred false
  vt : Bool := false
  o : List Value := []
  m : Value := .pred false
  l : Value := .pred false
  mx : Value := .pred false
  sk : Value := .bits 32 (BitVec.ofNat 64 4286578688)
  pe : Value := .pred false

/-- The registers of the words of rescale chunk `c` (64 from `%r741`; chunks 129 apart). -/
def oRegs (c : Nat) : List Nat := List.range' (1199 + 129 * c) 64

/-- The registers of the low and the high half of the score words. -/
def loRegs : List Nat := List.range' 2886 32
def hiRegs : List Nat := List.range' 2918 32

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
