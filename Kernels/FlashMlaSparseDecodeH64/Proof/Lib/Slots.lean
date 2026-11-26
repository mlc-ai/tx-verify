-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

/-! # The slots of the glued time table

Plain numbers only: the one design every role's local time (`<Role>/Time.lean`) and the glued
table (`Common/Time.lean`) are built on. No role and no state is named here; the roles name these
numbers, and each channel's waiter/producer facts are proved from the inequalities below.

**The stride.** Every role's block `r` of the main loop sits at
`frame r + <role>Off + <site offset>` with `frame r = loopBase + stride * r` and one stride
`stride = 128` for every role. The largest per-block need is the MMA lane's (`mmaPvc + 1 = 115`
places): between its commit to `qk_done` and its wait on `so_ready` lies warpgroup 0's block
from its `qk_done` wait to its `so_ready` arrival (72 places).
Every role pads its block to the stride (`*_span`).

**The origins.** A role's local place `p` is at glued time `<role>Org + p` (`Common/Time.lean`):
warpgroup 0 at `wg0Org = 100`, the MMA lane and the index warp at `mmaOrg = ixOrg = 103`
(`idleBase`), the TMA lane and the dequantizer at `tmaOrg = deqOrg = 132`. The prologues stay
below `loopBase = 140`. The local place of a role's block `r` site is `<role>Blk0 + stride * r +
<site offset>` with `<role>Blk0 = loopBase + <role>Off - <role>Org` (`*_loop`).

**The end.** Named barrier 12 (every warp's last event but the return) is at the one constant
slot `endSlot = loopBase + stride * (2 ^ 26 + 4)` for every role (the idle code of warpgroup 1
too), above every block place for `R < 2 ^ 26` blocks; the return is one later.

## The channels (glued slots; `r` the block; producer place `<` waiter place)

Each row: channel; producer pc: slot; waiter pcs: slots (`frame r = 140 + 128 r`).

* `q_tma`: MMA loads 1906..1927 and arrival 1929; waiter MMA 1931 (the lane itself).
* `q_utccp`: MMA commit 1982: 134; waiters MMA 1983, TMA 2205, dequant 2644: `qUtccpSlot = 135`.
* `last_store_done`: wg0 arrival 200: `lastArr = 105`; TMA 2209: `lastWait = 136`.
* `valid_coord_ready[r%4]`: index 2476/2565: `crArr r = frame r + 12`; wg0 264:
  `crWaitW0 r = frame r + 213`, TMA 2234: `crWaitT r = frame r + 16`.
* `valid_coord_free[r%4]`: wg0 571: `cfArrW0 r = frame r + 248`, TMA 2308:
  `cfArrT r = frame r + 99`; index 2446/2534 in block `r + 4`: `cfWait (r + 4) = frame (r+4) + 6`.
* `raw_ready[r%2]`: TMA 2305: `rrArr r = frame r + 98`; dequant 2677: `rrWait r = frame r + 104`.
* `raw_free[r%2]`: dequant 3599: `rfArr r = frame r + 188`; TMA 2245 in block `r + 2`:
  `rfWait (r + 2) = frame (r+2) + 17`.
* `dequant_ready[r%2]`: dequant 3597: `drArr r = frame r + 187`; MMA 2012:
  `drWait r = frame r + 192`.
* `qk_done[r%2]`: MMA commit 2105: `qkCommit r = frame r + 210`; wg0 272:
  `qkWait r = frame r + 214`.
* `so_ready[r%2]`: wg0 1122: `soArr r = frame r + 286`; MMA 2107: `soWait r = frame r + 296`.
* `sv_done[r%2]`: MMA commit 2148: `svCommit r = frame r + 306`; dequant 2684 in block `r + 2`:
  `svWaitD (r + 2) = frame (r+2) + 105`; wg0 1184 after the last block `R - 1`:
  `svWaitW0 R = frame R + 181`.
* barrier 12: every role (pcs 1835, 2160, 2330, 2585, 2604, 3610) at `endSlot`.

Barriers 9, 10/11 are inside warpgroup 0: the same table for every warp, so the same place.
The free rings' first uses (`raw_free` blocks 0, 1; `valid_coord_free` blocks 0–3; the
dequantizer's `sv_done` blocks 0, 1) pass at once (parity `okPolls + 1`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

/-- The slot of the commit to `bar_q_utccp`: the time of the MMA lane's wait at pc 1983. -/
def qUtccpSlot : Nat := 135

/-! ### Stride, origins, blocks -/

/-- **The block stride** shared by every role. -/
def stride : Nat := 128
/-- The first block's frame. -/
def loopBase : Nat := 140
/-- Block `r`'s frame. -/
def frame (r : Nat) : Nat := loopBase + stride * r

/-- The glued time of a role's local place `0`. -/
def wg0Org : Nat := 100
def mmaOrg : Nat := 103
def ixOrg : Nat := 103
def tmaOrg : Nat := 132
def deqOrg : Nat := 132

/-- A role's block offset in the frame. -/
def ixOff : Nat := 0
def tmaOff : Nat := 16
def deqOff : Nat := 104
def mmaOff : Nat := 192
def wg0Off : Nat := 212

/-! ### Site offsets in a role's block -/

/-- Index warp: the wait on `valid_coord_free`, the arrival on `valid_coord_ready`; the block's
places `0 .. ixSpan - 1` (the two index pairs' loads of two elements each come first: the first
pair 0–1, the extra cache's first pair 2–3, the next pair 4–5; `Index/Time.lean`). -/
def ixWait : Nat := 6
def ixArr : Nat := 12
def ixSpan : Nat := 13
/-- TMA lane: the waits on `valid_coord_ready`, `raw_free`, the arrivals on `raw_ready`,
`valid_coord_free` (its `Site.idx`). -/
def tmaCw : Nat := 0
def tmaRw : Nat := 1
def tmaRa : Nat := 82
def tmaCf : Nat := 83
/-- Dequantizer: the waits on `raw_ready`, `sv_done`, the arrivals on `dequant_ready`,
`raw_free` (its `Site.idx`). -/
def deqWraw : Nat := 0
def deqWsv : Nat := 1
def deqArrD : Nat := 83
def deqArrF : Nat := 84
/-- MMA lane: the wait on `dequant_ready`, the commit to `qk_done`, the wait on `so_ready` (after
the pad), the commit to `sv_done`. -/
def mmaKv : Nat := 0
def mmaQkc : Nat := 18
def mmaSo : Nat := 104
def mmaPvc : Nat := 114
/-- Warpgroup 0: the waits on `valid_coord_ready`, `qk_done`, the arrivals on
`valid_coord_free`, `so_ready` (from its block's first site, barrier 9 at pc 256). -/
def w0Wv : Nat := 1
def w0Wq : Nat := 2
def w0ArrV : Nat := 36
def w0ArrS : Nat := 74
/-- Warpgroup 0's epilogue after `R` blocks starts at `frame R + w0Epi`; its wait on `sv_done` is
`w0Wsv` later. -/
def w0Epi : Nat := 176
def w0Wsv : Nat := 5
/-- Warpgroup 0's set-up: the arrival on `last_store_done` at local place 5. -/
def w0ArrL : Nat := 5
/-- The TMA lane's wait on `last_store_done` at local place 4. -/
def tmaLastW : Nat := 4

/-- **The slot before the elections of warps 4 and 5**: a lane of either warp without its
election event (pc 1853, 2165) is at its startup, warpgroup 1's head (glued times below
`idleBase = 103`) or its role's first state at the election site (`mmaOrg`, `tmaOrg`). -/
def electSlot : Nat := tmaOrg

/-- The bound on the block count (`2 ^ 26`, `blockCap_eq`). -/
def blockCap : Nat := 67108864

/-- **Barrier 12's slot**, the same for every role. -/
def endSlot : Nat := loopBase + stride * (blockCap + 4)

/-- Warpgroup 0's epilogue frame after `R` blocks. -/
def epi (R : Nat) : Nat := frame R + w0Epi

/-! ### Local block bases (`<role>Org + <role>Blk0 = loopBase + <role>Off`) -/

def ixBlk0 : Nat := loopBase + ixOff - ixOrg
def tmaBlk0 : Nat := loopBase + tmaOff - tmaOrg
def deqBlk0 : Nat := loopBase + deqOff - deqOrg
def mmaBlk0 : Nat := loopBase + mmaOff - mmaOrg
def wg0Blk0 : Nat := loopBase + wg0Off - wg0Org
def wg0EpiBlk0 : Nat := loopBase + w0Epi - wg0Org

/-! ### The channel slots (glued times) -/

/-- `last_store_done`: warpgroup 0's arrival, the TMA lane's wait. -/
def lastArr : Nat := wg0Org + w0ArrL
def lastWait : Nat := tmaOrg + tmaLastW
/-- `valid_coord_ready[r % 4]`. -/
def crArr (r : Nat) : Nat := frame r + ixOff + ixArr
def crWaitW0 (r : Nat) : Nat := frame r + wg0Off + w0Wv
def crWaitT (r : Nat) : Nat := frame r + tmaOff + tmaCw
/-- `valid_coord_free[r % 4]`: block `r`'s arrivals, block `r`'s wait (of block `r - 4`'s). -/
def cfArrW0 (r : Nat) : Nat := frame r + wg0Off + w0ArrV
def cfArrT (r : Nat) : Nat := frame r + tmaOff + tmaCf
def cfWait (r : Nat) : Nat := frame r + ixOff + ixWait
/-- `raw_ready[r % 2]`. -/
def rrArr (r : Nat) : Nat := frame r + tmaOff + tmaRa
def rrWait (r : Nat) : Nat := frame r + deqOff + deqWraw
/-- `raw_free[r % 2]`: block `r`'s arrival, block `r`'s wait (of block `r - 2`'s). -/
def rfArr (r : Nat) : Nat := frame r + deqOff + deqArrF
def rfWait (r : Nat) : Nat := frame r + tmaOff + tmaRw
/-- `dequant_ready[r % 2]`. -/
def drArr (r : Nat) : Nat := frame r + deqOff + deqArrD
def drWait (r : Nat) : Nat := frame r + mmaOff + mmaKv
/-- `qk_done[r % 2]`. -/
def qkCommit (r : Nat) : Nat := frame r + mmaOff + mmaQkc
def qkWait (r : Nat) : Nat := frame r + wg0Off + w0Wq
/-- `so_ready[r % 2]`. -/
def soArr (r : Nat) : Nat := frame r + wg0Off + w0ArrS
def soWait (r : Nat) : Nat := frame r + mmaOff + mmaSo
/-- `sv_done[r % 2]`: block `r`'s commit, the dequantizer's block-`r` wait (of block `r - 2`'s),
warpgroup 0's wait after `R` blocks (of block `R - 1`'s). -/
def svCommit (r : Nat) : Nat := frame r + mmaOff + mmaPvc
def svWaitD (r : Nat) : Nat := frame r + deqOff + deqWsv
def svWaitW0 (R : Nat) : Nat := epi R + w0Wsv

/-! ### The required inequalities: producer place `<` waiter place -/

section
/-- Unfold every slot and close by `omega`. -/
local macro "slot_omega" : tactic => `(tactic| (simp only [
  qUtccpSlot, stride, loopBase, frame, wg0Org, mmaOrg, ixOrg, tmaOrg, deqOrg, ixOff, tmaOff,
  deqOff, mmaOff, wg0Off, ixWait, ixArr, ixSpan, tmaCw, tmaRw, tmaRa, tmaCf, deqWraw, deqWsv,
  deqArrD, deqArrF, mmaKv, mmaQkc, mmaSo, mmaPvc, w0Wv, w0Wq, w0ArrV, w0ArrS, w0Epi, w0Wsv,
  w0ArrL, tmaLastW, electSlot, endSlot, blockCap, epi, lastArr, lastWait, crArr, crWaitW0, crWaitT,
  cfArrW0, cfArrT, cfWait, rrArr, rrWait, rfArr, rfWait, drArr, drWait, qkCommit, qkWait, soArr,
  soWait, svCommit, svWaitD, svWaitW0] at *) <;> omega)

/-- `q_utccp`: the MMA lane's commit (local place 31) is before the slot. -/
theorem qUtccp_lt : mmaOrg + 31 < qUtccpSlot := by slot_omega
/-- `valid_coord_ready`: the index warp's arrival is before both waits of the block. -/
theorem cr_lt_w0 (r : Nat) : crArr r < crWaitW0 r := by slot_omega
theorem cr_lt_t (r : Nat) : crArr r < crWaitT r := by slot_omega
/-- `raw_free`: block `r`'s arrival before the TMA wait of block `r + 2`. -/
theorem rf_lt (r : Nat) : rfArr r < rfWait (r + 2) := by slot_omega
/-- `dequant_ready`. -/
theorem dr_lt (r : Nat) : drArr r < drWait r := by slot_omega
/-- `qk_done`. -/
theorem qk_lt (r : Nat) : qkCommit r < qkWait r := by slot_omega
/-- `sv_done`: block `r`'s commit before the dequantizer's wait of block `r + 2`, and the last
block's before warpgroup 0's wait after the loop. -/
theorem sv_lt_d (r : Nat) : svCommit r < svWaitD (r + 2) := by slot_omega
theorem sv_lt_w0 (R : Nat) (h : 1 ≤ R) : svCommit (R - 1) < svWaitW0 R := by slot_omega

/-- **Before the elections**: the MMA and TMA lanes' first states and warpgroup 1's head (glued
times at most `wg0Org + 3`, one past its last state) are at most `electSlot`, which is before the
`q_utccp` slot and every block's frame, so a lane that has not elected is short of every channel
event of the lag rows (`Common/Export/PreElect.lean`). -/
theorem elect_le : wg0Org + 3 ≤ electSlot ∧ mmaOrg ≤ electSlot ∧ tmaOrg ≤ electSlot := by
  slot_omega
theorem elect_lt_q : electSlot < qUtccpSlot := by slot_omega
theorem elect_lt (r o : Nat) : electSlot < frame r + o := by slot_omega

/-! ### Order inside a role -/

/-- The local block bases are past the prologues. -/
theorem loops : ixBlk0 = 37 ∧ tmaBlk0 = 24 ∧ deqBlk0 = 112 ∧ mmaBlk0 = 229 ∧ wg0Blk0 = 252 ∧
    wg0EpiBlk0 = 216 := by decide
end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
