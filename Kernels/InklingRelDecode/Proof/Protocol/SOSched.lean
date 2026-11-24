-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingSched

@[expose] public section

/-!
# The S/P/O handshake's schedule and parity arithmetic

Pure arithmetic on block numbers, no kernel, no execution. The blocks of one split are processed
through a double buffer: block `i` has its scores `S` in Tensor Memory buffer `i % 2` and is the
`i / 2`-th use of that buffer. The two buffers have two barriers each of arrival count 1:

* `s_ready b`: completed by the MMA warp's QK commit for block `2 u + b`; the default partition
  polls it for that block with parity `(i / 2) % 2` before it reads the scores;
* `p_ready b`: completed by the arrival of thread 0 of the default partition after the P store of
  block `2 u + b`; the MMA warp polls it, in the iteration after the QK of block `i`, with the same
  parity, before it issues the PV MMAs of that block.

And two barriers of one use per block / per kernel:

* `o_done`: completed by the MMA warp's second PV commit (after the PV MMAs of block `j`): its
  `j`-th commit; polled by the default partition in every iteration `i ≥ 1` (before the lazy-rescale
  test), with parity `(i + 1) % 2` (`SODefault`: the register is `iteration xor 1`);
* `o_final`: the one commit after the loop; polled once by the epilogue with parity 0.

`Open p c` (`RingSched`) says a poll of parity `p` of a barrier that has completed `c` phases
succeeds. The theorems here fix, for each barrier, the number of completed phases at which the
poll that the code issues succeeds, from the range the protocol keeps the barrier in:

* `s_ready` and `p_ready` (`full_open`, `full_open_iff`): the poll for block `i` succeeds exactly
  at `i / 2 + 1` completed phases when the barrier has completed `i / 2` or `i / 2 + 1`;
* `o_done` (`oDone_open_iff`): the poll of iteration `i` succeeds exactly at `i` completed phases
  when the barrier has completed `i - 1` or `i` (it cannot be further ahead: the phase `i` completes
  with the commit of block `i - 1`, and the next needs the arrival for block `i`, which follows
  the poll). **The poll's parity is also the parity of `i - 2`** (`oDone_open_alias`): the
  parity alone does not exclude a barrier two phases behind. What excludes it is the thread's own
  count of earlier polls (`i - 1`, dense polls) together with the alternation of a commit object
  (`SOOdone`);
* `o_final` (`oFinal_open_iff`).

`below2 b i` is the number of blocks `i' < i` of buffer `b` (`b < 2`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX.Kernels.InklingRelDecode.Proof.Ring (Open)

/-! ### Buffers, uses, blocks -/

/-- The Tensor Memory buffer of block `i`. -/
def buf (i : Nat) : Nat := i % 2

/-- The block that is use `u` of buffer `b`. -/
def blockB (b u : Nat) : Nat := 2 * u + b

/-- The blocks `i' < i` in buffer `b` (`b < 2`). -/
def below2 (b i : Nat) : Nat := (i + 1 - b) / 2

theorem below2_zero (b : Nat) : below2 b 0 = 0 := by unfold below2; omega

theorem below2_succ {b i : Nat} (hb : b < 2) :
    below2 b (i + 1) = below2 b i + if i % 2 = b then 1 else 0 := by
  unfold below2
  split <;> omega

theorem below2_of_buf {b i : Nat} (hb : b < 2) (hi : i % 2 = b) : below2 b i = i / 2 := by
  unfold below2; omega

/-! ### Parity and phases of the two-buffer barriers -/

/-- The parity of the poll of `o_done` in iteration `i`. -/
def oDoneParity (i : Nat) : Nat := (i + 1) % 2

/-! ### The dependency chain of the blocks, as arithmetic

The block `i + 2` reuses the buffer of block `i`. The QK of block `i + 2` is issued in iteration
`i + 2`, after the PV of block `i` (issued in iteration `i + 1`), whose A operand is the P tile of
block `i`, aliased on the buffer: so the QK of the next use of a buffer follows the PV read of the
current one in the MMA warp's program order (`qk_after_pv`). -/

end PTX.Kernels.InklingRelDecode.Proof.SO
