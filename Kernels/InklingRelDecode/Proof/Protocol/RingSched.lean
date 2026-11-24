-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

/-!
# The KV ring's schedule and parity arithmetic

Pure arithmetic on block numbers, no kernel, no execution. The K/V tiles of the iterations of one
split are staged in a ring of three slots: block `i` lives in slot `i % 3`, and it is the
`i / 3`-th use of that slot. The slot has two barriers of arrival count 1 (`kv_ready`, `kv_empty`),
and each use completes one phase of each: the producer's `expect_tx` arrival and the transaction
bytes of the copies complete the phase `i / 3` of `kv_ready`, and the MMA warp's PV commit for
block `i` completes the phase `i / 3` of `kv_empty`.

* The first `np ≤ 3` blocks are issued by the default partition's prologue, the others by the
  loader (`issuer`). The prologue does not wait: slot `s < np` is fresh. The loader waits for
  every block it issues, including those of fresh slots (`s ≥ np`, use 0).
* A poll of parity `p` of a barrier that has completed `c` phases succeeds when
  `p % 2 = (c + 1) % 2` (`Open`): the phase with parity `p` is the last completed one; on a
  fresh barrier (`c = 0`) parity 1 passes. The MMA warp waits for `kv_ready` with parity
  `(i / 3) % 2` and the loader for `kv_empty` with parity `1 - (i / 3) % 2` (`LdShape`,
  `MmShape`).
* `ready_open_iff`, `empty_open_iff`: the MMA's poll for block `i` is `Open` exactly at
  `i / 3 + 1` completed phases of `kv_ready` when the barrier has completed `i / 3` or
  `i / 3 + 1` phases (it cannot be further ahead: the next phase needs the next use's copies);
  the loader's poll for block `i` is `Open` exactly at `i / 3` completed phases of `kv_empty`
  when the barrier has completed `i / 3 - 1` or `i / 3` phases (the loader's earlier poll
  already needed `i / 3 - 1`).
* `loaderBlock`, `loader_parity`, `mma_parity`: a thread's `n`-th successful poll of a slot's
  barrier uses parity `(n + δ) % 2`, with offset `δ = 0` for the MMA warp's polls of
  `kv_ready`, `δ = 1` for the loader's polls of a fresh slot's `kv_empty` and `δ = 0` for the
  loader's polls of a prologue slot's `kv_empty` (whose first poll is for use 1).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring

/-! ### Slots, uses, blocks -/

/-- The ring slot of block `i`. -/
def slot (i : Nat) : Nat := i % 3

/-- The use of its slot that block `i` is. -/
def use (i : Nat) : Nat := i / 3

/-- The block that is use `u` of slot `s`. -/
def blockOf (s u : Nat) : Nat := 3 * u + s

/-! ### The unified schedule -/

/-- Who issues block `i`: the prologue for the first `np` blocks, the loader for the others. -/
inductive Issuer where
  | prologue
  | loader

/-- The issuer of block `i` when the prologue preloads `np` blocks. -/
def issuer (np i : Nat) : Issuer := if i < np then .prologue else .loader

/-- The use number of the loader's `n`-th block of slot `s`: the slot's use 0 is the prologue's
when `s < np`, so the loader's first block of that slot is its use 1. -/
def loaderUse (np s n : Nat) : Nat := n + if s < np then 1 else 0

/-- The loader's `n`-th block of slot `s`. -/
def loaderBlock (np s n : Nat) : Nat := blockOf s (loaderUse np s n)

/-! ### Parity and phases -/

/-- The parity of the MMA warp's poll of `kv_ready` for block `i` (`MmShape`). -/
def readyParity (i : Nat) : Nat := use i % 2

/-- The parity of the loader's poll of `kv_empty` for block `i` (`LdShape`). -/
def emptyParity (i : Nat) : Nat := 1 - use i % 2

/-- A poll of parity `p` of a barrier that has completed `c` phases succeeds: the phase of
parity `p` is the last completed one, or the barrier is fresh and `p` is odd. -/
def Open (p c : Nat) : Prop := p % 2 = (c + 1) % 2

end PTX.Kernels.InklingRelDecode.Proof.Ring
