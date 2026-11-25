-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Inv

@[expose] public section

/-! # The Conversion phase of the reference layer: entry and exit (statements)

The Conversion phase is the stretch of the program from instruction 387 to 621, executed by
all 192 threads of a block: the proxy fence at 387, the two loops in which a thread converts
its share of the 128 × 128 FP32 state to bfloat16 (per element one generic `ld.b32` through a
swizzled shared pointer, `cvt.rn.bf16.f32`, one `st.shared.b16` into the bfloat16 copy
`state_acc`), and the two `bar.sync 0` at 620 and 621. Its boundary with the other phases:

* **entry**: the exit of the startup phase (`Startup.Exit`, `Startup.Out`): the state at the
  site `fenceProxy_0` (instruction 387), before its event, with the ledger `Startup.ledExit`;
* **exit** (`Exit`, `Out`): the state after the transition of the second `bar.sync 0` (621),
  which is the first site of the CarryLoad phase: `load_31` (instruction 765) for a compute
  thread, `fenceProxy_1` (instruction 1401) for a thread of the load or the store warp. The
  local code in between (622 to 764) builds the base pointer of the carry loads and clears the
  128 carry registers.

**What a thread converts.** The state has 16384 elements; element `e` is the 2-byte slot at
offset `2 e` of `state_acc` (the first 32768 bytes of the block's shared window) and is read
from the FP32 buffer (offsets 32768 to 98304) at the *swizzled* address of offset `4 e`. A
thread of warp `w` and lane `l` converts the elements `slot0 g r` and `slot0 g r + 1` for the
*pairs* `r < pairs g`: pair `r` has the *pair index* `w + 6 r` (below 256), and
`slot0 g r = 1024 (i % 16) + 64 (i / 16) + 2 l` for the pair index `i`. A compute thread has 43
pairs (86 elements), a thread of the other two warps 42 (84 elements). The first `head g`
pairs (3 or 2) are converted by the first loop (instructions 406 to 452, one pair a round), the
other 40 by the second loop (453 to 618, four pairs a round).

**The swizzle.** The kernel computes the address of a generic access as
`p ^ ((p >> 3) & 16)` for the pointer `p` (the assumption `sharedBits` reads the three
instructions on the pointer's offset in the block's window): bit 4 of the address is flipped
when bit 7 is set. `swzN` is that function on numbers.

Abbreviations: `S` is the shared base `P.sharedBase`; `W n` is the 64-bit word of the number
`n`; a register is named by its id in the generated thread machine. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

/-! ### The numbers of the phase -/

/-- The number of rounds of the first loop (one pair a round): 3 for a compute thread, 2 for a
thread of the load or the store warp. -/
def head (g : Nat) : Nat := if warp g < 4 then 3 else 2

/-- The number of pairs of elements a thread converts: 43 for a compute thread, 42 for a
thread of the other two warps. -/
def pairs (g : Nat) : Nat := head g + 40

/-- The pair index of the `r`-th pair of a thread (the loop variable `%r1795`): the warp index
plus six times the ordinal. -/
def pairIx (g r : Nat) : Nat := warp g + 6 * r

/-- The even element of the `r`-th pair of a thread (the index `%r245` of the code). -/
def slot0 (g r : Nat) : Nat :=
  1024 * (pairIx g r % 16) + 64 * (pairIx g r / 16) + 2 * lane g

/-- **The `i`-th element a thread converts**, for `i < 2 * pairs g`: the two elements of a pair
follow each other. -/
def slotOf (g i : Nat) : Nat := slot0 g (i / 2) + i % 2

/-- The swizzle of a shared address: bit 4 is flipped when bit 7 is set. -/
def swzN (n : Nat) : Nat := n ^^^ ((n >>> 3) &&& 16)

/-- **The address a thread reads element `e` from**: the swizzled address of offset `4 e` of
the FP32 buffer. -/
def rdAddr (P : Params) (e : Nat) : Nat := swzN (P.sharedBase + 32768 + 4 * e)

/-- **The address a thread writes element `e` to**: offset `2 e` of `state_acc`. -/
def wrAddr (P : Params) (e : Nat) : Nat := P.sharedBase + 2 * e

/-- The generic pointer to address `n` of the shared window of the thread's own block: what a
pointer register (an opaque slot of the thread machine) holds. -/
def sptr (g n : Nat) : Value := .ptr 64 true (.shared (cta g) (cta g)) (W n)

/-- **The base of the carry loads of a compute thread** (the pointer `%rd4`, built at the
instructions 622 to 631): the shared base plus `1024 w + 64 (l % 4) + 4 (l / 4)` for warp `w`
and lane `l`. The `j`-th carry load reads at the swizzled address of this base plus a constant
of the code. -/
def carryBase (P : Params) (g : Nat) : Nat :=
  P.sharedBase + (1024 * warp g + 64 * (lane g % 4) + 4 * (lane g / 4))

/-! ### The registers that the two phases carry -/

/-- **The registers of the startup phase's exit**, which the Conversion and CarryLoad phases
read but never write: the thread and warp index and the pointer to the offsets array
(`Startup.Base`: `%r1`, `%r2`, `%rd1`), the six role flags (`%p83` to `%p88`),
`%cluster_ctarank` (`%r46`), the results of the scan (`Startup.Scan`: `%r8`, `%r9`, `%r1793`,
`%rd2`) and the flag of the election at instruction 312 (`%r180`). -/
structure Keep (P : Params) (g : Nat) (d : D) : Prop where
  base : Startup.Base P g d
  flags : Startup.Flags g d.p
  rank : d.w 352 = W 0
  scan : Startup.Scan P g d
  elected : d.w 486 = W (if lane g = 0 then 1 else 0)

theorem Keep.of_exit {P : Params} {g : Nat} {d : D} (h : Startup.Exit P g d) : Keep P g d :=
  ⟨h.base, h.flags, h.rank, h.scan, h.elected⟩

/-! ### The entry -/

/-- **The entry condition of the Conversion phase**: the exit of the startup phase, the state
at the proxy fence of instruction 387 before its event. -/
abbrev Entry (P : Params) (g : Nat) (d : D) : Prop := Startup.Exit P g d

/-- The entry condition before the thread's event `k`, with the ledger. -/
abbrev In (P : Params) (X : Execution) (g k : Nat) (d : D) : Prop := Startup.Out P X g k d

/-! ### The exit -/

/-- **The state at the exit of the Conversion phase** (the entry of the CarryLoad phase): the
carried registers; a compute thread is at its first carry load (`load_31`, instruction 765)
with the base pointer of the carry loads in `%rd4` and the swizzled address of the first load
in `%rd116`; a thread of the load or the store warp is at the proxy fence of instruction
1401. -/
structure Exit (P : Params) (g : Nat) (d : D) : Prop where
  keep : Keep P g d
  site : d.site = if tid g < 128 then .load 31 else .fenceProxy 1
  base : tid g < 128 → d.x 2250 = sptr g (carryBase P g)
  first : tid g < 128 → d.x 2362 = sptr g (swzN (carryBase P g + 32768))

/-- The number of events of the Conversion phase of a thread: the proxy fence, a load and a
store per element, two `bar.sync 0`. -/
def len (g : Nat) : Nat := 3 + 4 * pairs g

/-- **The ledger at the exit**: the startup's, with five `bar.sync 0` (the phase adds no
mbarrier event, no tensor load and no shuffle). -/
def ledExit (g : Nat) : Startup.Led :=
  ⟨5, (Startup.ledExit g).inits, (Startup.ledExit g).arrs, (Startup.ledExit g).issues, 1, 3⟩

/-- **The exit condition of the Conversion phase** before the thread's event `k`. -/
def Out (P : Params) (X : Execution) (g k : Nat) (d : D) : Prop :=
  Exit P g d ∧ Startup.ledOf ((X.tr g).take k) = ledExit g

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
