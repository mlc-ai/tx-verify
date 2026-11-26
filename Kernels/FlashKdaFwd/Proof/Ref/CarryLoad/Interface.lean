-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Interface

@[expose] public section

/-! # The CarryLoad phase of the reference layer: entry and exit (statements)

The CarryLoad phase is the stretch of the program from instruction 622 to 1402, between the
conversion loop and the tile loops. A *compute thread* (thread index in its block below 128)
executes 128 generic `ld.b32` there (instructions 765, 770, …, 1400: the sites `load_31` to
`load_158`), each through a swizzled shared pointer: it loads its 128 entries of the FP32 state
into its *carry registers*, which it keeps across the tile loop. Every thread then executes
`fence.proxy.async.shared::cta` (instruction 1401, the site `fenceProxy_1`: the fence that the
verified artifact adds to the upstream kernel) and `bar.sync 0` (instruction 1402, the site
`bar_5`). Its boundary with the other phases:

* **entry** (`Entry`, `In`): the exit of the Conversion phase (`Conversion.Exit`,
  `Conversion.Out`), the state after the transition of the `bar.sync 0` at 621: a compute
  thread is at its first carry load (`load_31`, instruction 765) with the base pointer of the
  carry loads in `%rd4` and the address of the first load in `%rd116`; a thread of the load or
  the store warp is at the proxy fence (`fenceProxy_1`). The local code 622 to 764 belongs to
  the transition of the barrier at 621 and is evaluated by the Conversion phase.
* **exit** (`Exit`, `Out`): the state at `bar_5` (instruction 1402), *before* the barrier's
  event. It is the entry of the tile loop of the thread's role (`Compute.In`,
  `Producer.Entered`, `Store.In`; `Links.lean` proves the three). The phase writes no control
  register, so the exit state holds the registers the startup phase left (`Conversion.Keep`).

**The ledger** is the startup's (`Startup.Led`: counts by kind of the thread's earlier events).
The phase makes no counted event before its exit: at every state of the phase and at the exit
the ledger is `Conversion.ledExit g`, with five `bar.sync 0`. The barrier at 1402 is the sixth.

**The fence.** The exit condition also says that the event before the exit state is the proxy
fence of instruction 1401 (`FenceBefore`): the protocol layer orders the generic reads of the
state buffer (the conversion loop, the carry loads) before the tile loads through "the sixth
`bar.sync 0` of a thread directly follows a proxy fence of the same thread".

Abbreviations: `W n` is the 64-bit word of the number `n`; a register is named by its id in
the generated thread machine (`%rdN` is `2246 + N`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion (Keep sptr swzN carryBase)

noncomputable section

/-! ### The entry -/

/-- **The entry condition of the CarryLoad phase**: the exit of the Conversion phase. A compute
thread is at its first carry load (`load_31`, instruction 765) with the base pointer of the
carry loads in `%rd4` (slot 2250) and the swizzled address of the first load in `%rd116` (slot
2362); a thread of the load or the store warp is at the proxy fence of instruction 1401. -/
abbrev Entry (P : Params) (g : Nat) (d : D) : Prop := Conversion.Exit P g d

/-- The entry condition before the thread's event `k`, with the ledger (five `bar.sync 0`). -/
abbrev In (P : Params) (X : Execution) (g k : Nat) (d : D) : Prop := Conversion.Out P X g k d

/-! ### The exit -/

/-- **The state at the exit of the CarryLoad phase**: the site `bar_5` (instruction 1402),
before its event, with the registers that the phases from the startup's exit on never write
(`Conversion.Keep`: the thread and warp index, the pointer to the offsets array, the six role
flags, `%cluster_ctarank`, the results of the scan of the offsets array, the flag of the
election at instruction 312). These are the control registers the three tile loops read. -/
structure Exit (P : Params) (g : Nat) (d : D) : Prop where
  keep : Keep P g d
  site : d.site = .bar 5

/-- **The number of events of the CarryLoad phase of a thread**: the 128 carry loads and the
proxy fence for a compute thread, the proxy fence alone for a thread of the load or the store
warp. The exit state is the state before the event with this ordinal after the entry. -/
def len (g : Nat) : Nat := if tid g < 128 then 129 else 1

/-- **The ledger at the exit**: the ledger of the entry (the phase's loads and its fence are in
no counted class): five `bar.sync 0`, the startup's `mbarrier.init`, arrival and tensor load
issues, one successful poll, three shuffles. -/
def ledExit (g : Nat) : Startup.Led := Conversion.ledExit g

/-- **The event before position `k` of thread `g` is the proxy fence of instruction 1401**
(`fence.proxy.async.shared::cta`). -/
def FenceBefore (X : Execution) (g k : Nat) : Prop :=
  0 < k ∧ X.get (g, k - 1) = some ⟨1401, .fenceProxy (.async (some (.shared .cta))) none⟩

/-- **The exit condition of the CarryLoad phase** before the thread's event `k`: the state at
`bar_5` with the kept registers, the ledger with five `bar.sync 0`, and the proxy fence as the
event before. -/
def Out (P : Params) (X : Execution) (g k : Nat) (d : D) : Prop :=
  Exit P g d ∧ Startup.ledOf ((X.tr g).take k) = ledExit g ∧ FenceBefore X g k

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
