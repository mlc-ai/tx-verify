-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Interface
public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Tables

@[expose] public section

/-! # The reference invariant of the CarryLoad phase (instructions 622 to 1402): statement

**How the code is laid out.** After the second `bar.sync 0` of the conversion (621) a compute
thread executes 128 loads, load `j` at instruction `765 + 5 j`:

    add.s64 %rdA, %rd4, K j      the base pointer of the thread moved by the constant `kOf j`
    shr.u64, and.b64, xor.b64    the swizzle of the moved address
    ld.b32  %r, [%rdD]           the generic load of four bytes into the carry register

so the phase has 130 sites: the loads `load_31` to `load_158`, the proxy fence `fenceProxy_1`
(1401) and the barrier `bar_5` (1402). The four pointer instructions of load `j + 1` are local
code between load `j` and load `j + 1`: in the thread machine they are the transition of load
`j`, which continues only if the moved pointer stays inside the shared window (the run's
condition). A thread of the load or the store warp enters at the fence.

**Positions.** A position (`Pos`) is a site of the phase before the exit: `ld j` (carry load
`j < 128`) or `fence`. The state at `bar_5` is the exit (`Interface.lean: Exit`), which is the
entry of the tile loops; it is not a position.

**The invariant** (`Inv`) of a state before the thread's event `k`, for a thread that entered
the phase at its event `k0`: a position; the registers that no code of the phase writes
(`Conversion.Keep`) and, at a load, the role fact (a compute thread) and the two opaque slots
that hold generic pointers, in closed form (`AtPos`: the base pointer `%rd4`, and the pointer
of the load, the swizzled address of the base plus the load's constant); the ledger of the
first `k` events, which is the entry's (five `bar.sync 0`); and the number of events since the
entry (`k = k0 + done pos`), so that the position, and with it the entry a load reads, is a
function of the event's index.

The invariant says nothing about the values of the carry registers: they are opaque data of
the thread machine (the value layer follows them, `Proof/Values/Ends/CarryLoad.lean`).

Abbreviations: `W n` is the 64-bit word of `n`; `sptr g a` is the generic pointer to address
`a` of the shared window of the thread's own block; `swzN` is the kernel's swizzle of an
address (bit 4 is flipped when bit 7 is set); `carryBase P g` is the address the base pointer
`%rd4` of thread `g` holds: the shared base plus `1024 warp + 64 (lane % 4) + 4 (lane / 4)`
(all three from `Conversion/Interface.lean`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion (Keep sptr swzN carryBase)

noncomputable section

/-! ### The sites and registers of the 128 loads -/

/-- **The site of carry load `j`** (`load_31` to `load_158`), and for `j ≥ 128` the site after
the last load (the proxy fence at instruction 1401). The value layer's `Values.Ends.carrySite`
is the same function. -/
def ldSite (j : Nat) : Site := if h : j < 128 then .load ⟨31 + j, by omega⟩ else .fenceProxy 1

/-- The opaque slot of the pointer that carry load `j` reads through (`%rd116`, `%rd120`, …:
register `%rd(116 + 4 j)`). -/
def ptrReg (j : Nat) : Nat := 2362 + 4 * j

/-- The opaque slot of the carry register that load `j` writes (`%r1907` down to `%r1812` for
the first 96 loads, then `%r1908` up to `%r1939`). -/
def dstReg (j : Nat) : Nat := if j < 96 then 2213 - j else 2118 + j

/-- **The address carry load `j` of thread `g` reads**: the swizzled address of the thread's
base pointer plus the constant of the load. -/
def ldAddr (P : Params) (g j : Nat) : Nat := swzN (carryBase P g + kOf j)

/-! ### Positions -/

/-- The sites of the CarryLoad phase before its exit: the 128 carry loads of a compute thread
and the proxy fence. -/
inductive Pos where
  | ld (j : Fin 128)
  | fence
  deriving DecidableEq

/-- The site of a position. -/
def Pos.site : Pos → Site
  | .ld j => ldSite j.val
  | .fence => .fenceProxy 1

/-- **The registers at a position.** At carry load `j`: the thread is a compute thread, the
slot of `%rd4` holds the base pointer of the thread's carry loads, and the slot of the load's
pointer register holds the pointer to the address the load reads. At the fence nothing is
needed (the kept registers are in `RefAt`). -/
def AtPos (P : Params) (g : Nat) : Pos → D → Prop
  | .ld j, d => tid g < 128 ∧ d.x 2250 = sptr g (carryBase P g) ∧
      d.x (ptrReg j.val) = sptr g (ldAddr P g j.val)
  | .fence, _ => True

/-- **The reference invariant of a state at a position**: the site, the registers the phase
never writes, the position's registers. -/
structure RefAt (P : Params) (g : Nat) (pos : Pos) (d : D) : Prop where
  site : d.site = pos.site
  keep : Keep P g d
  pos : AtPos P g pos d

/-! ### The number of events and the invariant -/

/-- **The number of events of the phase before a position**: `j` at carry load `j`; at the
fence, the 128 loads of a compute thread and none of a thread of the load or the store warp. -/
def done (g : Nat) : Pos → Nat
  | .ld j => j.val
  | .fence => if tid g < 128 then 128 else 0

variable (P : Params) (X : Execution) (g : Nat)

/-- **The invariant of the CarryLoad phase** before the thread's event `k`, for a thread that
entered the phase at its event `k0`: a position with its registers, the ledger of the entry
(five `bar.sync 0`; no event of the phase before the exit is counted) and the number of events
since the entry. -/
def Inv (k0 k : Nat) (d : D) : Prop :=
  ∃ pos, RefAt P g pos d ∧ Startup.ledOf ((X.tr g).take k) = ledExit g ∧ k = k0 + done g pos

/-- The thread left the CarryLoad phase, which it entered at event `k0`, at or before its
event `k`: the exit condition held at event `k0 + len g`. -/
def Left (L : Launch) (k0 k : Nat) : Prop :=
  k0 + len g ≤ k ∧ ∃ s1, Frame.stateAt (code L) X g (k0 + len g) = some (some s1) ∧
    Out P X g (k0 + len g) s1

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
