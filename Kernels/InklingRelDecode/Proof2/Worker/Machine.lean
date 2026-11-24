-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompMachine
public import Kernels.InklingRelDecode.Proof2.Startup.Base

@[expose] public section

/-! # The worker roles as one fragment

A thread of warps 4 to 7 enters the dispatch loop's head (pc 2337) from the startup and then runs
the dispatch (the `barrier.sync 1`, the role byte's load at pc 2340 and the `brx.idx` on it) and
the role the byte selects: the loader (pc 2344 to 2421), the MMA warp (pc 2422 to 2556), the idle
role (pc 2333 to 2336), the exit path (pc 2853 to 2855) or, for a byte above 3, a pair of
barriers (pc 2557 to 2559). Every role but the exit path returns to the loop's head.

This fragment is the first tree's composed worker machine (`Proof.WComp`, the dispatch loop with
its roles, the return of a role to the loop's head included) entered at the loop's head
(`Worker.Site.loop`) with the inherited registers the startup leaves (`workerPro`). Its states
before the loop's head (the first tree's own copy of the startup, `Worker.Site.bar0` to `shfl`)
are not reached from this entry. Its steps are `WComp.stepAt`.

The machine follows every value but one: the dispatch follows every role byte (`Worker.dispatch`),
the loader every pair of loop bounds and block-table word, the MMA warp every received word; the
MMA role is entered only with a Tensor Memory base word with room for 512 columns
(`WComp.baseOk`), and with another word the machine stops (`some none`). This content stop is
recorded in the development notes (Proof2 round 4); the base word is 0 by the startup's reference.
-/

namespace PTX.Kernels.InklingRelDecode.Proof2.Worker
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

/-- **The inherited registers at the dispatch loop's head**, for the base word `tm`: the
parameter words, the block-table base, the tensor map pointer `%rd1`, `%p3`, the warp index
(`%r3`, `%r4`), the shared base (`%r73`) and the base word (`%r2`). -/
def workerPro (Q : Params) (L : Launch) (g : Nat) (w : Value) : Proof.Loader.Pro where
  rest := fun r =>
    if r = 3 then .pred (decide (g % L.block < 32))
    else if r = 463 then w
    else if r = 464 ∨ r = 465 then b32 (g % L.block / 32)
    else if r = 534 then .bits 32 (Startup.baseW L)
    else if r = 1949 then .ptr 64 true (.param (param "1")) 0
    else b32 0
  w67 := Q.strideBt % 2 ^ 32
  w68 := Q.pageRows % 2 ^ 32
  w69 := Q.headRows % 2 ^ 32
  w70 := Q.headCols % 2 ^ 32
  w71 := Q.splits % 2 ^ 32
  bt := Q.btBase

/-- The fragment's first state: the dispatch loop's head. -/
def init (Q : Params) (L : Launch) (g : Nat) (w : Value) : Proof.WComp.WSt :=
  .worker ⟨.loop, workerPro Q L g w⟩

/-- **The worker fragment** for the base word register's value `w`. -/
@[reducible] def code (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Flow.Code kernel Assumptions.all L g :=
  { Proof.WComp.code L g Q with init := init Q L g w }

end
end PTX.Kernels.InklingRelDecode.Proof2.Worker
