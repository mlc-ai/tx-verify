-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Core.Assumption.IdealReal
public import Core.Assumption.ApproxExact
public import Core.Assumption.CommitOrder
public import Core.Assumption.PollAgree
public import Core.Assumption.SetMaxNRegSync
public import Kernels.InklingRelDecode.Assumptions.Exp2Template
public import Kernels.InklingRelDecode.Assumptions.Numerics
public import Kernels.InklingRelDecode.Assumptions.InputReadOnly

@[expose] public section

/-!
# The assumptions of the Inkling relative decode kernel

Each assumption is built from a constructor in `Core/Assumption/` where one covers the form, and
is a kernel-local `Assumption` limited to the instruction forms or instruction indices (pcs) that
need it where none does. `Audit/AssumptionSites.lean` checks the pc lists against the decoded
program.

`all` lists: the exact readings of the floating arithmetic (`idealArith`, `approx`, `swExp2`,
`lg2Exact`, `divFullExact`, `negExact`, `bf16Exact`), the commit order of two `tcgen05.commit`
sites (`commitOrder`), the poll branches (`pollAgree`), the `setmaxnreg` request without a
warpgroup synchronization (`setMaxNRegSync`) and the read-only input tensors (`inputReadOnly`,
`Assumptions/InputReadOnly.lean`: a plain `ld.global` at one of the 203 global loads returns the
launch content; a write of a byte such a read reads is undefined). The kernel needs no cluster
or `tcgen05.ld` wait assumption.
-/

namespace PTX.Kernels.InklingRelDecode.Assumptions
open PTX

/-- The kernel's floating computation that has an exact `.rn` (or rounding-free) meaning is read
as exact real arithmetic: the `kind::f16` MMAs with bf16 inputs and an f32 accumulator for
`S = Q Kᵀ` and `O += P V`; the `.f32` `add`, `mul`, `fma`, `sub`; the `.f32x2` `add`, `mul` and
`fma`; `min.f32` and `max.f32`; and the floating `setp`. -/
noncomputable def idealArith : Assumption :=
  Assumption.idealReal "inkling-ideal-arith"
    { float := [.add .f32, .mul .f32, .fma .f32, .subRn .f32, .mulF32x2, .addRnF32x2,
        .fmaRnF32x2, .min .f32, .max .f32, .setp .f32, .setpInf .f32],
      mma := [.f16 .bf16 .f32] }
    "The kernel computes S = Q K^T and O += P V with kind::f16 MMAs on bf16 inputs, and the \
    softmax scores, row maxima, row sums, rescaling and masks with f32 and f32x2 arithmetic; PTX \
    rounds these (\".rn mantissa LSB rounds to nearest even\") while the theorem states the exact \
    real attention."

/-- `ex2.approx.ftz.f32` (65 sites: the softmax exponentials and the rescale factor) is read as
the exact `2 ^ x` and `rcp.approx.ftz.f32` (1 site: the final normalization) as the exact
`1 / x`. -/
noncomputable def approx : Assumption :=
  Assumption.approxExact "inkling-approx-ex2-rcp" [.ex2 .f32, .rcp .f32]
    "The kernel computes the softmax exponentials with ex2.approx.ftz.f32 and the reciprocal of \
    the row sum with rcp.approx.ftz.f32; the theorem states the exact attention, so these are \
    read as the exact 2^x and 1/x, ignoring their ulp error and the flush of subnormal results \
    to zero."

/-- The `tcgen05.commit` sites of the MMA warp whose arrive-ons no wait observes and whose order
the CTA's exit relies on: the `kv_empty` commit (`Mma.Site.pvCommit1`, pc 2546) and the `o_done`
commit (`Mma.Site.pvCommit2`, pc 2548). -/
def commitOrderSites : List Nat := [2546, 2548]

/-- **The arrive-ons of the MMA warp's `kv_empty` and `o_done` commits are performed before the
arrive-on of the thread's next commit** (`Assumption.commitOrderAt`; approved by the user,
2026-11-18). The reading, as for FlashAttention-4's last Q-empty commit: one thread's
`tcgen05.commit`s at these two sites signal their mbarriers in issue order.

Why the kernel needs it. ERR-SHARED-LIFETIME reads PTX ISA 9.5, §2.2.2: "The executing CTA has to
make sure that the shared memory of the peer CTA exists before communicating with it via shared
memory and the peer CTA hasn’t exited before completing the shared memory operation." as: the
arrive-on of an asynchronous `tcgen05.commit` on an mbarrier in a CTA's shared memory completes
before that CTA exits. Some commit arrive-ons of this kernel have no waiting observer: the last
three `kv_empty` commits (the loader's ring waits stop before them: it does not drain the ring)
and the last `o_done` commit (the softmax warps wait for `o_done` in the iterations `i > 0`, and
the last `o_done` commit is issued after the last of those waits). Each of them is followed on
the MMA warp's program order by another commit whose arrive-on is observed: a `kv_empty` commit
by the `o_done` commit of its block (or by the `s_ready` commit of the next iteration) and the
last `o_done` commit by the `o_final` commit, which the epilogue's wait observes in every launch
(the second kernel fix moved that wait out of `if num_iters > 0`). The sites 2546 and 2548 chain
every unobserved arrive-on to an observed one.

The manual does not give this order. The commit description says: "track the completion of all the
prior asynchronous tcgen05 operations, as listed in mbarrier based completion mechanism , initiated
by the executing thread" (`tcgen05.commit`), and the list of §9.7.18.6.2.1.1 reads: "Completion of
the following instruction’s asynchronous operations is observed through the mbarrier based waiting
mechanism: tcgen05.mma tcgen05.cp tcgen05.shift tcgen05.commit is used to track the completion of
the above asynchronous instructions." An earlier commit is not among the operations a commit
tracks, and §9.7.18.6.2 states: "The asynchronous tcgen05 operations may execute and complete in a
different order than they were issued." The assumption covers that gap for these two commit
sites. -/
def commitOrder : Assumption :=
  Assumption.commitOrderAt "inkling-commit-order" commitOrderSites
    "The Inkling MMA warp never waits for its last three kv_empty tcgen05.commit arrive-ons or its \
    last o_done arrive-on; the CTA's exit relies on each being performed before the arrive-on of \
    the thread's next commit, which is observed."

/-- The six guarded `bra.uni` sites after an `mbarrier.try_wait`: the softmax `s_ready` (1258) and
`o_done` (2240) polls, the loader's `kv_empty` (2375), the MMA warp's `kv_ready` (2463) and
`p_ready` (2511) polls, and the epilogue's `o_final` (2566). Each is
`@!complete bra.uni waitLoop` right after the poll. -/
def pollAgreeSites : List Nat := [1258, 2240, 2375, 2463, 2511, 2566]

/-- At the six poll branches, two lanes' executions after polls of one mbarrier are not compared,
whatever the polls' parities (ASM-POLL-AGREE; same reading and same manual basis as FlashAttention-4
and the fp16 GEMM). -/
def pollAgree : Assumption :=
  Assumption.pollAgreeAt "inkling-poll-agree" pollAgreeSites
    "The Inkling decode kernel spins on all 32 lanes of a warp at each of its six waits with \
    mbarrier.try_wait; @!complete bra.uni waitLoop: lanes polling one phase in one round are not \
    ordered, so without the assumption two lanes of a warp may take different branches."

/-- The one `setmaxnreg` request site that follows another request of its warpgroup without a
synchronization: the `setmaxnreg.inc 256` at the head of the worker dispatch loop (pc 2337). -/
def regSyncSites : List Nat := [2337]

/-- **The `setmaxnreg.inc 256` at the head of the worker dispatch loop is not preceded by a
warpgroup synchronization** (`Assumption.setMaxNRegSyncAt`, ASM-SETMAXNREG-SYNC; approved by the
user, 2026-11-18). PTX ISA 9.5, §9.7.21.5: "After executing a setmaxnreg instruction, all warps in
the warpgroup must synchronize explicitly before executing subsequent setmaxnreg instructions."

Gluon's `warp_specialize` lowering emits this code: a worker warp enters the loop with
`setmaxnreg.dec 24`, two `barrier.sync 1`, `setmaxnreg.inc 256` (pc 2336) and then the loop-head
`setmaxnreg.inc 256` (pc 2337) with no synchronization in between; the role tails (the loader at
pc 2420 and the MMA warp at pc 2555) restore 256 with a `setmaxnreg.inc 256` and branch straight
back to the same loop-head `setmaxnreg.inc 256`, again with no warpgroup synchronization. The
generated code therefore formally violates the quoted sentence. Both requests are to 256, so the
second one requests no change. The assumption exempts only the requests at pc 2337 from the
requirement that the previous request of the warpgroup is ordered before them; the direction,
count, warpgroup and same-ordinal checks stay. The code-generation pattern should be reported to
Triton. -/
def setMaxNRegSync : Assumption :=
  Assumption.setMaxNRegSyncAt "inkling-setmaxnreg-sync" regSyncSites
    "The worker dispatch loop of the warp-specialized kernel restores the register count and \
    branches back to a second setmaxnreg.inc to the same count, with no warpgroup \
    synchronization between the two requests."

/-- All assumptions of the Inkling theorems. -/
noncomputable def all : List Assumption :=
  [idealArith, approx, swExp2 kernel, lg2Exact, divFullExact, negExact, bf16Exact,
    commitOrder, pollAgree, setMaxNRegSync, inputReadOnly]

end PTX.Kernels.InklingRelDecode.Assumptions
