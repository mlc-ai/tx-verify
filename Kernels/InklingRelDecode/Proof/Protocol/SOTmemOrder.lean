-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOTmemCols
public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaExec
public import Lemmas.Tcgen05.TcProgramOrder
public import Lemmas.Flow.NthEv

@[expose] public section

/-!
# The order of the P alias in Tensor Memory

The probabilities `P b` are stored over the first half of the score buffer `S b` (`SOTmemCols`).
Three accesses to the same columns of buffer `b` follow one another, and each is ordered before the
next by the dependency chain below.

1. **The S read, then the P write** (block `i`, softmax threads): a thread of warp `w` and half
   `h` reads `S` columns `[64 h, 64 h + 64)` (`tcgen05.ld` `.16x32bx2`, 64 words, half-split 64) and
   `tcgen05.wait::ld` finishes the read; it stores `P` into `[32 h', 32 h' + 32)` (`tcgen05.st`
   `.16x32bx2`, 32 words, half-split 32). The two halves of a warp share the lanes `0 … 15` of its
   quadrant, so the store of the thread of half 1 (columns `[32, 64)`) overwrites columns that the
   thread of half 0 reads (`[0, 64)`): **the S read of one thread must finish before the P store of
   the other half**. This is `ReadBefore .ld` (`WaitBefore .waitLd`): the thread's `wait::ld`
   before the barrier `bar.sync 0, 128` that every thread passes between its `wait::ld` and its
   `tcgen05.st` (the sites `bar20`), a named-barrier ordering: **a premise** (`PAliasSync`).
2. **The P write, then the PV read** (`SOHandoff.p_store_before_read`): proved from the premise of
   the `p_ready` handoff.
3. **The PV read, then the next QK write** (this file): the PV MMAs of block `i - 1` read `P` from
   Tensor Memory (A operand, `s.aTmem.isSome`) in iteration `i`; the QK MMAs of block `i + 1` are
   issued in iteration `i + 1` into the same buffer, **after the PV MMAs of block `i - 1` in the
   MMA warp's program order** (`pv_before_qk_exec`, from the commit counts: the `o_done` commit of
   iteration `i` separates them), and an MMA that reads A from Tensor Memory is pipelined before
   every later MMA of its thread (`Pipelined.of_aRead_po`): `ReadBefore .a`
   (`aRead_before_qk`). So the QK write cannot overtake the PV read of the same columns, with
   no wait between them. **This is the chain the S/P alias safety rests on.**

The order of the QK MMAs themselves (writing the same buffer one use apart) is the D-write/D-write
pipelining of one thread (`Before.of_mma_po`, same accumulator).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt trace_of countP_take_split)
open PTX.Kernels.InklingRelDecode.Proof.EvW (oDone)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {X : Execution}

/-- **The A read of an MMA from Tensor Memory is before every later MMA of its thread**: the A-read
and D-write of a later MMA are a pipelined pair (§9.7.18.6.2), so the write cannot pass the read. -/
theorem aRead_before_later_mma {x y : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} (hx : X.MmaIssue x d s acc mask) (ha : s.aTmem.isSome)
    (hy : X.MmaIssue y d' s' acc' mask') (hg : x.1 < L.threads) (hthr : x.1 = y.1)
    (hlt : x.2 < y.2) : ReadBefore L X .a x y :=
  .inr (.inr (.inl (Pipelined.of_aRead_po hx ha hy hg hthr hlt)))

/-! ### The program order of the MMA warp: the PV of block `i - 1` before the QK of block `i + 1` -/

variable {Q : Params} {g : Nat} {mem0 : Mem0} (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g)
include hpre hw

end
end PTX.Kernels.InklingRelDecode.Proof.SO
