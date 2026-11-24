-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RankDefs
public import Lemmas.Tmem.PairProtocol

@[expose] public section

/-! # A thread's paired Tensor Memory operations

Warp 0 of every CTA makes three paired Tensor Memory operations (`cta_group::2`): the
allocation in the prologue, and at the consumer's exit the permit relinquishment and the
deallocation. The operations a thread has made and the shape of its `n`-th operation are the
library's (`Tmem.Pair.tmemOps`, `Tmem.Pair.TmemShape`); this file gives the count a state implies
(`ThreadD.tmemOps`, by whether the thread is in warp 0), the site of the `n`-th operation
(`tmemPc`), the state after it (`TmemAfter`), and where in the rank table a thread of warp 0 is
before it (`TmemStage`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX

noncomputable section

export PTX.Tmem.Pair (isTmemOp tmemOps TmemShape lt_of_tmemShape)

/-- A list of events without undefined behaviour. -/
def NoUb (es : List Event) : Prop := ∀ e ∈ es, ∀ f, e.kind ≠ .ub f

/-- The operations before a state, for a thread in warp 0 (`w0`) or not: none before the
allocation, one until the relinquishment, two until the deallocation, three after it. A prologue
state counts the allocation by the warp index the shuffle returned. -/
def ThreadD.tmemOps (w0 : Bool) : ThreadD → Nat
  | .inl p => match p.site with
    | .shfl | .elect | .init _ | .alloc => 0
    | .allocWrite | .warpBar => 1
    | _ => if p.w = 0 then 1 else 0
  | .inr (.cons c) =>
    if w0 then (match c.site with | .ldBase | .dealloc => 2 | .exit => 3 | _ => 1) else 0
  | .inr _ => 0

/-- Only warp 0 holds the states around its operations. -/
def ThreadD.TmemWarp (w0 : Bool) : ThreadD → Prop
  | .inl p => p.site = .alloc ∨ p.site = .allocWrite ∨ p.site = .warpBar → p.w = 0
  | .inr (.cons c) => c.site = .relinquish ∨ c.site = .ldBase ∨ c.site = .dealloc → w0 = true
  | .inr _ => True

/-- A state at a paired Tensor Memory operation. -/
def ThreadD.AtTmem : ThreadD → Prop
  | .inl p => p.site = .alloc
  | .inr (.cons c) => c.site = .relinquish ∨ c.site = .dealloc
  | .inr _ => False

/-- The program position of a thread's `n`-th operation. -/
def tmemPc : Nat → Nat
  | 0 => Flow.tmemAlloc_0
  | 1 => Flow.tmemRelinquish_0
  | _ => Flow.tmemDealloc_0

/-- The state after a thread's `n`-th operation: the allocation's write or the warp barrier, the
read of the column, the exit. -/
def TmemAfter : Nat → ThreadD → Prop
  | 0, d => ∃ p : Prologue.D, d = .inl p ∧ (p.site = .allocWrite ∨ p.site = .warpBar)
  | 1, d => ∃ c : Consumer.D, d = .inr (.cons c) ∧ c.site = .ldBase
  | _, d => ∃ c : Consumer.D, d = .inr (.cons c) ∧ c.site = .exit

/-- Where a thread of warp 0 that has made `n` operations is in the rank table: in the prologue
at most at the allocation, then at most at the relinquishment, then at most at the
deallocation. -/
def TmemStage : Nat → ThreadD → Prop
  | 0, d => ∃ p : Prologue.D, d = .inl p ∧ p.site.vtime ≤ 40
  | 1, d => d.exitOff = none ∨ ∃ o, d.exitOff = some o ∧ o ≤ 4
  | 2, d => ∃ o, d.exitOff = some o ∧ o ≤ 8
  | _, _ => True

end
end PTX.Kernels.Fp16Gemm8192.Proof
