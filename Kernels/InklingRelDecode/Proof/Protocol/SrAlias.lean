-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SrCoord

@[expose] public section

/-!
# The S load before the `P` store of the other half (`PAliasSync` for the S loads)

The probabilities alias the first half of the score buffer, and the two halves of a warp share
lanes (`SO.half_overlap`): the `P` store of a thread of half 1 covers columns that the S load of a
thread of half 0 reads. The S load must finish before the store; the protection is the
`bar.sync 0, 128` that every softmax thread passes between its `tcgen05.wait::ld` and its `P` store
(the sites `bar20`).

`SO.PAliasSync` as defined quantifies over every `tcgen05.ld` of the CTA, the epilogue's load of `O`
and the rescale load included. **That statement is false** for the epilogue's `tcgen05.ld` of `O`
and the rescale `tcgen05.st` of the last iteration `n - 1` of the same thread: both have `n`
successful `s_ready` polls before them (the equality hypothesis holds) and cover the same cells of
`O`, and the load comes after the store, so `ReadBefore .ld load store` does not hold. Nothing
uses the definition. `PAliasSyncS` is the statement for the S loads, the loads the premise is
for: its conclusion is `ReadBefore .ld` for a store of the same iteration.

* `SLd`: the S load of iteration `i` by a softmax thread (`.16x32bx2 64` at `tm + 128 (i % 2)` plus
  the lane field, `i + 1` successful `s_ready` polls before it, its `wait::ld` after it, and a
  `bar.sync 0, 128` of the barrier-0 ordinal `ord20 i` after the wait);
* `PStSync`: the `P` store of iteration `i` has `i + 1` successful `s_ready` polls before it and a
  `bar.sync 0, 128` of ordinal `ord20 i` before it;
* `pAliasSync_S`: from `Bar128Causal` (`SrOrder`): the load's wait is before the load thread's
  barrier, which is before the store thread's later events.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InP InO TmOk below2)

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {c cm p0 tm : Nat} {Soft Mma : Nat → Prop}

/-- **The S load of iteration `i`** by the softmax thread `t` (event `lk`). -/
structure SLd (L : Launch) (X : Execution) (c : Nat) (Soft : Nat → Prop) (tm : Nat)
    (ord20 : Nat → Nat) (t lk i a : Nat) (vals : List Value) (sh : TcShape) : Prop where
  soft : Soft t
  shape : sh = .s16x32bx2 64 ∧ vals.length = 64 ∧ ∃ w, a = tm + 128 * (i % 2) + w * 2 ^ 21
  iter : okPolls (sReady L c 0) ((X.tr t).take lk) + okPolls (sReady L c 1) ((X.tr t).take lk) =
    i + 1
  sync : ∃ wl a1 pcw pc1, lk < wl ∧ X.get (t, wl) = some ⟨pcw, .tc .waitLd⟩ ∧ wl < a1 ∧
    X.get (t, a1) = some ⟨pc1, .bar 0 (some 128) .sync⟩ ∧
    ((X.tr t).take a1).countP (Execution.isBarId 0) = ord20 i

/-- **The `P` store of iteration `i`** after the barrier of its iteration. -/
structure PStSync (L : Launch) (X : Execution) (c : Nat) (ord20 : Nat → Nat) (t sk i : Nat) :
    Prop where
  iter : okPolls (sReady L c 0) ((X.tr t).take sk) + okPolls (sReady L c 1) ((X.tr t).take sk) =
    i + 1
  sync : ∃ ab pcb, ab < sk ∧ X.get (t, ab) = some ⟨pcb, .bar 0 (some 128) .sync⟩ ∧
    ((X.tr t).take ab).countP (Execution.isBarId 0) = ord20 i

variable (H : Mbar.Ctx L K A mem0 X c cm p0 Soft Mma) (l : Lane L X c cm p0 tm Soft)
include H l

end
end PTX.Kernels.InklingRelDecode.Proof.Sr
