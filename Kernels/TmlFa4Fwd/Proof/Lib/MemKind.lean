-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events
public import Kernels.TmlFa4Fwd.Spec

@[expose] public section

/-! # Memory events and the launch's words

`MemKind`: an event whose kind accesses memory (an access of the thread, a copy, a tensor copy or
store, an MMA). `InWord`: a footprint of one 32-bit word of the launch's inputs: a cumulative query
offset, a used-K length, a page-table entry. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX

/-- The event accesses memory. -/
def MemKind : Kind → Prop
  | .rd .. | .wr .. | .nc .. | .rmw .. | .copy .. | .tensorIssue .. | .tensorStore .. => True
  | .tc (.mma ..) => True
  | _ => False

/-- **The footprint is one word of the launch's scheduler inputs or of its page table.** -/
def InWord (p : Params) (a : Acc) : Prop :=
  a.size = 4 ∧
    ((∃ i ≤ p.batch, a.loc = globalLoc (p.cuQBase + 4 * i)) ∨
      (∃ i < p.batch, a.loc = globalLoc (p.usedKBase + 4 * i)) ∨
      ∃ i < p.batch, ∃ q < (p.kLength i + 15) / 16,
        a.loc = globalLoc (p.pageTableBase + 4 * (i * p.pageTableStride + q)))

end PTX.Kernels.TmlFa4Fwd.Proof
