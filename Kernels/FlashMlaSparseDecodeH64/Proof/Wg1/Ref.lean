-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Machine

@[expose] public section

/-! # Warpgroup 1's head: its reference invariant

`HRef L g s sh`: at head site `s`, with `sh` shuffles among the thread's events before it. Before
the head's shuffle the thread made the startup's two and is in warpgroup 1; after it, three, and
the exit is the launch's warp's: warp 4 at the MMA exit, warp 5 at the TMA exit, warp 4, 5 or 6 at
the idle exit, warp 7 at the index exit (the dispatch's word is the launch's warp word, which
the following premise owes, `Common/Recv.lean`). These are the facts the sub-entries' gates
(`subSel`) read. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX

/-- **The head's reference invariant.** -/
def HRef (L : Launch) (g : Nat) (s : Site) (sh : Nat) : Prop :=
  match s with
  | .smr | .hsh => sh = 2 ∧ wgOf L g = 1
  | .mma => 3 ≤ sh ∧ warpOf L g = 4
  | .tma => 3 ≤ sh ∧ warpOf L g = 5
  | .index => 3 ≤ sh ∧ warpOf L g = 7
  | .idle => 3 ≤ sh ∧ 4 ≤ warpOf L g ∧ warpOf L g < 7

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
