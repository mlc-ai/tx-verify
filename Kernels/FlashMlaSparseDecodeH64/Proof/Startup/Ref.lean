-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Machine

@[expose] public section

/-! # The startup's reference invariant

`Ref d mi b0`: at state `d`, with `mi` mbarrier initializations and `b0` events on CTA barrier 0
among the thread's events before it. Before the initializations none; before initialization `n`
exactly `n`; at the fence all 23; after the fence path or the path of a lane that lost the
election, `0` or `23`. Barrier 0 has not been passed before the hand-off, once at it. The `trap`
(a nonzero allocation word) has the counts of the read-back; that it is not reached is the
row `AllocRead` (`Iface/AllocRead.lean`), proved from the following theorem. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX

/-- **The startup's reference invariant.** -/
def Ref (d : D) (mi b0 : Nat) : Prop :=
  match d.site with
  | .sh _ | .elect _ => mi = 0 ∧ b0 = 0
  | .init n => mi = n.val ∧ b0 = 0
  | .fence => mi = 23 ∧ b0 = 0
  | .alloc | .allocSt | .ld | .trap | .relinq | .bar => (mi = 0 ∨ mi = 23) ∧ b0 = 0
  | .enter _ => (mi = 0 ∨ mi = 23) ∧ b0 = 1

/-- **The startup's words**: at state `d`, with `sh` shuffles among the thread's events before
it. At shuffle `j` the thread made `j` shuffles, and the first returned the launch's warpgroup
word (`wgW`); after the second both recorded words are the launch's (`wgW`, `warpW`), and on the
path of the elections (`x2 = 0`) the thread is in warp 0. The words are what the shuffles' source
lane sent (`Common/Recv.lean`), which the following premise owes. -/
def RefW (L : Launch) (g : Nat) (d : D) (sh : Nat) : Prop :=
  match d.site with
  | .sh j => sh = j.val ∧ (j.val = 1 → d.x1 = wgW L g)
  | .bar | .enter _ => sh = 2 ∧ d.x1 = wgW L g ∧ d.x2 = warpW L g
  | _ => sh = 2 ∧ d.x1 = wgW L g ∧ d.x2 = warpW L g ∧ warpOf L g = 0

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
