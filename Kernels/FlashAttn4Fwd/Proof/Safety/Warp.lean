-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.WarpGuards
public import Lemmas.Flow.PollSynced

@[expose] public section

/-! # The warp-divergence branch of `Unsafe`

`not_warpDivergent_synced` needs three facts of the kernel:

* its guarded uniform instructions are the branches of its wait loops, each right after its
  poll (`poll_guards`, in `WarpGuards`);
* every local step lands at the next position or off the poll branches (`local_lands`): the
  base rules frame their steps, and the two segment assumptions land at the next position of
  their start (pair-even) or at a stop that is not a poll branch (the software `exp2` segments,
  `segStops`, decided on the code);
* two distinct lanes of a warp polling at one position followed by a poll branch different
  objects are ordered in the execution-dependency order (`PollSynced`, EXT-DEPENDENCY-ORDER): in
  `hb`, or, at the loader's and the MMA warp's loop poll branches, through a full-mask
  `elect.sync` or `shfl.sync` instance between them; polls of one object need no order, since
  `Assumptions.pollAgree` (ASM-POLL-AGREE) selects every poll branch.

The last is a fact of the roles' polls and this branch's input. One object per position
(`PollObjUniform`) does not hold here: the MMA warp's KV polls compute their ring slot from the
item and trip, so one position polls different slots in different iterations; lanes of a warp at
different iterations must be ordered instead. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof PTX.Assumption

noncomputable section

set_option maxRecDepth 100000

/-- The software `exp2` segments stop off the poll branches. -/
theorem segStops : kernel.segStopsOk cuteExp2 Assumptions.swExp2Sites = true := by
  decide +kernel

/-- **Every local step of the kernel's assumptions lands at the next position or off the poll
branches.** -/
theorem local_lands {L : Launch} : LocalLands kernel Assumptions.all L := by
  refine LocalLands.of_rules
    (RulesFrame.idealReal (RulesFrame.cons_none (fun _ _ _ _ => rfl)
      (RulesFrame.approxExact ?_)))
    (.cons (.of_none fun _ _ _ => rfl) (.cons (.of_none fun _ _ _ => rfl)
      (.cons (.of_none fun _ _ _ => rfl) (.cons (segmentExact_segLands segStops)
      (.cons pairEvenAt_segLands ?_)))))
  · repeat' first | exact RulesFrame.nil | refine RulesFrame.cons_none (fun _ _ _ _ => rfl) ?_
  · repeat' first | exact .nil | refine .cons (.of_none fun _ _ _ => rfl) ?_

/-- **No warp-divergent execution**, given synchronized polls (polls of different objects
ordered in the execution-dependency order; polls of one object exempt by
`Assumptions.pollAgree`). -/
theorem no_warpDivergent {L : Launch} {X : Execution}
    (hsync : PollSynced L kernel Assumptions.all X) :
    ¬ WarpDivergent L kernel Assumptions.all X :=
  not_warpDivergent_synced poll_guards local_lands hsync

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
