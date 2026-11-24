-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Code
public import Kernels.TmlFa4Fwd.Proof.Progress.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Issue
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

/-! # The kind of the instruction at each site of the MMA warp -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

private def mmaSites : List Mma.Site :=
  [.bar1, .ldAlloc, .bcast, .q0, .q1, .uk] ++
  ([Epilogue.Scan.first, .loop, .second, .loop2].flatMap fun k =>
    [.word k, .down k, .total k] ++ (List.finRange 5).map (.up k)) ++
  ([false, true].flatMap fun l =>
    [.vote l, .pre l, .tiles l, .relinq l, .bar2 l, .dealloc l, .exit l]) ++
  (List.finRange 14).map .sh ++ (List.finRange 12).map .ce ++ (List.finRange 12).map .cm ++
  (List.finRange 4).flatMap fun b => [.eq b, .ep b] ++ (List.finRange 8).map (.qk b) ++
    (List.finRange 8).map (.pv b)

private theorem mma_kinds : mmaSites.all (fun s => siteOk s.pc false false) = true := by
  decide +kernel

/-- **A site of the MMA warp that is no poll** has a checked instruction. -/
theorem mma_kind {s : Mma.Site} (h : Progress.isPoll s = false) :
    siteOk s.pc false false = true := by
  refine List.all_eq_true.mp mma_kinds s ?_
  cases s with
  | bar1 | ldAlloc | bcast | q0 | q1 | uk => simp [mmaSites]
  | word k | down k | total k => cases k <;> simp [mmaSites]
  | up k j => cases k <;> simp [mmaSites]
  | vote l | pre l | tiles l | relinq l | bar2 l | dealloc l | exit l => cases l <;> simp [mmaSites]
  | wt k => simp [Progress.isPoll] at h
  | mw b ld => simp [Progress.isPoll] at h
  | sh k | ce k | cm k => simp [mmaSites]
  | eq b | ep b => simp [mmaSites]
  | qk b j | pv b j => simp [mmaSites]

/-- The allocation prefix: the register request, then the allocation. -/
theorem mma_start_kind {s : Mma.Start} (h : s ≠ .enter) :
    siteOk s.pc false (decide (s = .set)) = true := by
  cases s with
  | set => decide +kernel
  | alloc | wr => decide +kernel
  | enter => exact absurd rfl h

end PTX.Kernels.TmlFa4Fwd.Proof.Top
