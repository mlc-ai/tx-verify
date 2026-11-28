-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

/-! # The rendezvous schedule of a worker lane

A worker thread (warps 4 to 7) meets the CTA barriers at the two startup syncs (12, 14), the
dispatch round's publication sync (2338), the two syncs of its role (idle warps 4 and 5: 2334 and
2335; the loader, warp 6: the begin and end of its loop; the mma warp, 7: its two), the second
dispatch round's sync (2338) and the final sync (2853). `workerBar w t` is the pc of the `t`-th. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- The two rendezvous of the role of warp `w`. -/
def workerMid (w : Nat) : List Nat :=
  if w < 6 then [2334, 2335] else if w = 6 then [2346, 2419] else [2424, 2554]

def workerBar (w t : Nat) : Nat := ([12, 14, 2338] ++ workerMid w ++ [2338, 2853]).getD t 0

theorem workerBar_fixed (w : Nat) : workerBar w 0 = 12 ∧ workerBar w 1 = 14 ∧
    workerBar w 2 = 2338 ∧ workerBar w 5 = 2338 ∧ workerBar w 6 = 2853 := by
  unfold workerBar workerMid
  split
  · simp
  · split <;> simp

theorem workerBar_idle {w : Nat} (h : w < 6) :
    workerBar w 3 = 2334 ∧ workerBar w 4 = 2335 := by
  simp [workerBar, workerMid, h]

theorem workerBar_loader : workerBar 6 3 = 2346 ∧ workerBar 6 4 = 2419 := by
  simp [workerBar, workerMid]

theorem workerBar_mma : workerBar 7 3 = 2424 ∧ workerBar 7 4 = 2554 := by
  simp [workerBar, workerMid]

end PTX.Kernels.InklingRelDecode.Proof.Lib
