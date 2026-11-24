-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Mma.Places
public import Kernels.TmlFa4Fwd.Proof.Mma.Sim
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape

@[expose] public section

/-! # The times of the MMA warp's states -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The MMA warp -/

namespace Mm

/-- The MMA warp's sites whose event is a warp collective outside the pipeline: the broadcast
before the scan and the scan's shuffles and ballot. -/
def coll (s : Mma.Site) : Bool :=
  match s with
  | .bcast => true
  | s => s.scan && (Out.coll s.toE)

/-- The round of a pipeline state at place `q`: its broadcasts so far are three before the loop,
six per round done, and in the current round or the tail the ones before `q` (all six of the
round from place 38 on, `Mma.shAt`). -/
def round (q : Nat) (v : Mma.V) : Nat :=
  if 38 ≤ q ∧ q < 60 then (v.ps - 9) / 6 else (v.ps - 3) / 6

/-- Pipeline place `q` with `r` rounds done: slot 0 for the first K/V block, slot `r + 1` for
round `r` of the loop and for the tail after `r` rounds; offset `2 q`, so that the odd offsets are
free for the other roles. -/
def pipeT (p : Params) (q r : Nat) : Nat := clk p (if q < 20 then 0 else r + 1) (2 * q)

/-- The end: the permit's hand-back, barrier 2, the deallocation, the return. -/
def endOff : Mma.Site → Option (Bool × Nat)
  | .relinq l => some (l, 0)
  | .bar2 l => some (l, 4)
  | .dealloc l => some (l, 6)
  | .exit l => some (l, 8)
  | _ => none

/-- The scheduler's collectives before a state: the shuffles that are no broadcast of the
pipeline, and the pass's ballot. -/
def scans (d : Mma.D) (n : Cls → Nat) : Nat := n .shfl - d.v.ps + Out.ballots d.site.toE

/-- The time of a state of the allocation prefix. -/
def startT : Mma.Start → Nat
  | .set => scanBase
  | .alloc => scanBase + 1
  | _ => scanBase + 2

/-- **The time of an MMA-warp state** with ghost counts `n`: the pipeline by place and round,
the scheduler's passes by the collectives so far, the end after them. -/
def time (p : Params) (d : Mma.D) (n : Cls → Nat) : Nat :=
  if d.site.pipe then pipeT p d.site.ord (round d.site.ord d.v)
  else match endOff d.site with
    | some (l, o) => endT p l o
    | none =>
      if d.site = .bar1 then scanBase + 3
      else passTime (if d.site.late then endBase p else scanBase) (scans d n) (coll d.site)

theorem shAt_lin (q r : Nat) : Mma.shAt q r = Mma.shAt q 0 + 6 * r := by
  simp only [Mma.shAt, Mma.pq]
  norm_num
  omega

theorem shAt_table : ∀ q < 100, 20 ≤ q → if 38 ≤ q ∧ q < 60 then
    9 ≤ Mma.shAt q 0 ∧ Mma.shAt q 0 < 15 else 3 ≤ Mma.shAt q 0 ∧ (q < 86 → Mma.shAt q 0 < 9) := by
  decide

/-- **The round of a pipeline state** is its rounds done. -/
theorem round_eq {q r : Nat} {v : Mma.V} (hq : 20 ≤ q) (hq' : q < 86) (hp : v.ps = Mma.shAt q r) :
    round q v = r := by
  have h := shAt_table q (by omega) hq
  rw [shAt_lin] at hp
  unfold round
  split_ifs at h ⊢ <;> omega

/-- **The ring index of a K/V poll**: its poll is after the start of slot `i / 2`. -/
theorem kv_time (p : Params) {q r : Nat} {v : Mma.V} (hq : q = 2 ∨ q = 20 ∨ q = 29 ∨ q = 64)
    (hp : v.ps = Mma.shAt q r) (hr : q < 20 → r = 0) :
    clk p (Mma.ringAcq q r / 2) 0 ≤ pipeT p q (round q v) := by
  unfold pipeT
  split_ifs with h
  · have := hr h
    subst this
    obtain rfl : q = 2 := by omega
    simp [Mma.ringAcq, Mma.pq, clk]
  · rw [round_eq (by omega) (by omega) hp]
    have hi : Mma.ringAcq q r / 2 ≤ r + 1 := by
      rcases hq with rfl | rfl | rfl | rfl <;> simp [Mma.ringAcq, Mma.pq] <;> omega
    have := Nat.mul_le_mul_left span hi
    unfold clk; omega

theorem time_ge {p : Params} {d : Mma.D} {n : Cls → Nat} : 2 ≤ time p d n := by
  unfold time
  split
  · have := le_clk p (if d.site.ord < 20 then 0 else round d.site.ord d.v + 1) (2 * d.site.ord)
    simp only [pipeT, scanBase] at this ⊢
    omega
  split
  · rename_i l o _
    have := endT_ge p l o
    simp only [scanBase] at this ⊢
    omega
  split
  · simp only [scanBase]; omega
  · have := scan_pass_ge p d.site.late (scans d n) (coll d.site)
    simp only [scanBase] at this ⊢
    omega

end Mm

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
