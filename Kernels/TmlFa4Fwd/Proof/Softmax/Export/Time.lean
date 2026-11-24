-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
public import Kernels.TmlFa4Fwd.Proof.Common.Frame

@[expose] public section

/-! # The times of the softmax warps' states -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The softmax warps -/

namespace Sm

/-- The stage of a softmax lane: warps 0 to 3 run stage 0, warps 4 to 7 stage 1. -/
def stage (L : Launch) (g : Nat) : Nat := if Prologue.warpIndex L g < 4 then 0 else 1

/-- The scheduler's sites as the output warp's sites. -/
def toE : Softmax.Site → Epilogue.Site
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | _ => .q0

/-- The second pass's sites and the end after it. -/
def late : Softmax.Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .wend l | .barEnd l | .exit l => l
  | _ => false

/-- The request's reads and the first credit poll, in the prime region. -/
def pre : Softmax.Site → Option Nat
  | .q0 => some 0
  | .q1 => some 1
  | .uk => some 2
  | .wq => some 3
  | _ => none

/-- A round site of stage `st`: its band, whether it is past the round's S-full poll (its slot is
then one less than the S-full polls so far), and its offset. The score part: the S-full poll, the
loads, the Bias poll, loads, fence, barrier and arrival, the statistics store, the correction
barrier's arrival; the P part: the stores, their waits, the P-full arrival, the warp barrier, the
election, the second-P arrival, stage 0's closing credit poll and final stores. Stage 1's closing
poll opens its next slot's score part, and its final stores follow it there. -/
def place (st : Nat) : Softmax.Site → Option (Nat × Bool × Nat)
  | .ws _ => some (bandS st, false, 2)
  | .sld _ c => some (bandS st, true, 4 + 3 * c.val)
  | .sldw c => some (bandS st, true, 5 + 3 * c.val)
  | .wb _ => some (bandS st, true, 16)
  | .bld _ c => some (bandS st, true, 18 + c.val)
  | .fence _ => some (bandS st, true, 34)
  | .bsync _ => some (bandS st, true, 36)
  | .barr _ => some (bandS st, true, 38)
  | .stat _ => some (bandS st, true, 40)
  | .narr _ => some (bandS st, true, 42)
  | .pst _ q => some (bandP st, true, if q.val = 3 then 13 else 2 * q.val)
  | .pwst _ k => some (bandP st, true, 8 + 8 * k.val)
  | .parr _ => some (bandP st, true, 12)
  | .pws _ => some (bandP st, true, 18)
  | .pel _ => some (bandP st, true, 20)
  | .parr2 _ => some (bandP st, true, 22)
  | .pwend _ => if st = 0 then some (bandP 0, true, 24) else some (bandS 1, false, 0)
  | .fin k => if st = 0 then some (bandP 0, true, 26 + 2 * k.val)
      else some (bandS 1, false, 100 + 2 * k.val)
  | .finarr => if st = 0 then some (bandP 0, true, 30) else some (bandS 1, false, 104)
  | _ => none

/-- The sub-step of a P store: the store after its delayed wait. -/
def subOff (d : Softmax.D) : Nat :=
  match d.site with | .pst .first 0 | .pst .bias 0 => min d.k.val 1 | _ => 0

/-- The end: the poll for the last credit, barrier 2, the return. -/
def endOff : Softmax.Site → Option (Bool × Nat)
  | .wend l => some (l, 2)
  | .barEnd l => some (l, 4)
  | .exit l => some (l, 6)
  | _ => none

/-- **The time of a softmax state** of lane `g` with ghost counts `n`: a round site in its band of
the slot of its round (the S-full polls so far, `Softmax.Cnt.acquire 80`); the request's reads in
the prime region; the entry, the first barrier; the scheduler's passes by the shuffles so far (and
the pass's ballot), the end after them. -/
def time (p : Params) (L : Launch) (g : Nat) (d : Softmax.D) (n : Cls → Nat) : Nat :=
  match place (stage L g) d.site with
  | some (b, past, o) =>
    clk p (slotOf p (n (.soft (.acquire 80)) - if past then 1 else 0)) (b + o + subOff d)
  | none =>
    match pre d.site with
    | some o => primeBase p + o
    | none =>
      match endOff d.site with
      | some (l, o) => endT p l o
      | none =>
        if d.site = .setmax then scanBase else if d.site = .bar1 then scanBase + 3
        else passTime (if late d.site then endBase p else scanBase)
          (n .shfl + Out.ballots (toE d.site)) (Out.coll (toE d.site))

end Sm

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
