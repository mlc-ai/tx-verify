-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Cnt
public import Kernels.TmlFa4Fwd.Proof.Mma.Ledger
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Lemmas.Flow.Counter32
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The places and the closed forms of the counts

The definitions of the reference invariant's closed forms, apart from the invariant (`Ref.lean`): a
theorem about a place or a formula does not read the invariant. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- The barrier at shared offset `o` of the lane's CTA. -/
abbrev bl (L : Launch) (g o : Nat) : Loc := ⟨.shared, g / L.block, L.sharedBase + o⟩

/-- The ring indices `j < n` with `j mod 3 = s`. -/
def ringCount (n s : Nat) : Nat := (n + 2 - s) / 3

/-- The place of a site in the pipeline's program order. -/
def Site.ord : Site → Nat
  | .wt k => [1, 2, 9, 20, 21, 29, 35, 64, 65, 73].getD k.val 0
  | .sh k => [3, 4, 10, 22, 23, 24, 30, 36, 37, 66, 67, 68, 74, 75].getD k.val 0
  | .eq b => [5, 11, 31, 44].getD b.val 0
  | .qk b _ => [6, 12, 32, 45].getD b.val 0
  | .ce c => [7, 13, 15, 33, 42, 46, 48, 60, 62, 80, 82, 84].getD c.val 0
  | .cm c => [8, 14, 16, 34, 43, 47, 49, 61, 63, 81, 83, 85].getD c.val 0
  | .ep b => [25, 38, 69, 76].getD b.val 0
  | .pv b j => [26, 39, 70, 77].getD b.val 0 + if 5 < j.val then 2 else 0
  | .mw b _ => [27, 40, 71, 78].getD b.val 0
  | .word k | .down k | .up k _ | .total k => if k.late then 100 else 0
  | .vote l | .pre l | .tiles l | .relinq l | .bar2 l | .dealloc l | .exit l => if l then 100 else 0
  | _ => 0

/-- How often the site at place `x` has been passed at place `q` with `r` rounds done. -/
def pq (x q r : Nat) : Nat :=
  if 20 ≤ x ∧ x < 60 then r + (if 20 ≤ q ∧ q < 60 ∧ x < q then 1 else 0)
  else if x < q then 1 else 0

/-- The K/V ring's acquisitions and releases before place `q`. -/
def ringAcq (q r : Nat) : Nat := pq 2 q r + pq 20 q r + pq 29 q r + pq 64 q r
def ringRel (q r : Nat) : Nat := pq 16 q r + pq 43 q r + pq 49 q r + pq 81 q r

/-- The successful polls of the barrier at offset `o` before place `q`. -/
def acqAt (q r o : Nat) : Nat :=
  (if o = 0 then pq 1 q r else 0) + (if o = 8 then pq 9 q r else 0) +
    (if o = 96 then pq 21 q r + pq 65 q r else 0) + (if o = 104 then pq 35 q r + pq 73 q r else 0) +
    (if o = 112 then pq 27 q r + pq 71 q r else 0) +
    (if o = 120 then pq 40 q r + pq 78 q r else 0) +
    (if 32 ≤ o ∧ o < 56 ∧ o % 8 = 0 then ringCount (ringAcq q r) ((o - 32) / 8) else 0)

/-- The commits to the barrier at offset `o` before place `q`, on the lane that commits. -/
def commitAt (q r o : Nat) : Nat :=
  (if o = 80 then pq 8 q r + pq 34 q r else 0) + (if o = 88 then pq 14 q r + pq 47 q r else 0) +
    (if o = 16 then pq 61 q r else 0) + (if o = 24 then pq 63 q r else 0) +
    (if o = 144 then pq 83 q r else 0) + (if o = 152 then pq 85 q r else 0) +
    (if 56 ≤ o ∧ o < 80 ∧ o % 8 = 0 then ringCount (ringRel q r) ((o - 56) / 8) else 0)

/-- The elections before place `q`. -/
def electAll (q r : Nat) : Nat :=
  pq 5 q r + pq 11 q r + pq 31 q r + pq 44 q r + pq 7 q r + pq 13 q r + pq 15 q r + pq 33 q r +
    pq 42 q r + pq 46 q r + pq 48 q r + pq 60 q r + pq 62 q r + pq 80 q r + pq 82 q r +
    pq 84 q r + pq 25 q r + pq 38 q r + pq 69 q r + pq 76 q r

/-- The pipeline's broadcasts before place `q` (three before the loop, six per round, five in
the tail). -/
def shAt (q r : Nat) : Nat :=
  pq 3 q r + pq 4 q r + pq 10 q r + pq 22 q r + pq 23 q r + pq 24 q r + pq 30 q r + pq 36 q r +
    pq 37 q r + pq 66 q r + pq 67 q r + pq 68 q r + pq 74 q r + pq 75 q r

/-- A 32-bit word of a natural number. -/
abbrev iw (n : Nat) : BitVec 64 := i32 (n : Int)

/-- The loop registers with `r` rounds done. -/
def LoopRegs (v : V) (r : Nat) : Prop :=
  v.slot = iw ((2 * r + 1) % 3) ∧ v.kvp = iw ((2 * r + 1) / 3 % 2) ∧ v.pp = iw (r % 2) ∧
    v.accum = iw (if r = 0 then 0 else 1)

/-- The tile's number of K/V blocks as the loop compares it (a signed word). -/
abbrev Bs (p : Params) (L : Launch) (g : Nat) (v : V) : Int := toSigned 32 (r32 (blocks p L g v))

/-- The places of the commits: only the lane that wins the elections is there. -/
def cmQ : List Nat := [8, 14, 16, 34, 43, 47, 49, 61, 63, 81, 83, 85]

/-- The barrier offset of commit `c` with `r` rounds done. -/
def cmO (r : Nat) (c : Fin 12) : Nat :=
  [80, 88, 56, 80, 56 + 8 * ((2 * r + 1) % 3), 88, 56 + 8 * ((2 * r + 2) % 3), 16, 24,
    56 + 8 * ((2 * r + 1) % 3), 144, 152].getD c.val 0

/-- The pipeline's sites. -/
def Site.pipe : Site → Bool
  | .wt _ | .sh _ | .eq _ | .qk _ _ | .ep _ | .pv _ _ | .mw _ _ | .ce _ | .cm _ => true
  | _ => false

/-- The second pass's sites and the end after it. -/
def Site.late : Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .relinq l | .bar2 l | .dealloc l | .exit l => l
  | _ => false

/-- The sites before the scan. -/
def Site.early : Site → Bool
  | .bar1 | .ldAlloc | .bcast => true
  | _ => false

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
