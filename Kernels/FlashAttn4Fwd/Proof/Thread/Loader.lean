-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderWork
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Next

@[expose] public section

/-! # The loader as abstract states

Warp 14 of both CTAs (all 32 lanes) walks the static schedule of its cluster (`Work`). For
item `i` (`n` KV tiles) it loads, in order, the last K tile into the KV ring (`k0`), the two
query halves of the two softmax stages (`q0`, `q1`: Q ring, one slot per stage), the last V tile
(`v0`) and, for the trips `t < n - 1`, the K and V tiles `n - 2 - t` (`k`, `v`). Every use
first waits for its slot's empty barrier; on the leader CTA of the pair one elected lane then
arrives on the slot's full barrier expecting the transaction bytes of both CTAs' copies
(`elA`, `arrive`); on both CTAs one elected lane issues the `cta_group::2` copies (`elC`,
`copy`), two per use except one for a V tile. After its last item the loader waits for each
KV slot and the second Q slot to be empty (`drain`, `drainQ`) and the leader CTA's elected
lane arrives once more on the second Q slot's full barrier (`elTail`, `arriveTail`).

A state is the next event with the item `i`, the trip `t` and the three ring registers the
code carries: the KV slot `s` of the next K use (`%r3578`), its empty-barrier parity `ph`
(`%r3579`) and the Q empty parity `qp` (`%r3580`). The other registers are functions of these
(`table`); the registers the role inherits are the prologue's (`Prologue.valueOf`).

The copies' mbarrier operand is `and.b32 x, a, -16777217` of a `.shared::cta` address (the six
instructions `Assumptions.peerBitSites`); under the peer-bit assumption it is the even CTA's
`.shared::cluster` pointer (`peerV`), each of the six a segment step (`LoaderBase.run_peer`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000

/-- The six uses of an item's loop body: the last K and V tiles, the two Q halves, and a
trip's K and V tiles. -/
inductive UseK where
  | k0 | q0 | q1 | v0 | k | v
  deriving DecidableEq

/-- The number of copies of a use: one for a V tile, two otherwise. -/
def UseK.copies : UseK → Nat
  | .v0 | .v => 1
  | _ => 2

/-- The loader's next event. -/
inductive Site where
  | setMaxReg
  /-- The broadcast of the CTA's rank at an item's start (`shfl_4`). -/
  | head
  | wait (u : UseK)
  | elA (u : UseK)
  | arrive (u : UseK)
  | elC (u : UseK) (j : Fin 2)
  | copy (u : UseK) (j : Fin 2)
  | drain (k : Fin 6)
  | drainQ
  | elTail
  | arriveTail
  | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_1
  | .head => Flow.shfl_4
  | .wait .k0 => Flow.mbarWait_0 | .wait .q0 => Flow.mbarWait_1 | .wait .q1 => Flow.mbarWait_2
  | .wait .v0 => Flow.mbarWait_3 | .wait .k => Flow.mbarWait_4 | .wait .v => Flow.mbarWait_5
  | .elA .k0 => Flow.elect_15 | .elA .q0 => Flow.elect_18 | .elA .q1 => Flow.elect_21
  | .elA .v0 => Flow.elect_24 | .elA .k => Flow.elect_26 | .elA .v => Flow.elect_29
  | .arrive .k0 => Flow.mbarArrive_0 | .arrive .q0 => Flow.mbarArrive_1
  | .arrive .q1 => Flow.mbarArrive_2 | .arrive .v0 => Flow.mbarArrive_3
  | .arrive .k => Flow.mbarArrive_4 | .arrive .v => Flow.mbarArrive_5
  | .elC .k0 0 => Flow.elect_16 | .elC .k0 1 => Flow.elect_17
  | .elC .q0 0 => Flow.elect_19 | .elC .q0 1 => Flow.elect_20
  | .elC .q1 0 => Flow.elect_22 | .elC .q1 1 => Flow.elect_23
  | .elC .v0 _ => Flow.elect_25
  | .elC .k 0 => Flow.elect_27 | .elC .k 1 => Flow.elect_28
  | .elC .v _ => Flow.elect_30
  | .copy .k0 0 => Flow.tensorCopy_0 | .copy .k0 1 => Flow.tensorCopy_1
  | .copy .q0 0 => Flow.tensorCopy_2 | .copy .q0 1 => Flow.tensorCopy_3
  | .copy .q1 0 => Flow.tensorCopy_4 | .copy .q1 1 => Flow.tensorCopy_5
  | .copy .v0 _ => Flow.tensorCopy_6
  | .copy .k 0 => Flow.tensorCopy_7 | .copy .k 1 => Flow.tensorCopy_8
  | .copy .v _ => Flow.tensorCopy_9
  | .drain 0 => Flow.mbarWait_6 | .drain 1 => Flow.mbarWait_7 | .drain 2 => Flow.mbarWait_8
  | .drain 3 => Flow.mbarWait_9 | .drain 4 => Flow.mbarWait_10 | .drain 5 => Flow.mbarWait_11
  | .drainQ => Flow.mbarWait_12
  | .elTail => Flow.elect_31
  | .arriveTail => Flow.mbarArrive_6
  | .exit => Flow.exit_0

/-- A loader state: the next event, the item, the trip and the ring registers. -/
structure D where
  site : Site
  i : Nat
  t : Nat
  s : Nat
  ph : Nat
  qp : Nat

/-- The KV slot after slot `s` and the empty parity after `(s, p)`, as the code's `add 1`,
`setp.eq 6`, `selp` and `xor` compute them. -/
def snext (s : Nat) : Nat := if s + 1 = 6 then 0 else s + 1
def pnext (s p : Nat) : Nat := if s + 1 = 6 then 1 - p else p

/-- The KV slot and parity `k` uses after `(s, p)`. -/
def sAfter : Nat → Nat → Nat
  | 0, s => s
  | k + 1, s => snext (sAfter k s)
def pAfter : Nat → Nat → Nat → Nat
  | 0, _, p => p
  | k + 1, s, p => pnext (sAfter k s) (pAfter k s p)

/-- A 64-bit zero moved from a literal (the copies' cache-policy operands). -/
def zero64 : Value := .bits 64 (truncBits 64 (BitVec.ofInt 64 0))

/-- The copies' mbarrier operand computed from the address `sb + k` by
`and.b32 …, -16777217` under the peer-bit assumption (`Assumptions.peerBit`): the
`.shared::cluster` address of the same byte in the even CTA of the pair. -/
def peerV (L : Launch) (g k : Nat) : Value :=
  .ptr 32 false (.shared (ctaOf L g) (2 * (ctaOf L g / 2))) (BitVec.ofNat 64 (L.sharedBase + k))

/-- The CTA's `.shared::cluster` window address of `sb + k` (`cvta.to.shared::cluster`). -/
def win (L : Launch) (g k : Nat) : Value :=
  .ptr 32 false (.shared (ctaOf L g) (ctaOf L g)) (BitVec.ofNat 64 (L.sharedBase + k))

/-- The query row of the CTA's half of item `i` as the code computes it: the rank shifted by
7, plus the query block shifted by 9. -/
def qRowW (L : Launch) (g i : Nat) : BitVec 64 :=
  addW (shlW (BitVec.ofNat 64 (rank L g)) (BitVec.ofInt 64 7))
    (shlW (mblkW L g i) (BitVec.ofInt 64 9))

/-- The K/V row of the CTA's half of trip `t`. -/
def kRow (L : Launch) (g : Nat) (t : Nat) : Nat := 128 * (n L - 2 - t) + 64 * rank L g

/-- The registers of the loader at state `d`. Besides the registers live at the sites, the
table values the registers live at the checkpoints of the step proofs: the ceiling's
predicate and quotient, the schedule's branch predicates, the ring's wrap predicates and
incremented slots, the pointer conversions and the addresses before a mask. -/
def table (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let s1 := snext d.s
  [(344, .bits 32 (nbS1W L)), (345, .bits 32 (nbS2W L)), (348, .bits 32 (hS1W L)),
   (349, .bits 32 (hS2W L)), (350, b32 (n L)), (351, b32 (n L - 1)),
   (352, b32 (128 * (n L - 1))), (353, peerV L g 0), (354, sb L 8), (355, peerV L g 8),
   (356, win L g 0), (357, win L g 68608), (358, win L g 84992), (359, win L g 101376),
   (360, win L g 117760), (361, .bits 32 (GW L)), (362, b32 ((n L + 2 ^ 32 - 2) % 2 ^ 32)),
   (363, b32 (64 * rank L g)), (364, .bits 32 (qRowW L g d.i)),
   (365, sb L (8 * d.s)), (739, sb L (80 + 8 * d.s)),
   (366, b32 (128 * (n L - 1) + 64 * rank L g)), (367, peerV L g (32 + 8 * d.s)),
   (368, win L g (16384 * d.s)), (750, b32 (16384 * d.s)), (751, sb L (32 + 8 * d.s)),
   (369, b32 s1), (772, b32 (pnext d.s d.ph)),
   (370, .bits 32 (addW (qRowW L g d.i) (BitVec.ofInt 64 256))),
   (371, sb L (8 * s1)), (771, sb L (80 + 8 * s1)),
   (372, sb L (8 * d.s)), (783, sb L (80 + 8 * d.s)), (787, b32 (16384 * d.s)),
   (373, b32 (128 * (n L - 2 - d.t))), (374, b32 (kRow L g d.t)),
   (375, peerV L g (32 + 8 * d.s)), (376, win L g (16384 * d.s)), (789, sb L (32 + 8 * d.s)),
   (377, b32 s1), (795, b32 (pnext d.s d.ph)), (378, sb L (8 * s1)),
   (794, sb L (80 + 8 * s1)),
   (777, b32 (16384 * s1)), (778, sb L (32 + 8 * s1)),
   (779, peerV L g (32 + 8 * s1)), (780, win L g (16384 * s1)),
   (802, b32 (16384 * s1)), (803, sb L (32 + 8 * s1)),
   (804, peerV L g (32 + 8 * s1)), (805, win L g (16384 * s1)),
   (3908, .bits 32 (workW L g d.i)), (3909, .bits 32 (batchW L g d.i)),
   (3910, .bits 32 (headW L g d.i)), (3911, .bits 32 (mblkW L g d.i)),
   (3912, b32 d.t), (3913, b32 d.s), (3914, b32 d.ph), (3915, b32 d.qp),
   (830, sb L 24),
   (819, sb L (80 + 8 * d.s)), (820, sb L (80 + 8 * sAfter 1 d.s)),
   (821, b32 (pAfter 1 d.s d.ph)), (822, sb L (80 + 8 * sAfter 2 d.s)),
   (823, b32 (pAfter 2 d.s d.ph)), (824, sb L (80 + 8 * sAfter 3 d.s)),
   (825, b32 (pAfter 3 d.s d.ph)), (826, sb L (80 + 8 * sAfter 4 d.s)),
   (827, b32 (pAfter 4 d.s d.ph)), (828, sb L (80 + 8 * sAfter 5 d.s)),
   (829, b32 (pAfter 5 d.s d.ph)),
   (834, b32 (sAfter 1 d.s)), (839, b32 (sAfter 2 d.s)), (844, b32 (sAfter 3 d.s)),
   (849, b32 (sAfter 4 d.s)),
   (52, .pred (decide (rank L g ≠ 0))), (92, .pred (decide (rank L g ≠ 0))),
   (744, b32 (rank L g)),
   (749, b32 32768), (775, b32 32768), (786, b32 32768), (800, b32 32768),
   (758, b32 65536), (766, b32 65536), (859, b32 65536),
   (753, b32 0), (755, b32 64), (760, b32 0), (762, b32 64), (768, b32 0), (770, b32 64),
   (791, b32 0), (793, b32 64),
   (4074, zero64), (4076, zero64), (4079, zero64), (4081, zero64), (4084, zero64),
   (4086, zero64), (4089, zero64), (4092, zero64), (4094, zero64), (4097, zero64),
   (4073, .ptr 64 true (.param (param "5")) 0), (4075, .ptr 64 true (.param (param "5")) 0),
   (4078, .ptr 64 true (.param (param "4")) 0), (4080, .ptr 64 true (.param (param "4")) 0),
   (4083, .ptr 64 true (.param (param "4")) 0), (4085, .ptr 64 true (.param (param "4")) 0),
   (4088, .ptr 64 true (.param (param "6")) 0), (4091, .ptr 64 true (.param (param "5")) 0),
   (4093, .ptr 64 true (.param (param "5")) 0), (4096, .ptr 64 true (.param (param "6")) 0),
   -- checkpoints: the start
   (50, .pred false), (735, b32 (skOf L / 128)),
   (346, .bits 32 (qbW L g d.i)), (347, .bits 32 (mulLoW (qbW L g d.i) (BitVec.ofNat 64 (nb L)))),
   (51, .pred (PTX.compare .ge .s 32 (rd (BitVec.ofNat 64 (cid L g))) (rd (totW L)))),
   (4069, .bits 64 (BitVec.ofNat 64 L.sharedBase)),
   (4070, .ptr 64 true (.shared (ctaOf L g) (ctaOf L g)) (BitVec.ofNat 64 L.sharedBase)),
   (4071, .ptr 64 false (.shared (ctaOf L g) (ctaOf L g)) (BitVec.ofNat 64 L.sharedBase)),
   -- checkpoints: the item and trip loops
   (91, .pred (PTX.compare .lt .s 32 (rd (workW L g d.i)) (rd (totW L)))),
   (76, .pred (decide (n L < 2))), (90, .pred (decide (d.t ≠ n L - 1))),
   -- checkpoints: the ring's wrap tests
   (65, .pred (decide (d.s + 1 = 6))), (763, b32 (d.s + 1)),
   (77, .pred (decide (s1 + 1 = 6))), (781, b32 (s1 + 1)),
   (84, .pred (decide (d.s + 1 = 6))), (796, b32 (d.s + 1)),
   (89, .pred (decide (s1 + 1 = 6))), (806, b32 (s1 + 1)),
   (93, .pred (decide (d.s + 1 = 6))), (833, b32 (d.s + 1)),
   (94, .pred (decide (sAfter 1 d.s + 1 = 6))), (838, b32 (sAfter 1 d.s + 1)),
   (95, .pred (decide (sAfter 2 d.s + 1 = 6))), (843, b32 (sAfter 2 d.s + 1)),
   (96, .pred (decide (sAfter 3 d.s + 1 = 6))), (848, b32 (sAfter 3 d.s + 1)),
   (97, .pred (decide (sAfter 4 d.s + 1 = 6))), (853, b32 (sAfter 4 d.s + 1))]

/-- The value of register `r` at state `d`: the role's table, else the prologue's. -/
def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((table L g d).lookup r).getD (Prologue.valueOf L g 14 (rankOf L g) r)

/-- The registers live at `pc`, with their values in state `d`. -/
def factsAt (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

/-- Whether a site belongs to an item (not the start, the drain or the exit). -/
def Site.inItem : Site → Bool
  | .setMaxReg | .drain _ | .drainQ | .elTail | .arriveTail | .exit => false
  | _ => true

/-- Whether a site belongs to a trip of the KV loop. -/
def Site.inTrip : Site → Bool
  | .wait .k | .wait .v | .elA .k | .elA .v | .arrive .k | .arrive .v
  | .elC .k _ | .elC .v _ | .copy .k _ | .copy .v _ => true
  | _ => false

/-- Whether a site is an arrival or its election: the leader CTA of the pair only. -/
def Site.leadOnly : Site → Bool
  | .elA _ | .arrive _ | .elTail | .arriveTail => true
  | _ => false

/-- Bounds of the loader's states. -/
structure Inv (L : Launch) (g : Nat) (d : D) : Prop where
  s : d.s < 6
  ph : d.ph < 2
  qp : d.qp < 2
  item : d.site.inItem = true → d.i < T L g
  trip : d.site.inTrip = true → d.t + 2 ≤ n L
  lead : d.site.leadOnly = true → rank L g = 0
  one : ∀ u j, (d.site = .elC u j ∨ d.site = .copy u j) → j.val < u.copies

/-- After the last copy of a use: the next use, the next trip or the end of the item. The
ring registers move as the code moves them: the Q parity flips after the second Q half, the
KV slot moves by two after the V tile of the item's start and after each trip's V tile. -/
def afterUse (L : Launch) (g : Nat) (d : D) (u : UseK) : D :=
  match u with
  | .k0 => { d with site := .wait .q0 }
  | .q0 => { d with site := .wait .q1 }
  | .q1 => { d with site := .wait .v0, qp := 1 - d.qp }
  | .v0 =>
    let d' := { d with s := sAfter 2 d.s, ph := pAfter 2 d.s d.ph }
    if 2 ≤ n L then { d' with site := .wait .k, t := 0 } else itemEndOf L g d'
  | .k => { d with site := .wait .v }
  | .v =>
    let d' := { d with s := sAfter 2 d.s, ph := pAfter 2 d.s d.ph, t := d.t + 1 }
    if d.t + 1 + 1 < n L then { d' with site := .wait .k } else itemEndOf L g d'
where
  /-- The end of an item: the next item, or the drain. -/
  itemEndOf (L : Launch) (g : Nat) (d : D) : D :=
    if d.i + 1 < T L g then { d with site := .head, i := d.i + 1, t := 0 }
    else { d with site := .drain 0 }

/-- After copy `j` of use `u` (or its skipped election): the next copy, or the next use. -/
def afterCopy (L : Launch) (g : Nat) (d : D) (u : UseK) (j : Fin 2) : D :=
  if j.val + 1 < u.copies then { d with site := .elC u 1 } else afterUse L g d u

/-- The abstract successor after event `e`. Elections compare the leader with the thread's
lane; the item's rank broadcast must return the CTA's rank (the protocol layer shows it
does: every lane of the warp holds it); a site whose event is counted moves on only with an
event of its kind. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .setMaxReg =>
    some (some (if 0 < T L g then ⟨.head, 0, 0, 0, 1, 1⟩ else ⟨.drain 0, 0, 0, 0, 1, 1⟩))
  | .head =>
    match e.kind with
    | .shfl _ _ _ _ (.bits _ v) _ =>
      if v = BitVec.ofNat 64 (rank L g) then some (some { d with site := .wait .k0 })
      else some none
    | .shfl .. => some none
    | _ => none
  | .wait u =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      some (some (if ok then (if rank L g = 0 then { d with site := .elA u }
        else { d with site := .elC u 0 }) else d))
    | _ => none
  | .elA u =>
    match e.kind with
    | .elect _ _ ld =>
      some (some { d with site := if laneOf L g = ld then .arrive u else .elC u 0 })
    | _ => none
  | .arrive u =>
    match e.kind with
    | .arrive _ _ _ _ _ => some (some { d with site := .elC u 0 })
    | _ => none
  | .elC u j =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (if laneOf L g = ld then { d with site := .copy u j } else afterCopy L g d u j))
    | _ => none
  | .copy u j =>
    match e.kind with
    | .tensorIssue _ _ => some (some (afterCopy L g d u j))
    | _ => none
  | .drain k =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      some (some (if ok then (if h : k.val + 1 < 6 then { d with site := .drain ⟨k.val + 1, h⟩ }
        else { d with site := .drainQ }) else d))
    | _ => none
  | .drainQ =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      some (some (if ok then (if rank L g = 0 then { d with site := .elTail }
        else { d with site := .exit }) else d))
    | _ => none
  | .elTail =>
    match e.kind with
    | .elect _ _ ld =>
      some (some { d with site := if laneOf L g = ld then .arriveTail else .exit })
    | _ => none
  | .arriveTail =>
    match e.kind with
    | .arrive _ _ _ _ _ => some (some { d with site := .exit })
    | _ => none
  | .exit => none

/-! The equation lemmas of the definitions step files unfold, generated here once. -/

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
