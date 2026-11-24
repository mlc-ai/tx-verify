-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Flow.Sites
public import Kernels.FlashAttn4Fwd.Flow.Code
public import Kernels.FlashAttn4Fwd.Assumptions
public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Next
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.RegBits

@[expose] public section

/-! # The MMA warp (warp 12) as abstract states

On each CTA of a cluster, warp 12 allocates the 512 Tensor Memory columns of the CTA pair
(`tcgen05.alloc.cta_group::2`), publishes the address with `bar.sync 2` and reads it back. On the
leader CTA (rank 0) it then runs the cluster's work items `i` (item `c + i·G` while below the
item count): per item it waits for the two Q stages and the `2 n` K/V uses of the six-slot ring
(`n` KV trips), issues the S = Q Kᵀ MMAs (A and B from shared-memory descriptors) and the
O += P V MMAs (A = P from Tensor Memory), waits for softmax's P-ready barriers, and commits with
multicast to the S-full, KV-empty, Q-empty and O-full barriers of both CTAs. On the odd CTA the
item loop performs no event. Both CTAs then relinquish the allocation permit, synchronize at
`bar.sync 2`, hand off on the peer's `+320` barrier, wait on their own, and deallocate.

All 32 lanes run the role. Eight inline-assembly blocks elect one lane (`elect.sync
_|leader_thread`) and guard their MMAs with the election; the other lanes skip them as local
steps. The commit elections are the same: the elected lane commits, the others skip.

A state is the next event with the item `i`, the trip `t` (loop trips done, `n - 1` after the
loop) and the values read from memory (`base`) or set by the prologue and only carried here
(`pro`). Ring slots, parities, the accumulate flag, the Q descriptor toggle and every address
are functions of `(site, i, t)` in the value table. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### The shape as the code reads it

`seqlen_k` (`skOf`), the item count (`totOf`) and the thread's cluster (`clusterOf`) are those
of `Thread/Common.lean`. -/

/-- The KV trips of an item, `n = ⌈sk / 128⌉`. -/
def trips (L : Launch) : Nat := (skOf L + 127) / 128

/-- The number of clusters (`%nclusterid.x`). -/
def clusters (L : Launch) : Nat := L.grid / L.clusterSize.val

/-- The thread's CTA rank in its pair (`%ctaid.x & 1`). -/
def rank (L : Launch) (g : Nat) : Nat := g / L.block % 2

/-- Item `i` of the thread's cluster. -/
def work (L : Launch) (g i : Nat) : Nat := clusterOf L g + i * clusters L

/-- The ring use number of the first use of item `i` (`2 n` uses per item). -/
def kvBase (L : Launch) (i : Nat) : Nat := 2 * trips L * i

/-- The ring use number of use `u` of item `i`. -/
def kvUse (L : Launch) (i u : Nat) : Nat := kvBase L i + u

/-- The slot and the full-barrier parity of a ring use. -/
def kvSlot (L : Launch) (i u : Nat) : Nat := kvUse L i u % 6
def kvPar (L : Launch) (i u : Nat) : Nat := kvUse L i u / 6 % 2

/-- The P-ready handshakes of the items before item `i` (one per trip). -/
def pBase (L : Launch) (i : Nat) : Nat := trips L * i

/-- The parity of the P-ready and S/P handshake barriers at trip `t` of item `i`. -/
def pPar (L : Launch) (i t : Nat) : Nat := (pBase L i + t) % 2

/-- The CTA the `+320` hand-off targets: the other CTA of the pair. -/
def peer (L : Launch) (g : Nat) : Nat := clusterOf L g * 2 + (1 - rank L g)

/-! ### Descriptors -/

/-- The fixed high word of every shared-memory descriptor (`0x40004040`). -/
abbrev descHi : Nat := 1073758272

/-- A 64-bit shared-memory descriptor with low word `lo`. -/
def desc (lo : Nat) : Value := b64 (lo + descHi * 2 ^ 32)

/-- The low descriptor word of the Q tile of stage 1 (`low = false`) or stage 0. -/
def qLo (L : Launch) (low : Bool) : Nat :=
  (L.sharedBase + 101376) / 16 + 65536 - (if low then 2048 else 0)

/-- The low descriptor words of a KV slot read as K (K-major) and as V (MN-major). -/
def kLo (L : Launch) (s : Nat) : Nat := (L.sharedBase + 134144 + 16384 * s) / 16 + 65536
def vLo (L : Launch) (s : Nat) : Nat := (L.sharedBase + 134144 + 16384 * s) / 16

/-- The instruction descriptors of the QK and PV MMAs. -/
abbrev qkIdesc : Nat := 270532624
abbrev pvIdesc : Nat := 270598160

/-! ### Sites -/

inductive Site where
  /-- `setmaxnreg`, the pair allocation (request, then lane 0's address store), `bar.sync 2`,
  the read-back of the address and the broadcast of the Q descriptor. -/
  | setMaxReg | alloc | allocWrite | bar0 | ldBase | shflQ
  /-- Q-full polls of stages 0 and 1. -/
  | qWait (k : Fin 2)
  /-- KV-full polls: the item's first K, a loop V, a loop K, the last V. -/
  | kvWait (k : Fin 4)
  /-- P-ready polls (`+144`/`+152`) before a PV block: loop stage 0, 1, last stage 0, 1. -/
  | pWait (k : Fin 4)
  /-- The second P-ready poll (`+160`/`+168`) inside PV block `k`, of the elected lane or not. -/
  | p2Wait (k : Fin 4) (lead : Bool)
  /-- The constant broadcasts `shfl_6` … `shfl_19`. -/
  | shfl (k : Fin 14)
  /-- The election of asm block `b` and its eight MMAs. Blocks: S0 and S1 of the item's first
  K, PV0, S0, PV1, S1 of a trip, PV0 and PV1 of the last V. -/
  | elM (b : Fin 8)
  | mma (b : Fin 8) (j : Fin 8)
  /-- The twelve commit elections and commits. -/
  | elC (c : Fin 12)
  | commit (c : Fin 12)
  /-- The end: permit relinquish, `bar.sync 2`, the hand-off arrival on the peer, the wait on
  the own barrier, the deallocation, the exit. -/
  | relinquish | bar1 | arrivePeer | waitDealloc | dealloc | exit
  deriving DecidableEq

def qWaitPc : Fin 2 → Nat
  | 0 => Flow.mbarWait_13 | 1 => Flow.mbarWait_15

def kvWaitPc : Fin 4 → Nat
  | 0 => Flow.mbarWait_14 | 1 => Flow.mbarWait_16 | 2 => Flow.mbarWait_19
  | 3 => Flow.mbarWait_22

def pWaitPc : Fin 4 → Nat
  | 0 => Flow.mbarWait_17 | 1 => Flow.mbarWait_20 | 2 => Flow.mbarWait_23
  | 3 => Flow.mbarWait_25

def p2WaitPc : Fin 4 → Nat
  | 0 => Flow.mbarWait_18 | 1 => Flow.mbarWait_21 | 2 => Flow.mbarWait_24
  | 3 => Flow.mbarWait_26

def elMPc : Fin 8 → Nat
  | 0 => Flow.elect_32 | 1 => Flow.elect_34 | 2 => Flow.elect_37 | 3 => Flow.elect_38
  | 4 => Flow.elect_40 | 5 => Flow.elect_42 | 6 => Flow.elect_47 | 7 => Flow.elect_49

def elCPc : Fin 12 → Nat
  | 0 => Flow.elect_33 | 1 => Flow.elect_35 | 2 => Flow.elect_36 | 3 => Flow.elect_39
  | 4 => Flow.elect_41 | 5 => Flow.elect_43 | 6 => Flow.elect_44 | 7 => Flow.elect_45
  | 8 => Flow.elect_46 | 9 => Flow.elect_48 | 10 => Flow.elect_50 | 11 => Flow.elect_51

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_2
  | .alloc => Flow.tmemAlloc_0 | .allocWrite => Flow.tmemAlloc_0
  | .bar0 => Flow.bar_0 | .ldBase => Flow.load_0 | .shflQ => Flow.shfl_5
  | .qWait k => qWaitPc k | .kvWait k => kvWaitPc k | .pWait k => pWaitPc k
  | .p2Wait k _ => p2WaitPc k
  | .shfl k => Flow.shfl.getD (6 + k.val) 0
  | .elM b => elMPc b
  | .mma b j => Flow.mma.getD (8 * b.val + j.val) 0
  | .elC c => elCPc c
  | .commit c => Flow.tcCommit.getD c.val 0
  | .relinquish => Flow.tmemRelinquish_0 | .bar1 => Flow.bar_1
  | .arrivePeer => Flow.mbarArrive_7 | .waitDealloc => Flow.mbarWait_27
  | .dealloc => Flow.tmemDealloc_0 | .exit => Flow.exit_0

/-- The address store of the allocation is the second event of its instruction. -/
def Site.sub : Site → Nat
  | .allocWrite => 1
  | _ => 0

/-- The PV blocks. -/
def isPv (b : Fin 8) : Bool := b = 2 || b = 4 || b = 6 || b = 7

/-- The index of a PV block among the four, and the PV block of an index. -/
def pvIdx : Fin 8 → Fin 4
  | 4 => 1 | 6 => 2 | 7 => 3 | _ => 0

def pvGrp : Fin 4 → Fin 8
  | 0 => 2 | 1 => 4 | 2 => 6 | 3 => 7

/-- Whether the Q descriptors hold stage 0 (between an S0 block and the next S1 block). -/
def qLow : Site → Bool
  | .mma b _ => b = 0 || b = 3 || b = 4
  | .elM b => b = 1 || b = 4 || b = 5
  | .elC c | .commit c => c = 0 || c = 3 || c = 4
  | .qWait 1 | .shfl 2 | .shfl 7 | .shfl 8 | .pWait 1 | .p2Wait 1 _ => true
  | _ => false

/-! ### Abstract states and values -/

structure D where
  site : Site
  /-- The item. -/
  i : Nat
  /-- The trip: KV trips done in the loop (`n - 1` after it). -/
  t : Nat
  /-- The Tensor Memory address read back after the allocation. -/
  base : Value
  /-- The registers the prologue set that this role only carries. -/
  pro : Nat → Value

/-- The shared-memory pointer of the peer's `+320` barrier (`mapa`). -/
def peerPtr (L : Launch) (g : Nat) : Value :=
  .ptr 32 false (.shared (g / L.block) (peer L g)) (BitVec.ofNat 64 (L.sharedBase + 320))

/-- The lane's election in the asm block of a site: true at the MMAs (only the elected lane
reaches them) and as recorded at the inner P-ready polls. -/
def leadOf : Site → Bool
  | .mma _ _ => true
  | .p2Wait _ lead => lead
  | _ => false

/-- The MMA of a PV block a site is at or after: `j` at MMA `j`, 5 at the inner poll. -/
def jOf : Site → Nat
  | .mma _ j => j.val
  | .p2Wait _ _ => 5
  | _ => 0

/-- The registers of the eight asm blocks, at their literal ids. QK block at `B` (`B = 5355`,
`5372`, `5401`, `5428`): the election (`B`), the accumulator column (`B + 2`), the eight B
descriptors (`B + 8 + k`). PV block at `B` (`5390`, `5418`, `5446`, `5457`): the election
(`B`), the accumulate predicate (`B + 1`), the instruction descriptor, the accumulator and P
columns, the V descriptor's start, current low word, high word and the descriptor
(`B + 2` … `B + 8`). A block's registers are live only inside it, where the site gives the
lane's election (`leadOf`) and the current MMA (`jOf`). -/
def asmVals (L : Launch) (d : D) : List (Nat × Value) :=
  let s0 := kvSlot L d.i 0
  let sK := kvSlot L d.i (2 + 2 * d.t)
  let sV := kvSlot L d.i (1 + 2 * d.t)
  let ld := leadOf d.site
  let lo := vLo L sV + 128 * jOf d.site
  let qk (B col kl : Nat) : List (Nat × Value) :=
    [(B, .pred ld), (B + 2, b32 col), (B + 8, desc kl), (B + 9, desc (kl + 2)),
      (B + 10, desc (kl + 4)), (B + 11, desc (kl + 6)), (B + 12, desc (kl + 512)),
      (B + 13, desc (kl + 514)), (B + 14, desc (kl + 516)), (B + 15, desc (kl + 518))]
  let pv (B acc a : Nat) : List (Nat × Value) :=
    [(B, .pred ld), (B + 1, .pred (decide (d.t ≠ 0))), (B + 2, b32 pvIdesc), (B + 3, b32 acc),
      (B + 4, b32 a), (B + 5, b32 (vLo L sV)), (B + 6, b32 lo), (B + 7, b32 descHi),
      (B + 8, desc lo)]
  qk 5355 0 (kLo L s0) ++ qk 5372 128 (kLo L s0) ++ pv 5390 256 64 ++ qk 5401 0 (kLo L sK) ++
    pv 5418 384 192 ++ qk 5428 128 (kLo L sK) ++ pv 5446 256 64 ++ pv 5457 384 192

/-- The Q descriptors (`5343 + k`, the A operands of the QK MMAs), of stage 0 or 1. -/
def qVals (L : Launch) (d : D) : List (Nat × Value) :=
  let q := qLo L (qLow d.site)
  [(5343, desc q), (5344, desc (q + 2)), (5345, desc (q + 4)), (5346, desc (q + 6)),
    (5347, desc (q + 1024)), (5348, desc (q + 1026)), (5349, desc (q + 1028)),
    (5350, desc (q + 1030))]

/-- The MMA thread's register values (decoder register ids). -/
def values (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let sb := L.sharedBase
  let n := trips L
  let s0 := kvSlot L d.i 0
  let sV := kvSlot L d.i (1 + 2 * d.t)
  let sK := kvSlot L d.i (2 + 2 * d.t)
  [ -- prologue registers this role reads
    (308, .bits 16 (BitVec.ofNat 64 3)), (336, b32 12), (337, b32 sb), (338, b32 (rank L g)),
    (339, b32 (L.rankOfCta (g / L.block))), (340, b32 (sb + 128)), (665, b32 (skOf L)),
    (756, b32 (sb + 16)), (935, b32 (sb + 160)), (956, b32 (sb + 320)),
    (3250, b32 (sb + 192)), (3904, b32 (totOf L)), (3936, b32 (clusterOf L g)),
    -- allocation and Q descriptor
    (861, b32 512), (379, d.base), (865, b32 (qLo L false)),
    -- item constants
    (380, b32 (sb + 136)), (381, b32 (n - 1)), (382, b32 (sb + 200)), (383, b32 (sb + 24)),
    (384, b32 (clusters L)), (883, b32 (sb + 8)), (932, b32 (sb + 144)),
    (945, b32 (sb + 152)), (949, b32 (sb + 168)),
    -- loop state
    (3916, b32 (work L g d.i)), (3917, b32 d.t), (3918, b32 (pPar L d.i d.t)),
    (3919, b32 (if d.t = 0 then 0 else 1)), (3920, b32 sV), (3921, b32 (kvPar L d.i (1 + 2 * d.t))),
    (3922, b32 (d.i % 2)), (3923, b32 s0), (3924, b32 (kvPar L d.i 0)),
    -- ring addresses and parities
    (385, b32 (sb + 8 * s0)), (386, b32 (sb + 8 * sV)), (387, b32 sK), (388, b32 (sb + 8 * sK)),
    (389, b32 (sb + 8 * sV)), (873, b32 (sb + 8 * s0 + 32)), (891, b32 (sb + 8 * sV + 32)),
    (894, b32 (sb + 8 * sK + 32)), (895, b32 (kvPar L d.i (2 + 2 * d.t))),
    (931, b32 (sb + 8 * sV + 32)),
    -- descriptors and Tensor Memory columns (broadcast values and their sources)
    (881, b32 (kLo L s0)), (884, b32 (kLo L s0)), (903, b32 (vLo L sV)), (917, b32 (vLo L sV)),
    (914, b32 (kLo L sK)), (922, b32 (kLo L sK)), (941, b32 (vLo L sV)), (947, b32 (vLo L sV)),
    (874, b32 0), (885, b32 0), (896, b32 0), (897, b32 0), (923, b32 0),
    (886, b32 128), (924, b32 128), (892, b32 64), (904, b32 64), (933, b32 64), (942, b32 64),
    (893, b32 256), (905, b32 256), (934, b32 256), (943, b32 256),
    (916, b32 192), (919, b32 192), (946, b32 192), (950, b32 192),
    (918, b32 384), (920, b32 384), (948, b32 384), (951, b32 384),
    -- commit masks
    (323, .bits 16 (BitVec.ofNat 64 3)), (324, .bits 16 (BitVec.ofNat 64 3)),
    (325, .bits 16 (BitVec.ofNat 64 3)), (326, .bits 16 (BitVec.ofNat 64 3)),
    (327, .bits 16 (BitVec.ofNat 64 3)), (328, .bits 16 (BitVec.ofNat 64 3)),
    -- the end
    (957, b32 (1 - L.rankOfCta (g / L.block))), (958, peerPtr L g), (959, b32 1), (960, b32 512),
    -- the branch predicates: no item, odd CTA, no loop trip, loop again, next item
    (101, .pred (decide (totOf L ≤ clusterOf L g))), (105, .pred (decide (rank L g ≠ 0))),
    (869, b32 (skOf L / 128)), (104, .pred false),
    (889, b32 (kvSlot L d.i 0 + 1)), (113, .pred (decide (kvSlot L d.i 0 + 1 = 6))),
    (927, b32 (kvSlot L d.i (2 + 2 * d.t) + 1)),
    (123, .pred (decide (kvSlot L d.i (2 + 2 * d.t) + 1 = 6))),
    (906, b32 (kvSlot L d.i (1 + 2 * d.t) + 1)), (954, b32 (kvSlot L d.i (1 + 2 * d.t) + 1)),
    (135, .pred (decide (kvSlot L d.i (1 + 2 * d.t) + 1 = 6))),
    (112, .pred (decide (trips L - 1 < 1))), (124, .pred (decide (d.t ≠ trips L - 1))),
    (136, .pred (decide (work L g d.i < totOf L))),
    -- the QK instruction descriptor
    (5351, b32 qkIdesc)] ++ qVals L d ++ asmVals L d

def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values L g d).lookup r).getD (d.pro r)

def factsAt (L : Launch) (g pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

/-- The sites from the item's Q poll to its last commit. -/
def ItemSite : Site → Prop
  | .setMaxReg | .alloc | .allocWrite | .bar0 | .ldBase | .shflQ | .relinquish | .bar1
  | .arrivePeer | .waitDealloc | .dealloc | .exit => False
  | _ => True

/-- The part of an item a site is in: before the trip loop (1), in it (2), after it (3). -/
def region : Site → Nat
  | .qWait _ | .kvWait 0 | .shfl 0 | .shfl 1 | .shfl 2 | .elM 0 | .elM 1 | .mma 0 _ | .mma 1 _
  | .elC 0 | .elC 1 | .elC 2 | .commit 0 | .commit 1 | .commit 2 => 1
  | .kvWait 1 | .kvWait 2 | .pWait 0 | .pWait 1 | .p2Wait 0 _ | .p2Wait 1 _ | .shfl 3 | .shfl 4
  | .shfl 5 | .shfl 6 | .shfl 7 | .shfl 8 | .elM 2 | .elM 3 | .elM 4 | .elM 5 | .mma 2 _
  | .mma 3 _ | .mma 4 _ | .mma 5 _ | .elC 3 | .elC 4 | .elC 5 | .elC 6 | .commit 3
  | .commit 4 | .commit 5 | .commit 6 => 2
  | .kvWait 3 | .pWait 2 | .pWait 3 | .p2Wait 2 _ | .p2Wait 3 _ | .shfl 9 | .shfl 10
  | .shfl 11 | .shfl 12 | .shfl 13 | .elM 6 | .elM 7 | .mma 6 _ | .mma 7 _ | .elC 7 | .elC 8
  | .elC 9 | .elC 10 | .elC 11 | .commit 7 | .commit 8 | .commit 9 | .commit 10
  | .commit 11 => 3
  | _ => 0

/-- The trip of a state against its part of the item: 0 before the loop, a loop trip in it,
`n - 1` after it. -/
def TripOk (L : Launch) (d : D) : Prop :=
  match region d.site with
  | 1 => d.t = 0
  | 2 => d.t + 1 < trips L
  | 3 => d.t + 1 = trips L
  | _ => True

structure Inv (L : Launch) (g : Nat) (d : D) : Prop where
  t : d.t = 0 ∨ d.t < trips L
  i : ItemSite d.site → work L g d.i < totOf L ∧ rank L g = 0
  trip : TripOk L d

/-! ### Transitions -/

/-- The site after asm block `b` for the lane that issued its MMAs. -/
def afterGrp : Fin 8 → Site
  | 0 => .elC 0 | 1 => .elC 1 | 2 => .kvWait 2 | 3 => .elC 3 | 4 => .elC 4 | 5 => .elC 5
  | 6 => .elC 9 | 7 => .elC 10

/-- The site after the election of block `b` for a lane that was not elected: past the
block, or the poll inside a PV block. -/
def skipGrp (b : Fin 8) : Site := if isPv b then .p2Wait (pvIdx b) false else afterGrp b

/-- The site after MMA `j` of block `b`. -/
def mmaNext (b j : Fin 8) : Site :=
  if h : j.val + 1 < 8 then
    if isPv b ∧ j.val = 5 then .p2Wait (pvIdx b) true else .mma b ⟨j.val + 1, h⟩
  else afterGrp b

/-- The site after the constant broadcast `k`. -/
def shflNext : Fin 14 → Site
  | 0 => .shfl 1 | 1 => .elM 0 | 2 => .elM 1 | 3 => .shfl 4 | 4 => .shfl 5 | 5 => .elM 2
  | 6 => .elM 3 | 7 => .shfl 8 | 8 => .elM 4 | 9 => .shfl 10 | 10 => .shfl 11 | 11 => .elM 6
  | 12 => .shfl 13 | 13 => .elM 7

/-- The value lane 0 broadcasts at `shfl k` (the table's value of the source register). -/
def shflVal (L : Launch) (d : D) : Fin 14 → Value
  | 0 => b32 (kLo L (kvSlot L d.i 0)) | 1 => b32 0 | 2 => b32 128
  | 3 => b32 64 | 4 => b32 (vLo L (kvSlot L d.i (1 + 2 * d.t))) | 5 => b32 256
  | 6 => b32 (kLo L (kvSlot L d.i (2 + 2 * d.t))) | 7 => b32 192 | 8 => b32 384
  | 9 => b32 64 | 10 => b32 (vLo L (kvSlot L d.i (1 + 2 * d.t))) | 11 => b32 256
  | 12 => b32 192 | 13 => b32 384

/-- The state after commit election `c` (with or without the commit). -/
def afterCommit (L : Launch) (g : Nat) (d : D) (c : Fin 12) : D :=
  match c with
  | 0 => { d with site := .qWait 1 }
  | 1 => { d with site := .elC 2 }
  | 2 => if trips L - 1 < 1 then { d with site := .elC 7 } else { d with site := .kvWait 1 }
  | 3 => { d with site := .pWait 1 }
  | 4 => { d with site := .elM 5 }
  | 5 => { d with site := .elC 6 }
  | 6 =>
    if d.t + 1 < trips L - 1 then { d with site := .kvWait 1, t := d.t + 1 }
    else { d with site := .elC 7, t := d.t + 1 }
  | 7 => { d with site := .elC 8 }
  | 8 => { d with site := .kvWait 3 }
  | 9 => { d with site := .pWait 3 }
  | 10 => { d with site := .elC 11 }
  | 11 =>
    if work L g (d.i + 1) < totOf L then { d with site := .qWait 0, i := d.i + 1, t := 0 }
    else { d with site := .relinquish, i := d.i + 1, t := 0 }

/-- The site after a successful KV poll. -/
def kvNext : Fin 4 → Site
  | 0 => .shfl 0 | 1 => .pWait 0 | 2 => .shfl 6 | 3 => .pWait 2

/-- The site after a successful P-ready poll. -/
def pNext : Fin 4 → Site
  | 0 => .shfl 3 | 1 => .shfl 7 | 2 => .shfl 9 | 3 => .shfl 12

/-- The site after a successful second P-ready poll: the elected lane's last two MMAs, or past
the block. -/
def p2Next (k : Fin 4) (lead : Bool) : Site :=
  if lead then .mma (pvGrp k) 6 else afterGrp (pvGrp k)

/-- The state after the broadcast of the Q descriptor: the first item on the leader CTA, or
the end (no item, or the odd CTA, whose item loop performs no event). -/
def start (L : Launch) (g : Nat) (d : D) : D :=
  if rank L g = 0 ∧ work L g 0 < totOf L then { d with site := .qWait 0, i := 0, t := 0 }
  else { d with site := .relinquish, i := 0, t := 0 }

/-- The abstract successor after event `e`; `some none` after an event the role does not
follow (a broadcast value other than lane 0's); `none` after an unreadable address word, and
after the hand-off poll when the carried address is no bit value (`Value.regBits`), whose
deallocation would then be undefined behaviour. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .setMaxReg => some (some { d with site := .alloc })
  | .alloc =>
    if laneOf L g = 0 then some (some { d with site := .allocWrite })
    else some (some { d with site := .bar0 })
  | .allocWrite => some (some { d with site := .bar0 })
  | .bar0 => some (some { d with site := .ldBase })
  | .ldBase =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v => some (some { d with site := .shflQ, base := v })
      | .error _ => none
    | _ => none
  | .shflQ =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      if v = b32 (qLo L false) then some (some (start L g d)) else some none
    | _ => none
  | .qWait k =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      if ok then some (some { d with site := if k = 0 then .kvWait 0 else .shfl 2 })
      else some (some d)
    | _ => none
  | .kvWait k =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := kvNext k } else d))
    | _ => none
  | .pWait k =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := pNext k } else d))
    | _ => none
  | .p2Wait k lead =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := p2Next k lead } else d))
    | _ => none
  | .shfl k =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      if v = shflVal L d k then some (some { d with site := shflNext k }) else some none
    | _ => none
  | .elM b =>
    match e.kind with
    | .elect _ _ ld =>
      some (some { d with site := if laneOf L g = ld then .mma b 0 else skipGrp b })
    | _ => none
  | .mma b j => some (some { d with site := mmaNext b j })
  | .elC c =>
    match e.kind with
    | .elect _ _ ld =>
      if laneOf L g = ld then some (some { d with site := .commit c })
      else some (some (afterCommit L g d c))
    | _ => none
  | .commit c => some (some (afterCommit L g d c))
  | .relinquish => some (some { d with site := .bar1 })
  | .bar1 => some (some { d with site := .arrivePeer })
  | .arrivePeer => some (some { d with site := .waitDealloc })
  | .waitDealloc =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      if ok then (if d.base.regBits.isSome then some (some { d with site := .dealloc }) else none)
      else some (some d)
    | _ => none
  | .dealloc => some (some { d with site := .exit })
  | .exit => none

/-! ### Segment tactic -/

/-- The value-table reduction used after evaluating a segment. -/
macro "mma_values" : tactic =>
  `(tactic| simp only [valueOf, values, qVals, asmVals, PTX.Flow.lookupLit, Option.getD_some,
    Option.getD_none])

/-- Evaluate an MMA segment from `h` and close the facts of its end state. -/
syntax "mma_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| mma_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try mma_values
        all_goals seg_close [$extra,*]))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
