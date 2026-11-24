-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
public import Kernels.TmlFa4Fwd.Proof.Lib.SchedWords

@[expose] public section

/-! # The MMA warp as a site machine

Warp 12 runs from its first barrier after the allocation of its Tensor Memory columns (pc 1910)
to its `ret`. The `setmaxnreg` and the allocation before it (on lane 0 two events, the request
and the write of the address) belong to the hand-off (`Thread.lean`): a machine state at an
allocation would have to sit at sub-step 1 on lane 0. The warp meets the softmax and correction
warps at named barrier 2 (`bar1`), reads the allocated address back (`ldAlloc`) and broadcasts
the Q descriptor base (`bcast`). The persistent scheduler's first pass picks the CTA's
tile exactly as in the output warp (`word` … `tiles`, the same arithmetic on other registers,
recorded in `Epilogue.D`); the tile's coordinates give the request's offsets and used-K length
(`q0`, `q1`, `uk`) and the number of K/V blocks.

The pipeline is then: wait for Q stage 0 and K slot 0 (`wt 0`, `wt 1`), the QK MMAs of stage 0
(`eq 0` elects the issuing lane, `qk 0 j`), a commit (`ce 0`, `cm 0`), Q stage 1 (`wt 2`), the QK
MMAs of stage 1 (`qk 1 j`) and two commits. Each further K/V block is one round of the loop: the
V slot and the P half of stage 0 (`wt 3`, `wt 4`), the PV MMAs of stage 0 (`pv 0 j`, with a wait
for the second half of P between `j = 5` and `6`, `mw 0`), the next K slot (`wt 5`), the QK MMAs of
stage 0, a commit, P of stage 1 (`wt 6`), the PV MMAs of stage 1 (`pv 1 j`, `mw 1`), the release of
the V slot, the QK MMAs of stage 1 and the release of the K slot. The tail issues the last two PV
blocks (`pv 2`, `pv 3`) and three commits; the scheduler's second pass then finds no further tile,
and the warp gives up its allocation permit (`relinq`), meets the other warps again (`bar2`),
frees its columns (`dealloc`) and returns (`exit`).

Every shuffle in the pipeline broadcasts a word from lane 0; the machine records the word it
receives (`s0` … `s13`). The Q descriptors are inline-assembly registers that each QK block
moves by `∓2048`; the machine records their 64-bit words (`qd`). The loop registers `%r6144` to
`%r6148` are recorded as `trip`, `pp`, `accum`, `slot` and `kvp`. A load or shuffle of a 32-bit
register whose value is not a word stops the machine (`some none`); the address read back after
the allocation is recorded whatever it is (`ta`), as only the deallocation reads it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (tilesOf prefixOf addrU addrS Scan laneW ctaW paramW
  batchOf skipFirst reqOf skipLoop tlOf prefixD headsW lanePreds partials loopRegs chosen loopOf)

noncomputable section

/-! ### The matrix descriptors -/

/-- The upper word of every shared-memory matrix descriptor. -/
abbrev dhi : BitVec 64 := i32 1073758272
/-- A matrix descriptor from its lower word. -/
abbrev desc (lo : BitVec 64) : Value := joinValue (.bits 32 lo) (.bits 32 dhi)

/-- The descriptor offsets of the eight K-steps of a QK block. -/
def qoff (k : Fin 8) : Int := [0, 2, 4, 6, 1024, 1026, 1028, 1030].getD k.val 0

/-- The lower word of a QK block's descriptor `k` from its start word. -/
def qlo (st : BitVec 64) (k : Fin 8) : BitVec 64 := if k = 0 then st else addi st (qoff k)

/-- The Q descriptors after the broadcast of their base `x`. -/
def qinit (x : BitVec 64) (k : Fin 8) : BitVec 64 := qlo x k ||| dhi <<< 32

/-- A Q descriptor moved by `off`, as the inline assembly unpacks, adds and repacks it. -/
def qstep (w : BitVec 64) (off : Int) : BitVec 64 :=
  addi (truncBits 32 w) off ||| truncBits 32 (BitVec.ofNat 64 (w.toNat / 2 ^ 32)) <<< 32

/-- The lower word of a PV block's B descriptor at its MMA `j` (`j = 5` also at the wait). -/
def pvlo (st : BitVec 64) : Nat → BitVec 64
  | 0 => st
  | 6 => addi (addi st 640) 128
  | 7 => addi (addi (addi st 640) 128) 128
  | j => addi st (128 * j)

/-! ### Sites -/

inductive Site where
  | bar1 | ldAlloc | bcast
  | word (k : Scan)
  | down (k : Scan)
  | up (k : Scan) (j : Fin 5)
  | total (k : Scan)
  | vote (late : Bool)
  | pre (late : Bool)
  | tiles (late : Bool)
  | q0 | q1 | uk
  /-- The polls outside the PV blocks. -/
  | wt (k : Fin 10)
  /-- The broadcasts of the pipeline. -/
  | sh (k : Fin 14)
  /-- The election before QK block `b`, and its MMAs. -/
  | eq (b : Fin 4)
  | qk (b : Fin 4) (j : Fin 8)
  /-- The election before PV block `b`, its MMAs, and its poll before MMA 6 on the elected
  (`ld`) or another lane. -/
  | ep (b : Fin 4)
  | pv (b : Fin 4) (j : Fin 8)
  | mw (b : Fin 4) (ld : Bool)
  /-- The election before commit `c`, and the commit. -/
  | ce (c : Fin 12)
  | cm (c : Fin 12)
  /-- The end, after the first pass (no tile, `late = false`) or the second. -/
  | relinq (late : Bool) | bar2 (late : Bool) | dealloc (late : Bool) | exit (late : Bool)
  deriving DecidableEq

def Site.pc : Site → Nat
  | .bar1 => 1910
  | .ldAlloc => 1911
  | .bcast => 1916
  | .word k => match k with | .first => 1940 | .loop => 1999 | .second => 2653 | .loop2 => 2707
  | .down k => match k with | .first => 1941 | .loop => 2001 | .second => 2654 | .loop2 => 2709
  | .up k j => match k with
    | .first => 1960 + 4 * j.val | .loop => 2022 + 3 * j.val
    | .second => 2673 + 3 * j.val | .loop2 => 2730 + 3 * j.val
  | .total k => match k with | .first => 1980 | .loop => 2037 | .second => 2688 | .loop2 => 2745
  | .vote l => if l then 2756 else 2050
  | .pre l => if l then 2761 else 2057
  | .tiles l => if l then 2762 else 2061
  | .q0 => 2112
  | .q1 => 2113
  | .uk => 2116
  | .wt k => [2141, 2145, 2210, 2294, 2297, 2352, 2419, 2545, 2548, 2595].getD k.val 0
  | .sh k => [2151, 2152, 2214, 2307, 2308, 2310, 2361, 2423, 2425, 2558, 2559, 2561, 2599,
      2601].getD k.val 0
  | .eq b => [2153, 2215, 2363, 2464].getD b.val 0
  | .qk b j => [2197, 2259, 2407, 2508].getD b.val 0 + j.val
  | .ep b => [2311, 2426, 2562, 2602].getD b.val 0
  | .pv b j => [2319, 2434, 2570, 2610].getD b.val 0 + [0, 3, 6, 9, 12, 15, 21, 24].getD j.val 0
  | .mw b _ => [2335, 2450, 2586, 2626].getD b.val 0
  | .ce c => [2205, 2267, 2271, 2415, 2459, 2516, 2520, 2534, 2538, 2635, 2639, 2643].getD c.val 0
  | .cm c => [2208, 2270, 2274, 2418, 2462, 2519, 2523, 2537, 2541, 2638, 2642, 2646].getD c.val 0
  | .relinq _ => 2763
  | .bar2 _ => 2764
  | .dealloc _ => 2766
  | .exit _ => 9205

/-! ### States -/

/-- The values a state records. -/
structure V where
  /-- The scheduler's scan: the words its events returned and its loop state (its `site` is
  not read). -/
  sc : Epilogue.D := { site := .start }
  /-- The value read back from the allocation's address word. -/
  ta : Value := .pred false
  /-- The 64-bit words of the eight Q descriptors. -/
  qd : Fin 8 → BitVec 64 := fun _ => 0
  /-- The request's used-K length. -/
  ukw : BitVec 64 := 0
  /-- The words the pipeline's broadcasts returned. -/
  s0 : BitVec 64 := 0
  s1 : BitVec 64 := 0
  s2 : BitVec 64 := 0
  s3 : BitVec 64 := 0
  s4 : BitVec 64 := 0
  s5 : BitVec 64 := 0
  s6 : BitVec 64 := 0
  s7 : BitVec 64 := 0
  s8 : BitVec 64 := 0
  s9 : BitVec 64 := 0
  s10 : BitVec 64 := 0
  s11 : BitVec 64 := 0
  s12 : BitVec 64 := 0
  s13 : BitVec 64 := 0
  /-- The loop registers: the negated count of rounds left (`%r6144`), the P parity (`%r6145`),
  the accumulate flag of the PV MMAs (`%r6146`), the K/V slot (`%r6147`) and its parity
  (`%r6148`). -/
  trip : BitVec 64 := 0
  pp : BitVec 64 := 0
  accum : BitVec 64 := 0
  slot : BitVec 64 := 0
  kvp : BitVec 64 := 0
  /-- Ghost: the pipeline's broadcasts so far. -/
  ps : Nat := 0

structure D where
  site : Site
  v : V

/-! ### Register values -/

/-- The number of K/V blocks of the tile (`%r129`). -/
def blocks (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  min32 (ceil128 v.ukw)
    (ceil128 (add32 (add32 v.ukw (coords p L g v.sc).row) (sub32 v.sc.c0 v.sc.c1)))

/-- The registers of the launch the warp keeps throughout. -/
def valuesStart (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1062, b32 12), (1072, .bits 32 (ctaW L g)), (1178, b32 (L.sharedBase + 68608)),
   (2535, b32 L.sharedBase), (6495, b32 (L.sharedBase + 144)), (7502, b64 p.cuQBase),
   (7506, b64 p.cuQBase), (7503, b64 p.usedKBase)]

/-- The registers of the scheduler and the pipeline that keep one value wherever they are live:
the allocation address, the lane, the skip predicate of the first pass, the heads, the Q
descriptors and their instruction descriptor. -/
def valuesRole (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  [(1179, v.ta), (1180, .bits 32 (laneW L g)), (337, .pred (skipFirst p L g)),
   (7139, .bits 32 (headsW p)), (9632, w32 (i32 136316048)),
   (9624, .bits 64 (v.qd 0)), (9625, .bits 64 (v.qd 1)), (9626, .bits 64 (v.qd 2)),
   (9627, .bits 64 (v.qd 3)), (9628, .bits 64 (v.qd 4)), (9629, .bits 64 (v.qd 5)),
   (9630, .bits 64 (v.qd 6)), (9631, .bits 64 (v.qd 7))]

/-- The registers of a scan round. -/
def valuesScan (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : Scan → List (Nat × Value)
  | .first =>
    [(7877, addrU p.cuQBase (laneW L g)), (7193, .bits 32 c.w), (7196, .bits 32 c.tl),
     (7203, b32 p.batch)] ++ partials L g c 2465 3 7197
  | .loop =>
    loopRegs p L g false c 1182 7194 7199 7879 ++
    [(349, .pred (scmpi .eq .b (laneW L g) 31)), (7195, .bits 32 c.w), (7196, .bits 32 c.tl),
     (7203, b32 p.batch)] ++ lanePreds L g 355 ++ partials L g c 2486 3 7197
  | .second =>
    [(7884, addrU p.cuQBase (laneW L g)), (7209, .bits 32 c.w), (7212, .bits 32 c.tl),
     (7149, .bits 32 (paramW p.batch))] ++ lanePreds L g 414 ++ partials L g c 2642 3 7213
  | .loop2 =>
    loopRegs p L g true c 1196 7210 7215 7886 ++
    [(422, .pred (scmpi .eq .b (laneW L g) 31)), (7211, .bits 32 c.w), (7212, .bits 32 c.tl),
     (7149, .bits 32 (paramW p.batch))] ++ lanePreds L g 428 ++ partials L g c 2663 3 7213

/-- The registers of the choice of a request, in the first pass. -/
def valuesSelect (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  let r126 := sub32 c.cur (mul32 c.tot (headsW p))
  [(362, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p) r126) (ctaW L g))),
   (1186, .bits 32 r126), (7199, .bits 32 c.gx), (7196, .bits 32 c.tl),
   (7197, .bits 32 (prefixD L g c)), (1187, .bits 32 (popc c.bal)),
   (2501, .bits 32 (addi (popc c.bal) (-1))), (7203, .bits 32 (chosen c)), (7201, .bits 32 c.pv),
   (7148, .bits 32 (paramW p.batch)), (7156, .bits 32 (paramW 800))]

/-- The registers of the second pass's ballot. -/
def valuesSelect2 (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  [(435, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p)
      (sub32 c.cur (mul32 c.tot (headsW p)))) (ctaW L g))),
   (7212, .bits 32 c.tl), (7213, .bits 32 (prefixD L g c)), (1200, .bits 32 (popc c.bal)),
   (2679, .bits 32 (addi (popc c.bal) (-1)))]


/-- The registers of the request's reads. -/
def valuesReq (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let c := v.sc
  [(1188, sbi L 80), (2562, sbi L 8), (7202, .bits 32 (coords p L g c).row),
   (7880, wideS (chosen c)), (7881, addrS p.cuQBase (chosen c)), (2538, .bits 32 c.c0),
   (2540, .bits 32 (sub32 c.c0 c.c1)), (7882, addrS p.usedKBase (chosen c))]

/-- The next K/V slot (`%r132`) and its parity (`%r1512`). -/
abbrev slot1 (v : V) : BitVec 64 := sel (scmpi .eq .b (addi v.slot 1) 3) (i32 0) (addi v.slot 1)
abbrev kvp1 (v : V) : BitVec 64 :=
  xor32 v.kvp (sel (scmpi .eq .b (addi v.slot 1) 3) (i32 1) (i32 0))

/-- The shared address of a slot's barrier (`sb + 8 slot`). -/
abbrev slotAddr (L : Launch) (s : BitVec 64) : BitVec 64 := add32 (sbW L) (shl s 3)

/-- The B descriptor word of a slot (`%r1521`, `%r1532`, `%r1565`). -/
abbrev slotDesc (L : Launch) (s : BitVec 64) (tag : Int) : BitVec 64 :=
  ori (andi (shru (addi (add32 (sbW L) (shl s 15)) 68608) 4) 16320) tag

/-- The registers of the pipeline that keep one value wherever they are live. -/
def valuesPipe (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  [(1188, sbi L 80), (1189, .bits 32 (blocks p L g v)), (2562, sbi L 8), (2536, w32 (i32 0)),
   (2537, sbi L 32),
   (2560, w32 (ori (andi (shru (BitVec.ofNat 64 (L.sharedBase + 68608)) 4) 16320) 65536)),
   (2563, w32 (i32 0)), (2565, w32 (i32 128)),
   (2564, w32 v.s0), (2574, w32 v.s1), (2602, w32 v.s2),
   (2610, sbi L 96), (2614, sbi L 112), (2615, sbi L 104), (2618, sbi L 120), (1190, sbi L 88),
   (7204, w32 v.trip), (7205, w32 v.pp), (7206, w32 v.accum), (7207, w32 v.slot),
   (7208, w32 v.kvp),
   (1191, w32 (slotAddr L v.slot)), (2568, w32 (addi (slotAddr L v.slot) 32)),
   (2582, w32 (i32 64)), (2581, w32 (slotDesc L v.slot 67108864)), (2583, w32 (i32 256)),
   (2569, w32 v.s3), (2595, w32 v.s4), (2570, w32 v.s5),
   (1192, w32 (slot1 v)), (2572, w32 (kvp1 v)), (1193, w32 (slotAddr L (slot1 v))),
   (2571, w32 (addi (slotAddr L (slot1 v)) 32)), (2592, w32 (slotDesc L (slot1 v) 65536)),
   (2600, w32 v.s6), (2573, w32 (i32 0)), (2597, w32 (i32 192)), (2598, w32 (i32 384)),
   (2594, w32 v.s7), (2596, w32 v.s8), (2601, w32 (i32 0)),
   (1194, w32 (slotAddr L v.slot)), (2609, w32 (addi (slotAddr L v.slot) 32)),
   (2626, w32 (i32 64)), (2625, w32 (slotDesc L v.slot 67108864)), (2627, w32 (i32 256)),
   (2611, w32 v.s9), (2612, w32 v.s10), (2613, w32 v.s11), (2628, w32 (i32 192)),
   (2629, w32 (i32 384)), (2616, w32 v.s12), (2617, w32 v.s13)]

/-- The first scoped register of each QK block (its elected predicate), the block's B descriptor
start word and its accumulator column. -/
def qkBase (b : Fin 4) : Nat := [9636, 9653, 9682, 9709].getD b.val 0
def qkStart (v : V) (b : Fin 4) : BitVec 64 := if b.val < 2 then v.s0 else v.s6
def qkAcc (v : V) (b : Fin 4) : BitVec 64 := if b.val % 2 = 0 then v.s1 else v.s2

/-- The scoped registers of QK block `b`. -/
def valuesQk (v : V) (b : Fin 4) : List (Nat × Value) :=
  let r := qkBase b
  let st := qkStart v b
  [(r, .pred true), (r + 2, w32 (qkAcc v b)), (r + 8, desc (qlo st 0)), (r + 9, desc (qlo st 1)),
   (r + 10, desc (qlo st 2)), (r + 11, desc (qlo st 3)), (r + 12, desc (qlo st 4)),
   (r + 13, desc (qlo st 5)), (r + 14, desc (qlo st 6)), (r + 15, desc (qlo st 7))]

/-- The first scoped register of each PV block and its three broadcast words: the A operand's
column, the B descriptor start word and the accumulator column. -/
def pvBase (b : Fin 4) : Nat := [9671, 9699, 9727, 9738].getD b.val 0
def pvA (v : V) (b : Fin 4) : BitVec 64 := [v.s3, v.s7, v.s9, v.s12].getD b.val 0
def pvB (v : V) (b : Fin 4) : BitVec 64 := if b.val < 2 then v.s4 else v.s10
def pvAcc (v : V) (b : Fin 4) : BitVec 64 := [v.s5, v.s8, v.s11, v.s13].getD b.val 0

/-- The scoped registers of PV block `b` at its MMA `j` (the poll has those of `j = 5`), on a
lane whose election returned `ld`. -/
def valuesPv (v : V) (b : Fin 4) (j : Nat) (ld : Bool) : List (Nat × Value) :=
  let r := pvBase b
  [(r, .pred ld), (r + 1, .pred (scmpi .ne .b v.accum 0)), (r + 2, w32 (i32 136381584)),
   (r + 3, w32 (pvAcc v b)), (r + 4, w32 (pvA v b)), (r + 5, w32 (pvB v b)),
   (r + 6, w32 (pvlo (pvB v b) j)), (r + 7, w32 dhi), (r + 8, desc (pvlo (pvB v b) j))]

/-- The registers at state `d`. -/
def values (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  match d.site with
  | .bar1 | .ldAlloc => [(7203, b32 p.batch), (2451, w32 (i32 512))]
  | .bcast =>
    [(7203, b32 p.batch), (2455, w32 (ori (andi (shru (addi (sbW L) 35840) 4) 16320) 65536))]
  | .word k | .down k | .up k _ | .total k => valuesScan p L g d.v.sc k
  | .vote false | .pre false | .tiles false => valuesSelect p L g d.v.sc
  | .vote true | .pre true | .tiles true => valuesSelect2 p L g d.v.sc
  | .q0 | .q1 | .uk => valuesReq p L g d.v
  | .qk b _ => valuesQk d.v b ++ valuesPipe p L g d.v
  | .pv b j => valuesPv d.v b j.val true ++ valuesPipe p L g d.v
  | .mw b ld => valuesPv d.v b 5 ld ++ valuesPipe p L g d.v
  | .relinq _ | .bar2 _ | .dealloc _ | .exit _ => [(2682, w32 (i32 512))]
  | _ => valuesPipe p L g d.v

/-- The value of register `r` at state `d`; `ent` gives the startup registers the warp never
reads. -/
def valueOf (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) (d : D) (r : Nat) : Value :=
  ((values p L g d).lookup r).getD (((valuesRole p L g d.v).lookup r).getD
    (((valuesStart p L g).lookup r).getD (ent r)))

abbrev facts (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) (d : D) :
    List (Nat × Value) :=
  Flow.factsFrom (Flow.live d.site.pc) (valueOf p L g ent d)

/-! ### Transitions -/

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- A state at site `s` with the scan state changed by `f`. -/
abbrev scAt (d : D) (s : Site) (f : Epilogue.D → Epilogue.D) : D := ⟨s, { d.v with sc := f d.v.sc }⟩

/-- The end of the scan of pass `late`, with the last group's capped first request `gx` and the
tiles `cur` through it: past the batch, no tile; else the ballot. -/
def scanExit (p : Params) (late : Bool) (d : D) (gx cur : BitVec 64) : D :=
  if scmp .ge .s gx (batchOf p late) then { d with site := .relinq late }
  else scAt d (.vote late) fun c => { c with gx := gx, cur := cur }

/-- The loop head of pass `late` with group start `grp` and tiles `acc` before it. -/
def loopHead (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) (grp acc : BitVec 64) :
    D :=
  if scmp .ge .s (addi grp 31) (batchOf p late) then
    scanExit p late d (min32 (addi grp 31) (batchOf p late)) (addi (ctaW L g) 1)
  else if scmp .gt .s (reqOf L g grp) (batchOf p late) then
    scAt d (.down (loopOf late)) fun c => { c with grp := grp, acc := acc, w := i32 0 }
  else scAt d (.word (loopOf late)) fun c => { c with grp := grp, acc := acc }

/-- After lane 31's prefix sum `x` of a round of scan `k`. -/
def afterTotal (p : Params) (L : Launch) (g : Nat) (k : Scan) (d : D) (x : BitVec 64) : D :=
  let d := scAt d d.site fun c => { c with tot := x }
  match k with
  | .first | .second =>
    if scmp .gt .s (mul32 x (headsW p)) (ctaW L g) then
      scanExit p k.late d (i32 0) (mul32 x (headsW p))
    else loopHead p L g k.late d (i32 0) (mul32 x (headsW p))
  | .loop | .loop2 =>
    if scmp .le .s (mad32 x (headsW p) d.v.sc.acc) (ctaW L g) then
      loopHead p L g k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.v.sc.acc)
    else scanExit p k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
      (mad32 x (headsW p) d.v.sc.acc)

/-- After the chosen request's tile count `x`: the coordinates, then the request's reads if
the request exists. A division without a rule faults the thread. -/
def afterTiles (p : Params) (L : Launch) (g : Nat) (d : D) (x : BitVec 64) : Option D :=
  let d := scAt d d.site fun c => { c with nt := x }
  if divOk (coords p L g d.v.sc).n1 (coords p L g d.v.sc).d1 then
    if divOk (coords p L g d.v.sc).n2 (coords p L g d.v.sc).d2 then
      some (if scmp .lt .s (chosen d.v.sc) (paramW p.batch) then { d with site := .q0 }
        else { d with site := .relinq false })
    else none
  else none

/-- The start of a scheduler pass: lanes past the batch skip their read. -/
def passStart (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) : D :=
  let k : Scan := if late then .second else .first
  if scmp .gt .s (laneW L g) (if late then paramW p.batch else BitVec.ofNat 64 p.batch) then
    scAt d (.down k) fun c => { c with w := i32 0 }
  else { d with site := .word k }

/-- The loop registers on entry: the loop when the tile has two blocks or more, else the
tail. -/
def enterLoop (p : Params) (L : Launch) (g : Nat) (d : D) : D :=
  if scmpi .lt .s (blocks p L g d.v) 2 then
    ⟨.ce 7, { d.v with pp := i32 0, accum := i32 0, slot := i32 1, kvp := i32 0 }⟩
  else
    ⟨.wt 3, { d.v with
      trip := neg32 (blocks p L g d.v), pp := i32 0, accum := i32 0, slot := i32 1,
      kvp := i32 0 }⟩

/-- The end of a loop round: the next slot and parities, then another round or the tail. -/
def loopEnd (d : D) : D :=
  let s := addi (slot1 d.v) 1
  let v := { d.v with
    slot := sel (scmpi .eq .b s 3) (i32 0) s,
    kvp := xor32 (kvp1 d.v) (sel (scmpi .eq .b s 3) (i32 1) (i32 0)), pp := xori d.v.pp 1,
    trip := addi d.v.trip 1, accum := i32 1 }
  if scmpi .ne .b (addi d.v.trip 1) (-1) then ⟨.wt 3, v⟩ else ⟨.ce 7, v⟩

/-- Record broadcast `k`'s word. -/
def setS (v : V) (x : BitVec 64) : Fin 14 → V
  | 0 => { v with s0 := x } | 1 => { v with s1 := x } | 2 => { v with s2 := x }
  | 3 => { v with s3 := x } | 4 => { v with s4 := x } | 5 => { v with s5 := x }
  | 6 => { v with s6 := x } | 7 => { v with s7 := x } | 8 => { v with s8 := x }
  | 9 => { v with s9 := x } | 10 => { v with s10 := x } | 11 => { v with s11 := x }
  | 12 => { v with s12 := x } | 13 => { v with s13 := x }

/-- The site after broadcast `k`. -/
def shNext : Fin 14 → Site
  | 0 => .sh 1 | 1 => .eq 0 | 2 => .eq 1 | 3 => .sh 4 | 4 => .sh 5 | 5 => .ep 0 | 6 => .eq 2
  | 7 => .sh 8 | 8 => .ep 1 | 9 => .sh 10 | 10 => .sh 11 | 11 => .ep 2 | 12 => .sh 13 | 13 => .ep 3

/-- The site after a successful poll `k` (`wt 4` of the loop is followed by its broadcasts). -/
def wtNext : Fin 10 → Site
  | 0 => .wt 1 | 1 => .sh 0 | 2 => .sh 2 | 3 => .wt 4 | 4 => .sh 3 | 5 => .sh 6 | 6 => .sh 7
  | 7 => .wt 8 | 8 => .sh 9 | 9 => .sh 12

/-- The site after QK block `b` (its first commit's election). -/
def qkDone : Fin 4 → Site
  | 0 => .ce 0 | 1 => .ce 1 | 2 => .ce 3 | 3 => .ce 5

/-- The site after PV block `b`. -/
def pvDone : Fin 4 → Site
  | 0 => .wt 5 | 1 => .ce 4 | 2 => .wt 9 | 3 => .ce 9

/-- The Q descriptors' move in QK block `b`. -/
def qkOff (b : Fin 4) : Int := if b.val % 2 = 0 then -2048 else 2048

/-- The site after commit `c`, or after its election on a lane that does not commit, as a
function of the state (the loop entry and end, and the start of the second pass). -/
def ceNext (p : Params) (L : Launch) (g : Nat) (d : D) : Fin 12 → D
  | 0 => { d with site := .wt 2 }
  | 1 => { d with site := .ce 2 }
  | 2 => enterLoop p L g d
  | 3 => { d with site := .wt 6 }
  | 4 => { d with site := .eq 3 }
  | 5 => { d with site := .ce 6 }
  | 6 => loopEnd d
  | 7 => { d with site := .ce 8 }
  | 8 => { d with site := .wt 7 }
  | 9 => { d with site := .ce 10 }
  | 10 => { d with site := .ce 11 }
  | 11 => passStart p L g true d

/-- The successor after event `e`. -/
def succ (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .bar1 => some (some { d with site := .ldAlloc })
  | .ldAlloc =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => some (some ⟨.bcast, { d.v with ta := v }⟩)
      | .error _ => none
    | _ => none
  | .bcast =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      passStart p L g false ⟨.bcast, { d.v with qd := qinit x }⟩
    | _ => none
  | .word k =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => scAt d (.down k) fun c => { c with w := x }
      | .error _ => none
    | _ => none
  | .down k =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      scAt d (.up k 0) fun c => { c with dn := x, tl := tlOf p L g k c x }
    | _ => none
  | .up k j =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      match j with
      | 0 => scAt d (.up k 1) fun c => { c with u1 := x }
      | 1 => scAt d (.up k 2) fun c => { c with u2 := x }
      | 2 => scAt d (.up k 3) fun c => { c with u4 := x }
      | 3 => scAt d (.up k 4) fun c => { c with u8 := x }
      | 4 => scAt d (.total k) fun c => { c with u16 := x }
    | _ => none
  | .total k =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v (afterTotal p L g k d)
    | _ => none
  | .vote late =>
    match e.kind with
    | .vote _ _ b =>
      let d := scAt d d.site fun c => { c with bal := BitVec.ofNat 64 b.toNat }
      some (some (if scmpi .eq .b d.v.sc.bal 0 then
          scAt d (.tiles late) fun c => { c with pv := i32 0 }
        else { d with site := .pre late }))
    | _ => none
  | .pre late =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      if late then scAt d (.tiles true) fun c => c
      else scAt d (.tiles false) fun c => { c with pv := mul32 x (headsW p) }
    | _ => none
  | .tiles late =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match v with
      | .bits 32 x =>
        if late then some (some (scAt d (.relinq true) fun c => c))
        else (afterTiles p L g d x).map some
      | _ => some none
    | _ => none
  | .q0 =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => scAt d .q1 fun c => { c with c0 := x }
      | .error _ => none
    | _ => none
  | .q1 =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => scAt d .uk fun c => { c with c1 := x }
      | .error _ => none
    | _ => none
  | .uk =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => ⟨.wt 0, { d.v with ukw := x }⟩
      | .error _ => none
    | _ => none
  | .wt k =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := wtNext k } else d))
    | _ => none
  | .sh k =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x => ⟨shNext k, { setS d.v x k with ps := d.v.ps + 1 }⟩
    | _ => none
  | .eq b =>
    match e.kind with
    | .elect _ _ ld =>
      let v := { d.v with qd := fun i => qstep (d.v.qd i) (qkOff b) }
      some (some ⟨if laneOf L g = ld then .qk b 0 else qkDone b, v⟩)
    | _ => none
  | .qk b j => some (some { d with site := if j.val = 7 then qkDone b else .qk b (j + 1) })
  | .ep b =>
    match e.kind with
    | .elect _ _ ld =>
      some (some { d with site := if laneOf L g = ld then .pv b 0 else .mw b false })
    | _ => none
  | .pv b j =>
    some (some { d with
      site := if j.val = 5 then .mw b true else if j.val = 7 then pvDone b else .pv b (j + 1) })
  | .mw b ld =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      some (some (if ok then { d with site := if ld then .pv b 6 else pvDone b } else d))
    | _ => none
  | .ce c =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (if laneOf L g = ld then { d with site := .cm c } else ceNext p L g d c))
    | _ => none
  | .cm c => some (some (ceNext p L g d c))
  | .relinq l => some (some { d with site := .bar2 l })
  | .bar2 l => some (some { d with site := .dealloc l })
  | .dealloc l => some (some { d with site := .exit l })
  | .exit _ => none

/-- The MMA warp as a code machine. -/
@[reducible] def code (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := ⟨.bar1, {}⟩
  pc := (·.site.pc)
  facts := facts p L g ent
  inv := fun _ => True
  next := succ p L g

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
