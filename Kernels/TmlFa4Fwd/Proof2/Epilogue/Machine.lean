-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites
public import Lemmas.Flow.Step.SiteCases
public import Lemmas.Flow.Arith32Word

@[expose] public section

/-! # The output warp as a site machine

Warp 13 runs from its `setmaxnreg` (PTX line 3265) to its `ret`. Its lanes pick the tile of
their CTA by the persistent scheduler's first pass: every lane reads one cumulative query
offset (`word`), the warp turns the offsets into tile counts (`down`) and their prefix sums
(`up`, five shuffles), and lane 31's sum (`total`) decides whether the CTA's tile lies in the
first 32 requests or a later group of 31 (the loop rounds). A ballot (`vote`), the prefix and
the count of the chosen request (`pre`, `tiles`) give the tile's coordinates. The warp then
reads the request's two offsets (`q0`, `q1`), and stores the output tile in two stages: a poll
of the stage's ready barrier (`ready`), four tensor stores (`store`), a bulk-group commit; then
it waits for the stores to read shared memory (`drain`) and frees each stage (`free`). The
scheduler's second pass repeats the search for the next tile, which never exists, and the warp
returns (`exit`).

The machine follows any value an event returns: a load or shuffle of a 32-bit word records the
word (`.bits 32 x`), and a value of another kind stops the machine (`some none`), as no b32
register of the warp ever holds one. The registers live at each site are a function of the
launch, the recorded words and the loop state (`values`); every comparison the code branches on
is the same expression in `succ`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The arithmetic of the code, on the bits its registers hold -/

export PTX.Flow.Arith32 (r32 i32 add32 addi sub32 mul32 mad32 min32 shrs shru shl andi xor32
  not32 popc scmp scmpi sel sdiv divOk fdiv W toNat_W r32_W i32_W add32_W addi_W addi31_W addi1_W
  i32_zero scmp_W toSigned_W scmp_lt_W scmp_le_W scmp_gt_W scmp_ge_W min32_W sub32_W mul32_W
  mad32_W toNat_shrs_W scmp_ne_b_W scmpi_gt_neg1_W shl8_W not32_add_W sdiv_W fdiv_W popc_W)

/-- The tiles of 256 rows that a request of `dn - w` rows needs (rounded up). -/
def tilesOf (dn w : BitVec 64) : BitVec 64 :=
  let r := sub32 dn w
  let s := add32 r (shru (shrs r 31) 24)
  add32 (shrs s 8) (sel (scmpi .gt .s r (-1) && scmp .ne .b r (andi s (-256))) (i32 1) (i32 0))

/-- The partial sums of the five `up` steps: lane `l` adds the count of lane `l - 1`, then the
sums `2`, `4`, `8`, `16` lanes below. -/
abbrev ps1 (lane tl u : BitVec 64) : BitVec 64 := add32 (sel (scmpi .eq .b lane 0) (i32 0) u) tl
abbrev psk (lane s u : BitVec 64) (k : Int) : BitVec 64 :=
  add32 s (sel (scmpi .gt .u lane k) u (i32 0))

/-- The inclusive prefix sum of the tile counts that the five `up` shuffles build. -/
abbrev prefixOf (lane tl u1 u2 u4 u8 u16 : BitVec 64) : BitVec 64 :=
  psk lane (psk lane (psk lane (psk lane (ps1 lane tl u1) u2 1) u4 3) u8 7) u16 15

/-- A global address: a 64-bit base plus four times an unsigned (`wide.u32`) or signed
(`wide.s32`) 32-bit index. -/
abbrev addrU (base : Nat) (i : BitVec 64) : Value :=
  .bits 64 (truncBits 64 (truncBits 64 (BitVec.ofNat 64 base) +
    truncBits 64 (BitVec.ofNat 64 ((r32 i).toNat * (i32 4).toNat))))
abbrev addrS (base : Nat) (i : BitVec 64) : Value :=
  .bits 64 (truncBits 64 (truncBits 64 (BitVec.ofNat 64 base) +
    truncBits 64 (truncBits (2 * 32)
      (BitVec.ofInt 64 (toSigned 32 (r32 i) * toSigned 32 (i32 4))))))

/-! ### Sites -/

/-- The four scans of the scheduler: the first round and the loop rounds of each pass. -/
inductive Scan where
  | first | loop | second | loop2
  deriving DecidableEq

/-- The second pass. -/
def Scan.late : Scan → Bool
  | .second | .loop2 => true
  | _ => false

inductive Site where
  | start
  | word (k : Scan)
  | down (k : Scan)
  | up (k : Scan) (j : Fin 5)
  | total (k : Scan)
  | vote (late : Bool)
  | pre (late : Bool)
  | tiles (late : Bool)
  | q0 | q1
  | ready (st : Fin 2)
  | store (st : Fin 2) (b : Fin 4)
  | commit (st : Fin 2)
  | drain (st : Fin 2)
  | free (st : Fin 2)
  /-- The return, after the first pass (no tile) or the second. -/
  | exit (late : Bool)
  deriving DecidableEq

def Scan.word : Scan → Nat
  | .first => 2776 | .loop => 2835 | .second => 2989 | .loop2 => 3043

def Scan.down : Scan → Nat
  | .first => 2777 | .loop => 2837 | .second => 2990 | .loop2 => 3045

def Scan.up : Scan → Nat
  | .first => 2796 | .loop => 2858 | .second => 3009 | .loop2 => 3066

def Scan.total : Scan → Nat
  | .first => 2816 | .loop => 2873 | .second => 3024 | .loop2 => 3081

def Site.pc : Site → Nat
  | .start => 2769
  | .word k => k.word
  | .down k => k.down
  | .up .first j => 2796 + 4 * j.val
  | .up k j => k.up + 3 * j.val
  | .total k => k.total
  | .vote l => if l then 3092 else 2887
  | .pre l => if l then 3097 else 2894
  | .tiles l => if l then 3098 else 2898
  | .q0 => 2953
  | .q1 => 2954
  | .ready st => if st = 0 then 2958 else 2972
  | .store 0 b => [2963, 2965, 2967, 2969].getD b.val 0
  | .store _ b => 2976 + b.val
  | .commit st => if st = 0 then 2970 else 2980
  | .drain st => if st = 0 then 2981 else 2984
  | .free st => if st = 0 then 2983 else 2985
  | .exit _ => 9205

/-! ### States -/

/-- A state: the site, the words the warp's events returned in the current round, and the
scheduler's loop state. -/
structure D where
  site : Site
  /-- The lane's cumulative offset of the round. -/
  w : BitVec 64 := 0
  /-- The next lane's offset (`down`). -/
  dn : BitVec 64 := 0
  /-- The lane's tile count of the round. -/
  tl : BitVec 64 := 0
  /-- The five `up` shuffles. -/
  u1 : BitVec 64 := 0
  u2 : BitVec 64 := 0
  u4 : BitVec 64 := 0
  u8 : BitVec 64 := 0
  u16 : BitVec 64 := 0
  /-- Lane 31's prefix sum: the round's tile count. -/
  tot : BitVec 64 := 0
  /-- The first request of the round's group, before the round's step of 31. -/
  grp : BitVec 64 := 0
  /-- The tiles before the round's group. -/
  acc : BitVec 64 := 0
  /-- The last group's first request, and the tiles through it, when the scan stops. -/
  gx : BitVec 64 := 0
  cur : BitVec 64 := 0
  /-- The ballot, the chosen request's prefix (times the heads) and tile count. -/
  bal : BitVec 64 := 0
  pv : BitVec 64 := 0
  nt : BitVec 64 := 0
  /-- The chosen request's two offsets. -/
  c0 : BitVec 64 := 0
  c1 : BitVec 64 := 0

/-! ### Register values -/

/-- The lane index as `%laneid` reads it. -/
abbrev laneW (L : Launch) (g : Nat) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 (laneOf L g))
/-- The CTA index, the tile the CTA owns. -/
abbrev ctaW (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (g / L.block)
/-- A 32-bit parameter word as `ld.param` reads it. -/
abbrev paramW (n : Nat) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 n)

/-- The batch size as the scan of pass `late` reads it. -/
def batchOf (p : Params) (late : Bool) : BitVec 64 :=
  if late then paramW p.batch else BitVec.ofNat 64 p.batch

/-- The condition of skipping a lane's tile count: past the batch, or lane 31. -/
def skipFirst (p : Params) (L : Launch) (g : Nat) : Bool :=
  !(scmpi .ne .b (laneW L g) 31 && scmp .lt .s (laneW L g) (BitVec.ofNat 64 p.batch))

/-- The request a loop round's lane reads: the group's first request plus 31 plus the lane. -/
abbrev reqOf (L : Launch) (g : Nat) (grp : BitVec 64) : BitVec 64 :=
  add32 (addi grp 31) (laneW L g)

/-- The condition of skipping a lane's tile count in a loop round. -/
def skipLoop (p : Params) (L : Launch) (g : Nat) (late : Bool) (grp : BitVec 64) : Bool :=
  scmpi .eq .b (laneW L g) 31 || scmp .ge .s (reqOf L g grp) (batchOf p late)

/-- The lane's tile count after the `down` shuffle returned `x`. -/
def tlOf (p : Params) (L : Launch) (g : Nat) (k : Scan) (d : D) (x : BitVec 64) : BitVec 64 :=
  match k with
  | .first | .second => sel (skipFirst p L g) (i32 0) (tilesOf x d.w)
  | .loop => sel (skipLoop p L g false d.grp) (i32 0) (tilesOf x d.w)
  | .loop2 => sel (skipLoop p L g true d.grp) (i32 0) (tilesOf x d.w)

/-- The lane's prefix sum of the round. -/
abbrev prefixD (L : Launch) (g : Nat) (d : D) : BitVec 64 :=
  prefixOf (laneW L g) d.tl d.u1 d.u2 d.u4 d.u8 d.u16

/-- The heads as `ld.param` reads them. -/
abbrev headsW (p : Params) : BitVec 64 := paramW p.heads

/-- The registers of the launch: the startup values the warp keeps throughout. -/
def valuesStart (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1062, b32 13), (1072, .bits 32 (ctaW L g)), (1178, b32 (L.sharedBase + 68608)),
   (2390, b32 (L.sharedBase + 208)), (2535, b32 L.sharedBase), (6497, b32 (L.sharedBase + 224)),
   (7228, b32 p.batch), (7290, .ptr 64 false (.param (param 10)) 0),
   (7502, b64 p.cuQBase), (7506, b64 p.cuQBase), (1201, .bits 32 (laneW L g)),
   (268, .pred (skipFirst p L g)), (7138, .bits 32 (headsW p))]

/-- The lane predicates of a round's `up` steps (`> 15`, `> 7`, `> 3`, `> 1`, `= 0`) from
register `r`. -/
def lanePreds (L : Launch) (g r : Nat) : List (Nat × Value) :=
  [(r, .pred (scmpi .gt .u (laneW L g) 15)), (r + 1, .pred (scmpi .gt .u (laneW L g) 7)),
   (r + 2, .pred (scmpi .gt .u (laneW L g) 3)), (r + 3, .pred (scmpi .gt .u (laneW L g) 1)),
   (r + 4, .pred (scmpi .eq .b (laneW L g) 0))]

/-- The partial sums of a round's `up` steps, in registers `r`, `r + k`, `r + 2k`, `r + 3k`, and
the prefix sum in register `q`. -/
def partials (L : Launch) (g : Nat) (d : D) (r k q : Nat) : List (Nat × Value) :=
  let s1 := ps1 (laneW L g) d.tl d.u1
  let s2 := psk (laneW L g) s1 d.u2 1
  let s3 := psk (laneW L g) s2 d.u4 3
  let s4 := psk (laneW L g) s3 d.u8 7
  [(r, .bits 32 s1), (r + k, .bits 32 s2), (r + 2 * k, .bits 32 s3), (r + 3 * k, .bits 32 s4),
   (q, .bits 32 (psk (laneW L g) s4 d.u16 15))]

/-- The registers of a loop round of pass `late` (from register `r` on: the CTA's index plus
one, the lane's request, the tiles before the group, the group's capped end). -/
def loopRegs (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) (r a m x : Nat) :
    List (Nat × Value) :=
  [(r, .bits 32 (addi (ctaW L g) 1)), (r + 2, .bits 32 (reqOf L g d.grp)), (a, .bits 32 d.acc),
   (m, .bits 32 (min32 (addi d.grp 31) (batchOf p late))), (x, addrS p.cuQBase (reqOf L g d.grp))]

/-- The registers of a scan round, in the registers of `k`. -/
def valuesScan (p : Params) (L : Launch) (g : Nat) (d : D) : Scan → List (Nat × Value)
  | .first =>
    [(7863, addrU p.cuQBase (laneW L g)), (7217, .bits 32 d.w), (7220, .bits 32 d.tl)] ++
      partials L g d 2317 3 7221
  | .loop =>
    loopRegs p L g false d 1203 7218 7223 7865 ++
    [(280, .pred (scmpi .eq .b (laneW L g) 31)), (7219, .bits 32 d.w), (7220, .bits 32 d.tl)] ++
      lanePreds L g 286 ++ partials L g d 2338 3 7221
  | .second =>
    [(7873, addrU p.cuQBase (laneW L g)), (7229, .bits 32 d.w), (7232, .bits 32 d.tl),
     (7147, .bits 32 (paramW p.batch))] ++ lanePreds L g 311 ++ partials L g d 2410 3 7233
  | .loop2 =>
    loopRegs p L g true d 1210 7230 7235 7875 ++
    [(319, .pred (scmpi .eq .b (laneW L g) 31)), (7231, .bits 32 d.w), (7232, .bits 32 d.tl),
     (7147, .bits 32 (paramW p.batch))] ++ lanePreds L g 325 ++ partials L g d 2431 3 7233

/-- The chosen request's coordinates: the request's row base `2^30 - rows + 256 tile` and its
head (`r7226`, `r7227`), from the chosen request's tile count `nt` and the tiles before it; and
the operands of the code's two divisions. -/
structure Coords where
  row : BitVec 64
  head : BitVec 64
  n1 : BitVec 64
  d1 : BitVec 64
  n2 : BitVec 64
  d2 : BitVec 64

def coords (p : Params) (L : Launch) (g : Nat) (d : D) : Coords :=
  let heads := headsW p
  let k := paramW 800
  let r1207 := sub32 d.cur (mul32 d.tot heads)
  let r2357 := sub32 (ctaW L g) (add32 r1207 d.pv)
  let r2358 := shl d.nt 8
  let r2366 := sel (scmp .gt .s (shrs r2358 3) k) (sel (scmp .gt .s (shrs r2358 4) k)
    (sel (scmp .gt .s (shrs r2358 5) k) (sel (scmp .gt .s (shrs r2358 6) k) (i32 1) (i32 2))
      (i32 4)) (i32 8)) (i32 16)
  let r2367 := min32 r2366 heads
  let r2368 := mul32 r2367 d.nt
  let r2373 := fdiv r2357 r2368
  let r2375 := sub32 r2357 (mul32 r2373 r2368)
  let r2376 := mul32 r2373 r2367
  let r2379 := sel (scmp .gt .s (add32 r2376 r2367) heads) (sub32 heads r2376) r2367
  let r2384 := fdiv r2375 r2379
  ⟨addi (shl (add32 d.nt (not32 r2384)) 8) 1073741824,
   sub32 (add32 r2375 r2376) (mul32 r2384 r2379), r2357, r2368, r2375, r2379⟩

/-- The chosen request: the ballot's count past the group's first request. -/
abbrev chosen (d : D) : BitVec 64 := add32 (popc d.bal) d.gx

/-- The registers of the choice of a request, in the first pass. -/
def valuesSelect (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let r1207 := sub32 d.cur (mul32 d.tot (headsW p))
  [(293, .pred (scmp .le .s (mad32 (prefixD L g d) (headsW p) r1207) (ctaW L g))),
   (1207, .bits 32 r1207), (7223, .bits 32 d.gx), (7220, .bits 32 d.tl),
   (7221, .bits 32 (prefixD L g d)), (1208, .bits 32 (popc d.bal)),
   (2353, .bits 32 (addi (popc d.bal) (-1))), (7228, .bits 32 (chosen d)), (7225, .bits 32 d.pv),
   (7146, .bits 32 (paramW p.batch)), (7155, .bits 32 (paramW 800))]

/-- The registers of the output writeback. -/
def valuesWrite (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let c := coords p L g d
  let row := sub32 (add32 c.row d.c0) d.c1
  [(307, .pred (scmp .gt .s (laneW L g) (paramW p.batch))), (7147, .bits 32 (paramW p.batch)),
   (7226, .bits 32 c.row), (7227, .bits 32 c.head), (7867, addrS p.cuQBase (chosen d)),
   (2392, .bits 32 d.c0), (2393, .bits 32 d.c1), (2395, .bits 32 row), (7229, .bits 32 (i32 0)),
   (7868, .ptr 64 true (.param (param 10)) 0), (7869, .bits 64 (truncBits 64 (BitVec.ofInt 64 0))),
   (2396, .bits 32 (i32 32)), (2397, .bits 32 (i32 64)), (2398, .bits 32 (i32 96)),
   (2391, .bits 32 (addi (BitVec.ofNat 64 L.sharedBase) 216)), (2399, .bits 32 (addi row 128)),
   (2400, .bits 32 (i32 1))]

/-- The registers of the second pass's ballot. -/
def valuesSelect2 (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  [(332, .pred (scmp .le .s (mad32 (prefixD L g d) (headsW p)
      (sub32 d.cur (mul32 d.tot (headsW p)))) (ctaW L g))),
   (7232, .bits 32 d.tl), (7233, .bits 32 (prefixD L g d)), (1214, .bits 32 (popc d.bal)),
   (2447, .bits 32 (addi (popc d.bal) (-1)))]

/-- The registers at state `d`. -/
def values (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  match d.site with
  | .word k | .down k | .up k _ | .total k => valuesScan p L g d k
  | .vote false | .pre false | .tiles false => valuesSelect p L g d
  | .vote true | .pre true | .tiles true => valuesSelect2 p L g d
  | .start | .exit _ => []
  | _ => valuesWrite p L g d

/-- The value of register `r` at state `d`; `ent` gives the startup registers the warp never
reads. -/
def valueOf (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) (d : D) (r : Nat) : Value :=
  ((values p L g d).lookup r).getD (((valuesStart p L g).lookup r).getD (ent r))

abbrev facts (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) (d : D) :
    List (Nat × Value) :=
  Flow.factsFrom (Flow.live d.site.pc) (valueOf p L g ent d)

/-! ### Transitions -/

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- The loop scan of pass `late`. -/
def loopOf (late : Bool) : Scan := if late then .loop2 else .loop

/-- The end of the scan of pass `late`, with the last group's capped first request `gx` and the
tiles `cur` through it: past the batch, the warp returns; else it votes. -/
def scanExit (p : Params) (late : Bool) (d : D) (gx cur : BitVec 64) : D :=
  if scmp .ge .s gx (batchOf p late) then { d with site := .exit late }
  else { d with site := .vote late, gx := gx, cur := cur }

/-- The loop head of pass `late` with group start `grp` and tiles `acc` before it: past the
batch the scan ends (with the CTA index plus one as its tiles, so the back edge is not taken),
else the lane reads its request's offset if the request exists. -/
def loopHead (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) (grp acc : BitVec 64) :
    D :=
  if scmp .ge .s (addi grp 31) (batchOf p late) then
    scanExit p late d (min32 (addi grp 31) (batchOf p late)) (addi (ctaW L g) 1)
  else if scmp .gt .s (reqOf L g grp) (batchOf p late) then
    { d with site := .down (loopOf late), grp := grp, acc := acc, w := i32 0 }
  else { d with site := .word (loopOf late), grp := grp, acc := acc }

/-- After lane 31's prefix sum `x` of a round of scan `k`. -/
def afterTotal (p : Params) (L : Launch) (g : Nat) (k : Scan) (d : D) (x : BitVec 64) : D :=
  let d := { d with tot := x }
  match k with
  | .first | .second =>
    if scmp .gt .s (mul32 x (headsW p)) (ctaW L g) then
      scanExit p k.late d (i32 0) (mul32 x (headsW p))
    else loopHead p L g k.late d (i32 0) (mul32 x (headsW p))
  | .loop | .loop2 =>
    if scmp .le .s (mad32 x (headsW p) d.acc) (ctaW L g) then
      loopHead p L g k.late d (min32 (addi d.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.acc)
    else scanExit p k.late d (min32 (addi d.grp 31) (batchOf p k.late))
      (mad32 x (headsW p) d.acc)

/-- After the chosen request's tile count `x`: the coordinates, then the writeback if the
request exists. A division without a rule faults the thread. -/
def afterTiles (p : Params) (L : Launch) (g : Nat) (d : D) (x : BitVec 64) : Option D :=
  let d := { d with nt := x }
  if divOk (coords p L g d).n1 (coords p L g d).d1 then
    if divOk (coords p L g d).n2 (coords p L g d).d2 then
      some (if scmp .lt .s (chosen d) (paramW p.batch) then { d with site := .q0 }
        else { d with site := .exit false })
    else none
  else none

/-- The next store of stage `st`, or its commit. -/
def storeNext (st : Fin 2) : Fin 4 → Site
  | 0 => .store st 1
  | 1 => .store st 2
  | 2 => .store st 3
  | 3 => .commit st

/-- The successor after event `e`. -/
def succ (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .start =>
    some (some (if scmp .gt .s (laneW L g) (BitVec.ofNat 64 p.batch) then
      { d with site := .down .first, w := i32 0 } else { d with site := .word .first }))
  | .word k =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => { d with site := .down k, w := x }
      | .error _ => none
    | _ => none
  | .down k =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      { d with site := .up k 0, dn := x, tl := tlOf p L g k d x }
    | _ => none
  | .up k j =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      match j with
      | 0 => { d with site := .up k 1, u1 := x }
      | 1 => { d with site := .up k 2, u2 := x }
      | 2 => { d with site := .up k 3, u4 := x }
      | 3 => { d with site := .up k 4, u8 := x }
      | 4 => { d with site := .total k, u16 := x }
    | _ => none
  | .total k =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v (afterTotal p L g k d)
    | _ => none
  | .vote late =>
    match e.kind with
    | .vote _ _ b =>
      let d := { d with bal := BitVec.ofNat 64 b.toNat }
      some (some (if scmpi .eq .b d.bal 0 then { d with site := .tiles late, pv := i32 0 }
        else { d with site := .pre late }))
    | _ => none
  | .pre late =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      if late then { d with site := .tiles true }
      else { d with site := .tiles false, pv := mul32 x (headsW p) }
    | _ => none
  | .tiles late =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match v with
      | .bits 32 x => if late then some (some { d with site := .exit true })
        else (afterTiles p L g d x).map some
      | _ => some none
    | _ => none
  | .q0 =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => { d with site := .q1, c0 := x }
      | .error _ => none
    | _ => none
  | .q1 =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => { d with site := .ready 0, c1 := x }
      | .error _ => none
    | _ => none
  | .ready st =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .store st 0 } else d))
    | _ => none
  | .store st b => some (some { d with site := storeNext st b })
  | .commit 0 => some (some { d with site := .ready 1 })
  | .commit 1 => some (some { d with site := .drain 0 })
  | .drain st => some (some { d with site := .free st })
  | .free 0 => some (some { d with site := .drain 1 })
  | .free 1 =>
    some (some (if scmp .gt .s (laneW L g) (paramW p.batch) then
      { d with site := .down .second, w := i32 0 } else { d with site := .word .second }))
  | .exit _ => none

/-- The output warp as a code machine. -/
@[reducible] def code (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := ⟨.start, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  pc := (·.site.pc)
  facts := facts p L g ent
  inv := fun _ => True
  next := succ p L g


/-- The registers live at the `setmaxnreg` that the warp never reads, with their startup values:
two barrier addresses and three launch words. -/
def ent (p : Params) (L : Launch) (r : Nat) : Value :=
  if r = 1069 then b32 (L.sharedBase + 192) else if r = 6495 then b32 (L.sharedBase + 144)
  else if r = 7500 then b64 p.lseBase else if r = 7501 then b64 p.lseStride
  else if r = 7503 then b64 p.usedKBase else .pred false

/-- The output warp's machine. -/
abbrev M (p : Params) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  code p L g (ent p L)

theorem live_2769 : Flow.live 2769 = [1062, 1069, 1072, 1178, 2390, 2535, 6495, 6497, 7228,
    7290, 7500, 7501, 7502, 7503, 7506] := by
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
