-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Base
public import Kernels.TmlFa4Fwd.Proof2.Mma.Machine
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part122
public import Kernels.TmlFa4Fwd.Flow.Code.Part123
public import Kernels.TmlFa4Fwd.Flow.Code.Part124
public import Kernels.TmlFa4Fwd.Flow.Code.Part125
public import Kernels.TmlFa4Fwd.Flow.Code.Part126
public import Kernels.TmlFa4Fwd.Flow.Code.Part127
public import Kernels.TmlFa4Fwd.Flow.Code.Part128
public import Kernels.TmlFa4Fwd.Flow.Code.Part129
public import Kernels.TmlFa4Fwd.Flow.Code.Part130
public import Kernels.TmlFa4Fwd.Flow.Code.Part131
public import Kernels.TmlFa4Fwd.Flow.Code.Part132
public import Kernels.TmlFa4Fwd.Flow.Code.Part133
public import Kernels.TmlFa4Fwd.Flow.Code.Part134
public import Kernels.TmlFa4Fwd.Flow.Code.Part135
public import Kernels.TmlFa4Fwd.Flow.Code.Part136
public import Kernels.TmlFa4Fwd.Flow.Code.Part137
public import Kernels.TmlFa4Fwd.Flow.Code.Part138
public import Kernels.TmlFa4Fwd.Flow.Code.Part139
public import Kernels.TmlFa4Fwd.Flow.Code.Part140
public import Kernels.TmlFa4Fwd.Flow.Code.Part141
public import Kernels.TmlFa4Fwd.Flow.Code.Part142
public import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

/-! # The correction warps as a site machine

Warps 8 to 11 (128 threads, one accumulator row each) run from their `setmaxnreg` (pc 7746) to
the `ret`. A lane meets the MMA and softmax warps at named barrier 2 (`bar1`), frees the two
statistics slots (`arr`), and picks its CTA's tile by the persistent scheduler's first pass,
exactly as the output warp (`word` … `tiles`, the same arithmetic on other registers, recorded in
an `Epilogue.D`). With a tile it reads the request's offsets and used-K length (`q0`, `q1`,
`uk`), meets its softmax warp at its two named barriers (`nb`, with the arrival `free` between),
and runs one rescale round per K/V block after the first (`r…`): per stage, a named barrier, the
stage's scale from the statistics word, a ballot whether some row needs rescaling, and then eight
Tensor Memory loads of 16 accumulator columns, each multiplied by the scale and stored back
(`rld`, `rldw`, `rst`), a store wait and two arrivals. The final stage (`f…`) reads each stage's
row sum and maximum, waits for the last PV MMA, and normalizes the accumulator: sixteen loads of
8 columns (`fld`, `fwl`), multiplied by the reciprocal row sum and stored to shared memory in two
four-word stores each (`fst`), a proxy fence and two arrivals. The LSE stores (`lse`) and the
scheduler's second pass follow; the second pass finds no further tile, and the lane waits for the
output warp (`wend`), meets the other warps at barrier 2 (`barEnd`) and returns (`exit`).

A state is a site, the recorded values, and the sub-step `k` of the instruction (`Code.sub`):
the four elements of a vector store fire at sub-steps 0 to 3, and a rescale load (a site of the
kernel's `tcLdDataflow` assumption) performs its load at sub-step 0 and its implicit wait at
sub-step 1 (`rldw`). Every successor of a state at sub-step 0 is at sub-step 0 (in both
branches of a conditional successor, `D.ite`).

The machine follows every value: a load or shuffle of a 32-bit register records the word, and a
value of another kind stops the machine (`some none`); a statistics word or a Tensor Memory
element records its real number (`.float .f32 x`), and a value of another kind stops it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (r32 i32 add32 addi sub32 mul32 mad32 min32 shrs shru
  andi scmp scmpi sel addrU addrS xor32 not32 shl popc divOk fdiv Scan laneW paramW
  batchOf skipFirst reqOf tlOf prefixD headsW lanePreds partials chosen loopOf)
open PTX.Kernels.TmlFa4Fwd.Proof2.Mma (ori ceil128 sbW sbi w32 neg32 wideS)

noncomputable section

/-! ### Values -/

/-- A real `f32` payload, and a pair of them. -/
abbrev fv (x : ℝ) : Value := .float .f32 x
abbrev fp (x y : ℝ) : Value := .pair (fv x) (fv y)

/-- The real number of an `f32` payload. -/
def fl32 (v : Value) : Option ℝ :=
  match v with
  | .float .f32 x => some x
  | _ => none

/-- The real numbers of `n` loaded elements, when each is an `f32` payload. -/
def flN (n : Nat) (vals : List Value) : Option (Nat → ℝ) :=
  if (List.range n).all fun i => (fl32 (vals.getD i (.pred false))).isSome then
    some fun i => (fl32 (vals.getD i (.pred false))).getD 0
  else none

/-! ### Sites -/

inductive Site where
  | setmax | bar1
  /-- The two statistics-slot arrivals of the start. -/
  | arr (k : Fin 2)
  | word (k : Scan)
  | down (k : Scan)
  | up (k : Scan) (j : Fin 5)
  | total (k : Scan)
  | vote (late : Bool)
  | pre (late : Bool)
  | tiles (late : Bool)
  | q0 | q1 | uk
  /-- The two named barriers with the softmax warp before the rescale rounds, and the arrival
  between them. -/
  | nb (k : Fin 2)
  | free
  /-- A rescale round's stage `st`: the named barrier, the scale, the ballot. -/
  | rbar (st : Fin 2)
  | rscale (st : Fin 2)
  | rvote (st : Fin 2)
  /-- Chunk `c` of a stage: its load (sub-step 0), its implicit wait (sub-step 1), its store. -/
  | rld (st : Fin 2) (c : Fin 8)
  | rldw (st : Fin 2) (c : Fin 8)
  | rst (st : Fin 2) (c : Fin 8)
  /-- The stage's store wait and its two arrivals. -/
  | rwait (st : Fin 2)
  | rarr (st : Fin 2) (k : Fin 2)
  /-- The final stage: the first arrival, then per stage the named barrier, the row sum and
  maximum, the arrival, the two polls. -/
  | farr0
  | fbar (st : Fin 2)
  | fsum (st : Fin 2)
  | fmax (st : Fin 2)
  | farr (st : Fin 2)
  | fw (st : Fin 2) (k : Fin 2)
  /-- Chunk `j` of the final stage: its load, its wait, its two four-word stores. -/
  | fld (st : Fin 2) (j : Fin 16)
  | fwl (st : Fin 2) (j : Fin 16)
  | fst (st : Fin 2) (j : Fin 16) (h : Fin 2)
  | fence (st : Fin 2)
  | fdone (st : Fin 2) (k : Fin 2)
  /-- The two LSE stores. -/
  | lse (h : Fin 2)
  /-- The end, after the first pass (no tile, `late = false`) or the second. -/
  | wend (late : Bool) | barEnd (late : Bool) | exit (late : Bool)
  deriving DecidableEq

/-- The program counter of rescale load `c` of stage `st`, and of its store. -/
def rldPc (st : Fin 2) (c : Fin 8) : Nat :=
  8012 + 219 * st.val + if c.val = 0 then 0 else 27 + 26 * (c.val - 1)
def rstPc (st : Fin 2) (c : Fin 8) : Nat := rldPc st c + if c.val = 0 then 26 else 25

/-- The program counter of final load `j` of stage `st`. -/
def fldPc (st : Fin 2) (j : Fin 16) : Nat :=
  296 * st.val + [8480, 8499, 8518, 8537, 8555, 8572, 8589, 8606, 8623, 8640, 8657, 8674, 8691,
    8708, 8725, 8742].getD j.val 0

/-- The distance from final store 0 of a chunk to its store 1. -/
def fstGap (j : Fin 16) : Nat := if j.val < 4 then 4 else 3

def Site.pc : Site → Nat
  | .setmax => 7746
  | .bar1 => 7747
  | .arr k => 7752 + 2 * k.val
  | .word k => match k with | .first => 7761 | .loop => 7821 | .second => 9089 | .loop2 => 9144
  | .down k => match k with | .first => 7762 | .loop => 7823 | .second => 9090 | .loop2 => 9146
  | .up k j => match k with
    | .first => 7781 + 4 * j.val | .loop => 7844 + 3 * j.val
    | .second => 9110 + 3 * j.val | .loop2 => 9167 + 3 * j.val
  | .total k => match k with | .first => 7801 | .loop => 7859 | .second => 9125 | .loop2 => 9182
  | .vote l => if l then 9194 else 7873
  | .pre l => if l then 9199 else 7880
  | .tiles l => if l then 9200 else 7884
  | .q0 => 7955
  | .q1 => 7956
  | .uk => 7959
  | .nb k => 7985 + 3 * k.val
  | .free => 7987
  | .rbar st => 8006 + 219 * st.val
  | .rscale st => 8007 + 219 * st.val
  | .rvote st => 8009 + 219 * st.val
  | .rld st c => rldPc st c
  | .rldw st c => rldPc st c
  | .rst st c => rstPc st c
  | .rwait st => 8221 + 219 * st.val
  | .rarr st k => 8223 + 219 * st.val + k.val
  | .farr0 => 8464
  | .fbar st => 8465 + 296 * st.val
  | .fsum st => 8466 + 296 * st.val
  | .fmax st => 8467 + 296 * st.val
  | .farr st => 8468 + 296 * st.val
  | .fw st k => 8473 + 296 * st.val + 3 * k.val
  | .fld st j => fldPc st j
  | .fwl st j => fldPc st j + 5
  | .fst st j h => fldPc st j + 12 + h.val * fstGap j
  | .fence st => 8758 + 296 * st.val
  | .fdone st k => 8759 + 296 * st.val + k.val
  | .lse h => 9073 + 9 * h.val
  | .wend _ => 9201
  | .barEnd _ => 9204
  | .exit _ => 9205

/-! ### States -/

/-- The values a state records. -/
structure V where
  /-- The scheduler's scan: the words its events returned and its loop state (its `site` is
  not read). -/
  sc : Epilogue.D := { site := .start }
  /-- The request's used-K length. -/
  ukw : BitVec 64 := 0
  /-- The rescale rounds' counter `%r6218` (the negated number of rounds left). -/
  trip : BitVec 64 := 0
  /-- The scales of the current rescale round, by stage, and its two ballots. -/
  s0 : ℝ := 0
  s1 : ℝ := 0
  b0 : BitVec 64 := 0
  b1 : BitVec 64 := 0
  /-- The sixteen accumulator elements of the current rescale chunk. -/
  xs : Nat → ℝ := fun _ => 0
  /-- The row sum and the row maximum of each stage, read for the final stage. -/
  rs0 : ℝ := 0
  rm0 : ℝ := 0
  rs1 : ℝ := 0
  rm1 : ℝ := 0
  /-- The eight accumulator elements of the current final chunk. -/
  ys : Nat → ℝ := fun _ => 0

/-- A state: the site, the recorded values and the sub-step. -/
structure D where
  site : Site
  v : V
  k : Fin 4 := 0

/-- A state at sub-step 0. -/
abbrev D.mk' (s : Site) (v : V) : D := ⟨s, v, 0⟩

/-- A conditional successor (both branches at sub-step 0). -/
abbrev D.ite (c : Bool) (a b : D) : D := if c = true then a else b

/-- The scale of rescale stage `st`, and its ballot. -/
def sOf (v : V) : Fin 2 → ℝ | 0 => v.s0 | 1 => v.s1
def bOf (v : V) : Fin 2 → BitVec 64 | 0 => v.b0 | 1 => v.b1

/-- The row sum of final stage `st`. -/
def rsOf (v : V) : Fin 2 → ℝ | 0 => v.rs0 | 1 => v.rs1

/-- Record stage `st`'s scale, ballot, row sum, row maximum. -/
def setS (v : V) (x : ℝ) : Fin 2 → V | 0 => { v with s0 := x } | 1 => { v with s1 := x }
def setB (v : V) (x : BitVec 64) : Fin 2 → V | 0 => { v with b0 := x } | 1 => { v with b1 := x }
def setRs (v : V) (x : ℝ) : Fin 2 → V | 0 => { v with rs0 := x } | 1 => { v with rs1 := x }
def setRm (v : V) (x : ℝ) : Fin 2 → V | 0 => { v with rm0 := x } | 1 => { v with rm1 := x }

/-! ### Register values -/

/-- The thread index as `%tid.x` reads it, and the row of the thread (`tid & 127`). -/
abbrev tidW (L : Launch) (g : Nat) : BitVec 64 :=
  truncBits 32 (BitVec.ofNat 64 ((L.tidOf g).get .x))
abbrev rowW (L : Launch) (g : Nat) : BitVec 64 := andi (tidW L g) 127

/-- The warp index within the four correction warps' named barriers: `%r565`, `%r566`. -/
abbrev nb0W (L : Launch) (g : Nat) : BitVec 64 :=
  addi (andi (BitVec.ofNat 64 (g % L.block / 32)) 3) 3
abbrev nb1W (L : Launch) (g : Nat) : BitVec 64 :=
  addi (andi (BitVec.ofNat 64 (g % L.block / 32)) 3) 7

/-- The parameters the role loads, by their names in the code. -/
def ps (p : Params) : List (String × Nat) :=
  ("kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
      ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
      ptrbf16gmemalign16o1i64div8_0_param_12", p.scaleLog2Bits) :: Epilogue.ps p

/-- The CTA index as `%ctaid.x` reads it, under the launch with the role's parameters explicit
(the launch the role's segments run on, `Base.params`). -/
abbrev ctaR (p : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  truncBits 32 (BitVec.ofNat 64 (((explicitParams L (ps p)).ctaidOf
    (g / (explicitParams L (ps p)).block)).get .x))

/-- The registers of the row: `%r567` (the thread's statistics word), `%r569` and `%r573` (the
row's Tensor Memory address in the two accumulators), `%r570`, `%r571` (its output staging
rows). -/
abbrev statW (L : Launch) (g : Nat) : BitVec 64 := add32 (sbW L) (shl (rowW L g) 2)
abbrev quarter (L : Launch) (g : Nat) : BitVec 64 := shru (rowW L g) 5
abbrev tm0 (L : Launch) (g : Nat) : BitVec 64 := ori (shl (quarter L g) 21) 256
abbrev tm1 (L : Launch) (g : Nat) : BitVec 64 := ori (shl (quarter L g) 21) 384
abbrev stg0 (L : Launch) (g : Nat) : BitVec 64 :=
  add32 (sbW L) (r32 (shl (quarter L g) 12) ||| r32 (andi (shl (tidW L g) 7) 3968))
abbrev stg1 (L : Launch) (g : Nat) : BitVec 64 := addi (stg0 L g) 3072

/-- The chosen request's coordinates as the correction warps compute them: the output warp's
`Epilogue.coords` on the CTA index the role reads itself (`%r558`). -/
def coords (p : Params) (L : Launch) (g : Nat) (d : Epilogue.D) : Epilogue.Coords :=
  let heads := headsW p
  let k := paramW 800
  let r1207 := sub32 d.cur (mul32 d.tot heads)
  let r2357 := sub32 (ctaR p L g) (add32 r1207 d.pv)
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

/-- The registers of a loop round of pass `late` (the output warp's `loopRegs` on the role's
CTA index). -/
def loopRegsR (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : Epilogue.D) (r a m x : Nat) :
    List (Nat × Value) :=
  [(r, .bits 32 (addi (ctaR p L g) 1)), (r + 2, .bits 32 (reqOf L g d.grp)), (a, .bits 32 d.acc),
   (m, .bits 32 (min32 (addi d.grp 31) (batchOf p late))), (x, addrS p.cuQBase (reqOf L g d.grp))]

/-- The chosen request's row offset `%r6216` (the output warp's coordinates without the shift
and offset) and its head (`%r4888`). -/
def rowOff (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : BitVec 64 :=
  let co := coords p L g c
  add32 c.nt (not32 (fdiv co.n2 co.d2))

/-- The 64-bit head (`cvt.s64.s32 %rd2317`). -/
abbrev headW (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : BitVec 64 :=
  truncBits 64 (cvtIntBits false .s 64 .s 32 (truncBits 32 (coords p L g c).head))

/-- The number of K/V blocks of the tile (`%r576`). -/
def blocks (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  min32 (ceil128 v.ukw)
    (ceil128 (addi (sub32 (add32 (shl (rowOff p L g v.sc) 8) v.ukw) (sub32 v.sc.c1 v.sc.c0)) 256))

/-- The registers of the launch the role keeps throughout. -/
def valuesStart (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1062, b32 (g % L.block / 32)), (1069, b32 (L.sharedBase + 192)),
   (2390, b32 (L.sharedBase + 208)), (2535, b32 L.sharedBase),
   (6495, b32 (L.sharedBase + 144)), (6497, b32 (L.sharedBase + 224)), (7500, b64 p.lseBase),
   (7501, b64 p.lseStride), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
   (7506, b64 p.cuQBase)]

/-- The registers of the row and of the scheduler that keep one value wherever they are live. -/
def valuesRole (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1612, .bits 32 (tidW L g)), (1613, .bits 32 (rowW L g)), (1614, sbi L 96),
   (1615, sbi L 104), (1616, .bits 32 (laneW L g)), (685, .pred (skipFirst p L g)),
   (1618, .bits 32 (ctaR p L g)), (7142, .bits 32 (headsW p)), (7143, .bits 32 (headsW p)),
   (7153, .bits 32 (paramW p.batch)), (7131, sbi L 232)]

/-- The registers of a scan round. -/
def valuesScan (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : Scan → List (Nat × Value)
  | .first =>
    [(8988, addrU p.cuQBase (laneW L g)), (7267, .bits 32 c.w), (7270, .bits 32 c.tl),
     (7277, b32 p.batch), (5868, w32 (i32 1))] ++ partials L g c 5878 3 7271
  | .loop =>
    loopRegsR p L g false c 1619 7268 7273 8990 ++
    [(697, .pred (scmpi .eq .b (laneW L g) 31)), (7269, .bits 32 c.w), (7270, .bits 32 c.tl),
     (7277, b32 p.batch)] ++ lanePreds L g 703 ++ partials L g c 5899 3 7271
  | .second =>
    [(9531, addrU p.cuQBase (laneW L g)), (7279, .bits 32 c.w), (7282, .bits 32 c.tl)] ++
      lanePreds L g 748 ++ partials L g c 7091 3 7283
  | .loop2 =>
    loopRegsR p L g true c 1658 7280 7285 9533 ++
    [(756, .pred (scmpi .eq .b (laneW L g) 31)), (7281, .bits 32 c.w), (7282, .bits 32 c.tl)] ++
      lanePreds L g 762 ++ partials L g c 7112 3 7283

/-- The registers of the choice of a request, in the first pass. -/
def valuesSelect (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  let r126 := sub32 c.cur (mul32 c.tot (headsW p))
  [(710, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p) r126) (ctaR p L g))),
   (1623, .bits 32 r126), (7273, .bits 32 c.gx), (7270, .bits 32 c.tl),
   (7271, .bits 32 (prefixD L g c)), (1624, .bits 32 (popc c.bal)),
   (5914, .bits 32 (addi (popc c.bal) (-1))), (7277, .bits 32 (chosen c)),
   (7275, .bits 32 c.pv), (7152, .bits 32 (paramW p.batch)), (7158, .bits 32 (paramW 800))]

/-- The registers of the second pass's ballot. -/
def valuesSelect2 (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  [(769, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p)
      (sub32 c.cur (mul32 c.tot (headsW p)))) (ctaR p L g))),
   (7282, .bits 32 c.tl), (7283, .bits 32 (prefixD L g c)), (1662, .bits 32 (popc c.bal)),
   (7128, .bits 32 (addi (popc c.bal) (-1))), (7287, w32 (i32 0))]

/-- The registers of the tile, from its choice to the end of the final stage: the named
barriers, the row's addresses, the request and the counts. -/
def valuesTile (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let c := v.sc
  [(1625, .bits 32 (nb0W L g)), (1626, .bits 32 (nb1W L g)), (1627, .bits 32 (statW L g)),
   (1628, sbi L 200), (1629, .bits 32 (tm0 L g)), (1630, .bits 32 (stg0 L g)),
   (1631, .bits 32 (stg1 L g)), (1632, .bits 32 (andi (tidW L g) 1)),
   (1633, .bits 32 (tm1 L g)), (7276, .bits 32 (rowOff p L g c)), (7277, .bits 32 (chosen c)),
   (8991, wideS (chosen c)), (8992, addrS p.cuQBase (chosen c)),
   (8993, addrS p.usedKBase (chosen c)), (9605, .bits 64 (headW p L g c)),
   (1634, .bits 32 c.c0), (1635, .bits 32 (sub32 c.c1 c.c0)),
   (1636, .bits 32 (blocks p L g v)), (5967, .bits 32 (shl (rowOff p L g c) 8)),
   (5978, w32 (i32 1)), (7287, w32 (i32 1))]

/-- The rescale rounds' registers: the chunk addresses (`%r577` … `%r590`), the counter. -/
def valuesRound (v : V) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1637, .bits 32 (addi (tm0 L g) 16)), (1638, .bits 32 (addi (tm0 L g) 32)),
   (1639, .bits 32 (addi (tm0 L g) 48)), (1640, .bits 32 (addi (tm0 L g) 64)),
   (1641, .bits 32 (addi (tm0 L g) 80)), (1642, .bits 32 (addi (tm0 L g) 96)),
   (1643, .bits 32 (addi (tm0 L g) 112)), (1644, .bits 32 (addi (tm0 L g) 144)),
   (1645, .bits 32 (addi (tm0 L g) 160)), (1646, .bits 32 (addi (tm0 L g) 176)),
   (1647, .bits 32 (addi (tm0 L g) 192)), (1648, .bits 32 (addi (tm0 L g) 208)),
   (1649, .bits 32 (addi (tm0 L g) 224)), (1650, .bits 32 (addi (tm0 L g) 240)),
   (7278, w32 v.trip), (6236, w32 (i32 1)), (6494, w32 (i32 1))]

/-- The first data register of rescale chunk `c` of stage `st` (its 16 loaded elements, then
its 16 products). -/
def rBase (st : Fin 2) (c : Fin 8) : Nat := 5980 + 258 * st.val + 32 * c.val

/-- The stage's scale register (`%r591`, `%r592`) and the pair of it (`%rd1715`, `%rd1846`). -/
def rScaleReg (st : Fin 2) : Nat := 1651 + st.val
def rPairReg (st : Fin 2) : Nat := 9003 + 131 * st.val

/-- The loaded elements of a rescale chunk. -/
def rLoaded (st : Fin 2) (c : Fin 8) (xs : Nat → ℝ) : List (Nat × Value) :=
  (List.range 16).map fun i => (rBase st c + i, fv (xs i))

/-- The products of a rescale chunk, in the registers its store reads: register
`rBase + 16 + 2 i` holds element `14 - 2 i` times the scale and the next register element
`15 - 2 i`. -/
def rProducts (st : Fin 2) (c : Fin 8) (xs : Nat → ℝ) (s : ℝ) : List (Nat × Value) :=
  (List.range 8).flatMap fun i =>
    [(rBase st c + 16 + 2 * i, fv (xs (14 - 2 * i) * s)),
     (rBase st c + 17 + 2 * i, fv (xs (15 - 2 * i) * s))]

/-- The registers of a rescale stage at its sites. -/
def valuesRescale (st : Fin 2) (v : V) : List (Nat × Value) :=
  [(rScaleReg st, fv (sOf v st)), (rPairReg st, fp (sOf v st) (sOf v st)),
   (731 + 2 * st.val,
    .pred (Assumption.erealCompare .lt (sOf v st : EReal) (1 : ℝ)))]

/-- The final stage's registers: the reciprocal row sum and its pair, the output staging
addresses (`%r5440` … `%r5451`, then per chunk), the parities. -/
def fRecip (x : ℝ) : ℝ := if x ≠ 0 then x⁻¹ else 1

/-- A word of final stage `st`. -/
def fStage : Fin 2 → BitVec 64 → BitVec 64 → BitVec 64 | 0, a, _ => a | 1, _, b => b

/-- The final stage's shared registers. -/
def valuesFinal (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let a0 := addi (stg0 L g) 68608
  let sw (x : BitVec 64) : BitVec 64 := xor32 (andi (shru x 3) 112) x
  [(7134, .bits 32 (paramW p.scaleLog2Bits)),
   (6500, .bits 32 (sel (scmpi .eq .b (andi (tidW L g) 1) 0) (i32 16) (i32 (-16)))),
   (6502, .bits 32 (sel (scmpi .eq .b (andi (tidW L g) 2) 0) (i32 32) (i32 (-32)))),
   (6504, .bits 32 (sel (scmpi .eq .b (andi (tidW L g) 4) 0) (i32 64) (i32 (-64)))),
   (6508, .bits 32 (sw a0)), (6511, .bits 32 (sw (stg1 L g))),
   (6498, w32 (i32 1)), (6496, w32 (i32 0)), (6499, sbi L 152),
   (6512, fv v.rs0), (6513, fv v.rm0), (1653, fv v.rs1), (1654, fv v.rm1),
   (6515, fv (fRecip v.rs0)), (9259, fp (fRecip v.rs0) (fRecip v.rs0)),
   (6795, fv (fRecip v.rs1)), (9391, fp (fRecip v.rs1) (fRecip v.rs1)),
   (739, .pred (Assumption.erealCompare .ne (v.rs0 : EReal) (0 : ℝ))),
   (740, .pred (Assumption.erealCompare .ne (v.rs1 : EReal) (0 : ℝ)))]

/-- The first loaded register of final chunk `j` of stage `st`. -/
def fBaseN (st : Fin 2) (j : Nat) : Nat :=
  280 * st.val + [6516, 6535, 6554, 6573, 6591, 6608, 6625, 6642, 6659, 6676, 6693, 6710, 6727,
    6744, 6761, 6778].getD j 0
abbrev fBase (st : Fin 2) (j : Fin 16) : Nat := fBaseN st j.val

/-- The first pack register of final chunk `j` (four packs, then four products). -/
def fPack (st : Fin 2) (j : Fin 16) : Nat := 9260 + 132 * st.val + 8 * j.val

/-- The data registers of final chunk `j`: the eight elements, their four packs (high
elements first), the four products by the reciprocal `r` (low elements first), and the eight
unpacked products in the registers the two stores read. -/
def fChunk (st : Fin 2) (j : Fin 16) (ys : Nat → ℝ) (r : ℝ) : List (Nat × Value) :=
  let b := fBase st j
  let q := fPack st j
  let u := if j.val < 4 then b + 13 else b + 12
  (List.range 8).map (fun i => (b + i, fv (ys i))) ++
  [(q, fp (ys 6) (ys 7)), (q + 1, fp (ys 4) (ys 5)), (q + 2, fp (ys 2) (ys 3)),
   (q + 3, fp (ys 0) (ys 1)),
   (q + 4, fp (ys 0 * r) (ys 1 * r)), (q + 5, fp (ys 2 * r) (ys 3 * r)),
   (q + 6, fp (ys 4 * r) (ys 5 * r)), (q + 7, fp (ys 6 * r) (ys 7 * r)),
   (b + 8, fv (ys 2 * r)), (b + 9, fv (ys 3 * r)), (b + 10, fv (ys 0 * r)),
   (b + 11, fv (ys 1 * r)),
   (u, fv (ys 6 * r)), (u + 1, fv (ys 7 * r)), (u + 2, fv (ys 4 * r)), (u + 3, fv (ys 5 * r))]

/-- The output staging address registers of a final stage: the four store-0 bases
`a`, `a + d2`, `a + d4`, `a + d4 + d2` and the store-1 bases (each plus `d1`), and the load
address registers `tm0 + 128 st + 8 j` (`j ≥ 1`). -/
def fAddrs (L : Launch) (g : Nat) (st : Fin 2) : List (Nat × Value) :=
  let a := fStage st (xor32 (andi (shru (stg1 L g) 3) 112) (stg1 L g))
    (xor32 (andi (shru (addi (stg0 L g) 68608) 3) 112) (addi (stg0 L g) 68608))
  let tm (j : Nat) : BitVec 64 :=
    fStage st (addi (tm0 L g) (8 * j)) (addi (tm0 L g) (128 + 8 * j))
  let d1 := sel (scmpi .eq .b (andi (tidW L g) 1) 0) (i32 16) (i32 (-16))
  let d2 := sel (scmpi .eq .b (andi (tidW L g) 2) 0) (i32 32) (i32 (-32))
  let d4 := sel (scmpi .eq .b (andi (tidW L g) 4) 0) (i32 64) (i32 (-64))
  let a1 := add32 a d2
  let a2 := add32 a d4
  let a3 := add32 a2 d2
  [(fBase st 0 + 12, .bits 32 (add32 a d1)), (fBase st 1 - 2, .bits 32 (tm 1)),
   (fBase st 1 - 1, .bits 32 a1), (fBase st 1 + 12, .bits 32 (add32 a1 d1)),
   (fBase st 2 - 2, .bits 32 (tm 2)), (fBase st 2 - 1, .bits 32 a2),
   (fBase st 2 + 12, .bits 32 (add32 a2 d1)), (fBase st 3 - 2, .bits 32 (tm 3)),
   (fBase st 3 - 1, .bits 32 a3), (fBase st 3 + 12, .bits 32 (add32 a3 d1))] ++
  (List.range 12).map fun i => (fBaseN st (i + 4) - 1, .bits 32 (tm (i + 4)))

/-- The real number of the softmax scale (`param_12`, an `f32` pattern of a finite number by
`Pre.scales`). -/
def scaleR (p : Params) : ℝ := ((f32Value p.scaleLog2Bits).getD 0 : ℚ)

/-- The real number of the `f32` constant `0f3F317218` (the code's `ln 2`), as the constant's
rule reads it. -/
abbrev ln2F : ℝ := 1453635 / 2097152

/-- The LSE of a row from its sum and maximum: `(scale · max + log₂ sum) · ln 2`. -/
abbrev lseOf (p : Params) (rs rm : ℝ) : ℝ := (scaleR p * rm + Real.logb 2 rs) * ln2F

/-- The LSE store address of the row (`%rd203`): the LSE base plus four times the row's index
`head · stride + q0 + (q-offset | row)`. -/
def lseAddr (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
      (truncBits 64
        (truncBits 64
            (truncBits 64
              (truncBits 64 (BitVec.ofNat 64 p.lseBase) +
                truncBits 64
                  (if 2 ≥ 64 then 0
                  else
                    truncBits 64
                      (truncBits 64
                          (truncBits 64
                            (truncBits 64 (headW p L g v.sc) *
                                truncBits 64 (BitVec.ofNat 64 p.lseStride) +
                              truncBits 64
                                (truncBits 64
                                  (cvtIntBits false IType.s 64 IType.s 32
                                    (truncBits 32 v.sc.c0))))) <<<
                        2)))) +
          truncBits 64
            (if 2 ≥ 64 then 0
            else
              truncBits 64
                (truncBits 64
                    (truncBits 64
                        (truncBits 64
                          (cvtIntBits false IType.s 64 IType.s 32
                            (truncBits 32
                              (Epilogue.shl (rowOff p L g v.sc) 8)))) |||
                      truncBits 64 (truncBits 64 (truncBits 32 (rowW L g)))) <<<
                  2))))

/-- An LSE register: the LSE when the row sum is not zero, else `-inf` (the code's `selp` on the
row sum's comparison with 0, `%p737`, `%p740`). -/
abbrev lseSel (p : Params) (rs rm : ℝ) : Value :=
  if Assumption.erealCompare .ne (rs : EReal) (0 : ℝ) = true then fv (lseOf p rs rm)
  else .bits 32 (BitVec.ofNat 64 4286578688)

/-- The LSE's registers: the store address, the two values (`%rd203`, `%r595`, `%r596`) and the
row limit `%r6017`. -/
def valuesLse (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  [(7491, .bits 64 (lseAddr p L g v)), (1655, lseSel p v.rs0 v.rm0),
   (7077, .bits 32 (sub32 (sub32 v.sc.c1 v.sc.c0) (shl (rowOff p L g v.sc) 8))),
   (1656, lseSel p v.rs1 v.rm1)]

/-- The registers at state `d`. -/
def values (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let v := d.v
  match d.site with
  | .setmax | .bar1 | .arr _ => [(7277, b32 p.batch), (5868, w32 (i32 1))]
  | .word k | .down k | .up k _ | .total k => valuesScan p L g v.sc k
  | .vote false | .pre false | .tiles false => valuesSelect p L g v.sc
  | .vote true | .pre true | .tiles true => valuesSelect2 p L g v.sc
  | .q0 | .q1 | .uk | .nb _ | .free => valuesTile p L g v
  | .rbar st | .rscale st | .rvote st | .rwait st | .rarr st _ =>
    valuesRescale st v ++ valuesRound v L g ++ valuesTile p L g v
  | .rld st c | .rldw st c | .rst st c =>
    rLoaded st c v.xs ++ rProducts st c v.xs (sOf v st) ++ valuesRescale st v ++
      valuesRound v L g ++ valuesTile p L g v
  | .farr0 | .fbar _ | .fsum _ | .fmax _ | .farr _ | .fw _ _ | .fence _ | .fdone _ _ =>
    valuesFinal p L g v ++ fAddrs L g 0 ++ fAddrs L g 1 ++ valuesTile p L g v
  | .fld st j | .fwl st j | .fst st j _ =>
    fChunk st j v.ys (fRecip (rsOf v st)) ++ valuesFinal p L g v ++ fAddrs L g st ++
      valuesTile p L g v
  | .lse _ => valuesLse p L g v ++ valuesFinal p L g v ++ valuesTile p L g v
  | .wend false | .barEnd false | .exit false => [(7287, w32 (i32 1))]
  | .wend true | .barEnd true | .exit true => [(7287, w32 (i32 0))]

/-- The value of register `r` at state `d`. -/
def valueOf (p : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values p L g d).lookup r).getD (((valuesRole p L g).lookup r).getD
    (((valuesStart p L g).lookup r).getD (.pred false)))

/-- The registers live at a state: at the implicit wait of a rescale load, those after the
load. -/
def livePc (d : D) : Nat :=
  match d.site with
  | .rldw _ _ => d.site.pc + 1
  | _ => d.site.pc

abbrev facts (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live (livePc d)) (valueOf p L g d)

/-! ### Transitions -/

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- Follow a real `f32` payload. -/
def real32 (v : Value) (f : ℝ → D) : Option (Option D) :=
  match v with
  | .float .f32 x => some (some (f x))
  | _ => some none

/-- A state at site `s` with the scan state changed by `f`. -/
abbrev scAt (d : D) (s : Site) (f : Epilogue.D → Epilogue.D) : D :=
  D.mk' s { d.v with sc := f d.v.sc }

/-- The end of the scan of pass `late`, with the last group's capped first request `gx` and the
tiles `cur` through it: past the batch, no tile (the final poll); else the ballot. -/
def scanExit (p : Params) (late : Bool) (d : D) (gx cur : BitVec 64) : D :=
  D.ite (scmp .ge .s gx (batchOf p late)) (D.mk' (.wend late) d.v)
    (scAt d (.vote late) fun c => { c with gx := gx, cur := cur })

/-- The loop head of pass `late` with group start `grp` and tiles `acc` before it. -/
def loopHead (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) (grp acc : BitVec 64) :
    D :=
  D.ite (scmp .ge .s (addi grp 31) (batchOf p late))
    (scanExit p late d (min32 (addi grp 31) (batchOf p late)) (addi (ctaR p L g) 1))
    (D.ite (scmp .gt .s (reqOf L g grp) (batchOf p late))
      (scAt d (.down (loopOf late)) fun c => { c with grp := grp, acc := acc, w := i32 0 })
      (scAt d (.word (loopOf late)) fun c => { c with grp := grp, acc := acc }))

/-- After lane 31's prefix sum `x` of a round of scan `k`. -/
def afterTotal (p : Params) (L : Launch) (g : Nat) (k : Scan) (d : D) (x : BitVec 64) : D :=
  let d := scAt d d.site fun c => { c with tot := x }
  match k with
  | .first | .second =>
    D.ite (scmp .gt .s (mul32 x (headsW p)) (ctaR p L g))
      (scanExit p k.late d (i32 0) (mul32 x (headsW p)))
      (loopHead p L g k.late d (i32 0) (mul32 x (headsW p)))
  | .loop | .loop2 =>
    D.ite (scmp .le .s (mad32 x (headsW p) d.v.sc.acc) (ctaR p L g))
      (loopHead p L g k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.v.sc.acc))
      (scanExit p k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.v.sc.acc))

/-- After the chosen request's tile count `x`: the coordinates, then the request's reads if
the request exists. A division without a rule faults the thread. -/
def afterTiles (p : Params) (L : Launch) (g : Nat) (d : D) (x : BitVec 64) : Option D :=
  let d := scAt d d.site fun c => { c with nt := x }
  let co := coords p L g d.v.sc
  if divOk co.n1 co.d1 then
    if divOk co.n2 co.d2 then
      some (D.ite (scmp .lt .s (chosen d.v.sc) (paramW p.batch)) (D.mk' .q0 d.v)
        (D.mk' (.wend false) d.v))
    else none
  else none

/-- The start of a scheduler pass: lanes past the batch skip their read. -/
def passStart (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) : D :=
  let k : Scan := if late then .second else .first
  D.ite (scmp .gt .s (laneW L g) (if late then paramW p.batch else BitVec.ofNat 64 p.batch))
    (scAt d (.down k) fun c => { c with w := i32 0 }) (D.mk' (.word k) d.v)

/-- The rescale rounds on entry: none when the tile has fewer than two blocks. -/
def enterRounds (p : Params) (L : Launch) (g : Nat) (d : D) : D :=
  D.ite (scmpi .lt .s (blocks p L g d.v) 2) (D.mk' .farr0 d.v)
    (D.mk' (.rbar 0) { d.v with trip := neg32 (blocks p L g d.v) })

/-- The end of a rescale round: another round or the final stage. -/
def roundEnd (d : D) : D :=
  let v := { d.v with trip := addi d.v.trip 1 }
  D.ite (scmpi .ne .b (addi d.v.trip 1) (-1)) (D.mk' (.rbar 0) v) (D.mk' .farr0 v)

/-- The site after the ballot of rescale stage `st`: the stage's first chunk, or its arrivals
when no row of the warp needs rescaling. -/
def afterVote (st : Fin 2) (d : D) (b : BitVec 64) : D :=
  let v := setB d.v b st
  D.ite (scmpi .eq .b b 0) (D.mk' (.rarr st 0) v) (D.mk' (.rld st 0) v)

/-- After the last arrival of the final stage: the LSE stores of the rows the request has
(`%p739`, `%p741`), then the second pass. -/
def afterFinal (p : Params) (L : Launch) (g : Nat) (d : D) : D :=
  let lim := sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (rowOff p L g d.v.sc) 8)
  D.ite (scmp .ge .s (rowW L g) lim)
    (D.ite (scmp .ge .s (rowW L g) (addi lim (-128))) (passStart p L g true d)
      (D.mk' (.lse 1) d.v))
    (D.mk' (.lse 0) d.v)

/-- After LSE store `h`. -/
def afterLse (p : Params) (L : Launch) (g : Nat) (d : D) : Fin 2 → D
  | 0 =>
    let lim := sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (rowOff p L g d.v.sc) 8)
    D.ite (scmp .ge .s (rowW L g) (addi lim (-128))) (passStart p L g true d) (D.mk' (.lse 1) d.v)
  | 1 => passStart p L g true d

/-- The successor after event `e` (at sub-step 0 unless stated). -/
def succ (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  let go (s : Site) : Option (Option D) := some (some (D.mk' s d.v))
  match d.site with
  | .setmax => go .bar1
  | .bar1 => go (.arr 0)
  | .arr 0 => go (.arr 1)
  | .arr 1 => some (some (passStart p L g false d))
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
      some (some (D.ite (scmpi .eq .b d.v.sc.bal 0)
        (scAt d (.tiles late) fun c => { c with pv := i32 0 }) (D.mk' (.pre late) d.v)))
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
        if late then some (some (scAt d (.wend true) fun c => c))
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
      | .ok v => word32 v fun x => D.mk' (.nb 0) { d.v with ukw := x }
      | .error _ => none
    | _ => none
  | .nb 0 => go .free
  | .free => go (.nb 1)
  | .nb 1 => some (some (enterRounds p L g d))
  | .rbar st => go (.rscale st)
  | .rscale st =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => real32 v fun x =>
        D.mk' (.rvote st) (setS d.v x st)
      | .error _ => none
    | _ => none
  | .rvote st =>
    match e.kind with
    | .vote _ _ b => some (some (afterVote st d (BitVec.ofNat 64 b.toNat)))
    | _ => none
  | .rld st c =>
    if d.k = 0 then
      match e.kind with
      | .tc (.ld _ vals _) => match flN 16 vals with
        | some xs => some (some ⟨.rldw st c, { d.v with xs := xs }, 1⟩)
        | none => some none
      | _ => none
    else some none
  | .rldw st c => if d.k = 1 then go (.rst st c) else some none
  | .rst st c => if c.val = 7 then go (.rwait st) else go (.rld st (c + 1))
  | .rwait st => go (.rarr st 0)
  | .rarr st 0 => go (.rarr st 1)
  | .rarr 0 1 => go (.rbar 1)
  | .rarr 1 1 => some (some (roundEnd d))
  | .farr0 => go (.fbar 0)
  | .fbar st => go (.fsum st)
  | .fsum st =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => real32 v fun x =>
        D.mk' (.fmax st) (setRs d.v x st)
      | .error _ => none
    | _ => none
  | .fmax st =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => real32 v fun x =>
        D.mk' (.farr st) (setRm d.v x st)
      | .error _ => none
    | _ => none
  | .farr st => go (.fw st 0)
  | .fw st k =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      some (some (if ok then D.mk' (if k.val = 0 then .fw st 1 else .fld st 0) d.v else d))
    | _ => none
  | .fld st j =>
    match e.kind with
    | .tc (.ld _ vals _) => match flN 8 vals with
      | some ys => some (some (D.mk' (.fwl st j) { d.v with ys := ys }))
      | none => some none
    | _ => none
  | .fwl st j => go (.fst st j 0)
  | .fst st j h =>
    if d.k.val < 3 then some (some { d with k := d.k + 1 })
    else if h.val = 0 then go (.fst st j 1)
    else if j.val = 15 then go (.fence st) else go (.fld st (j + 1))
  | .fence st => go (.fdone st 0)
  | .fdone st 0 => go (.fdone st 1)
  | .fdone 0 1 => go (.fbar 1)
  | .fdone 1 1 =>
    -- the LSE's logarithms: the kernel's rule on positive row sums, Core's `lg2(+0) = -inf` on
    -- zero ones (the code's `selp` then stores `-inf`); a negative sum is not followed
    if 0 ≤ d.v.rs0 ∧ 0 ≤ d.v.rs1 then some (some (afterFinal p L g d)) else some none
  | .lse 0 => if 0 ≤ d.v.rs1 then some (some (afterLse p L g d 0)) else some none
  | .lse 1 => some (some (afterLse p L g d 1))
  | .wend late =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then D.mk' (.barEnd late) d.v else d))
    | _ => none
  | .barEnd late => go (.exit late)
  | .exit _ => none

/-- The midway sub-steps a state may have: the elements of a vector store and the implicit wait
of a rescale load. -/
def Site.midOk : Site → Fin 4 → Prop
  | .fst _ _ _, _ => True
  | .rldw _ _, k => k = 1
  | _, _ => False

/-- The correction warps as a code machine. -/
@[reducible] def code (p : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := D.mk' .setmax {}
  pc := (·.site.pc)
  facts := facts p L g
  sub := (·.k.val)
  inv := fun d => d.k = 0 ∨ d.site.midOk d.k
  next := succ p L g

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
