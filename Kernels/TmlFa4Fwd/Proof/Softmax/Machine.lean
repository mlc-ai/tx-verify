-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
public import Kernels.TmlFa4Fwd.Proof.Lib.SchedWords
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.Expo1
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoP
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.Rsum1
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.RsumP
public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasExpoVals
public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasFold
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.RsumB
public import Kernels.TmlFa4Fwd.Proof.Softmax.Live
public import Kernels.TmlFa4Fwd.Proof.Softmax.MaskSeg
public import Kernels.TmlFa4Fwd.Proof.Softmax.PlainFold
public import Lemmas.Flow.MaskedPack
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps as a site machine

Warps 0 to 7 (two stages of 128 rows, one row per thread) run from their `setmaxnreg` (pc 3102)
to the `ret` (pc 9205). A lane meets the MMA and correction warps at named barrier 2 (`bar1`)
and picks its CTA's tile by the persistent scheduler's first pass, the output warp's arithmetic
on other registers (`word` … `tiles`, recorded in an `Epilogue.D`). With a tile it reads the
request's offsets and used-K length (`q0`, `q1`, `uk`) and processes the tile's K/V blocks in
three kinds of rounds (`Rd`):

* `first`: the first block, with the bias and the causal mask. Two polls (`wq`, `ws`), four
  score loads from Tensor Memory (`sld`), the bias poll (`wb`) and sixteen four-word bias loads
  from shared memory (`bld`, sub-steps 0 to 3), a proxy fence, the stage's named barrier and
  one lane's arrival freeing the bias slot (`fence`, `bsync`, `barr`); then the maximum and the
  exponentials (local code), the arrival at the correction warps' named barrier (`narr`), four
  P stores to Tensor Memory with two store waits and an arrival between (`pst`, `pwst`,
  `parr`), a warp barrier, an election and the elected lane's arrival (`pws`, `pel`, `parr2`),
  and the poll for the row statistics slot (`pwend`).
* `bias`: a later block with bias (the loop at pcs 5032 to 6653): the same without `wq` and
  with the statistics store (`stat`) before the named-barrier arrival.
* `plain`: a block without bias (the loop at pcs 6661 to 7604): one poll, four score loads
  with their implicit waits (`sld`, `sldw`, sites of the kernel's `tcLdDataflow` assumption),
  the statistics store and the P part.

The first P store of a `first` and a `bias` round is a site of the kernel's `delayedTmem`
assumption: it waits for the score loads at sub-step 0 and stores at sub-step 1. After the
rounds the lane stores its row sum and maximum (`fin`), arrives at the correction warps'
barrier (`finarr`), runs the scheduler's second pass (which finds no further tile), waits for
the output warp (`wend`), meets the other warps at barrier 2 (`barEnd`) and returns (`exit`).

The machine follows every value an event returns: a 32-bit load or shuffle records the word and
stops (`some none`) on a value of another kind; a score load records the reals of its 32 elements
and stops on an element that is not an `f32` payload (`flAll`); a bias load records the halves of
its words and stops on a word that is not two `bf16` payloads or masked halves (`biasOk`), and
bytes that do not rebuild into a value fault the thread (`none`).

The state's register facts name the control registers only (`ctlLive`, `Live.lean`): the
registers the softmax code computes from scores and bias (`dataRanges`, 4650 registers found by
a closure over the role's floating instructions, conversions and moves from the loaded
registers) are not stated.
No branch, guard or non-store event of the role reads such a register, so the control flow is
stated in full. The data machine `codeD` (`Data.lean`) has the same states and successors and
also states the data registers its table names; the fragment is built on it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 add32 addi sub32 mul32 mad32 min32 shrs shru
  andi scmp scmpi sel addrU addrS xor32 not32 shl popc divOk fdiv sdiv Scan laneW ctaW paramW
  batchOf skipFirst reqOf tlOf prefixD headsW lanePreds partials chosen loopOf)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ori ceil128 sbW sbi w32 neg32 wideS)

noncomputable section

/-! ### Arithmetic of the code that the other roles do not use -/

abbrev max32 (x y : BitVec 64) : BitVec 64 := sel (scmp .gt .s x y) (r32 x) (r32 y)
abbrev maxi (x : BitVec 64) (n : Int) : BitVec 64 := max32 x (i32 n)
abbrev or32 (x y : BitVec 64) : BitVec 64 := r32 x ||| r32 y

/-- The warp index of the thread, and whether its warp is in the second stage (`%r2 > 3`). -/
abbrev warpW (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (g % L.block / 32)
abbrev stg (L : Launch) (g : Nat) : Bool := scmpi .gt .s (warpW L g) 3
/-- The thread index as `%tid.x` reads it. -/
abbrev tidW (L : Launch) (g : Nat) : BitVec 64 :=
  truncBits 32 (BitVec.ofNat 64 ((L.tidOf g).get .x))

/-- The 16-bit selection of one or zero (`selp.b16 … 1, 0, p`), as the code computes it. -/
abbrev sel16 (c : Bool) : BitVec 64 :=
  truncBits 16
    (if c = true then truncBits 16 (BitVec.ofInt 64 1) else truncBits 16 (BitVec.ofInt 64 0))

/-- The stage's barrier base: the shared base plus eight in the second stage (`%r1714`). -/
abbrev sbS (L : Launch) (g : Nat) : BitVec 64 :=
  add32 (sbW L) (BitVec.ofNat 64 ((sel16 (stg L g)).toNat * 8))
/-- A barrier address of the stage: its base plus `n`. -/
abbrev sbSi (L : Launch) (g : Nat) (n : Int) : Value := .bits 32 (addi (sbS L g) n)

/-- The stage's Tensor Memory column base of the scores (`%r1728`, `%r2162`, `%r2910`,
`%r4120`): 128 in the second stage, with the thread's lane quarter in bits 21 and 22. -/
abbrev tmS (L : Launch) (g : Nat) : BitVec 64 :=
  or32 (sel (stg L g) (i32 128) (i32 0)) (andi (shl (tidW L g) 16) 6291456)

/-- The thread's row slot in shared memory (`%r1718`): the base plus `128 · (tid mod 128)`. -/
abbrev rowSb (L : Launch) (g : Nat) : BitVec 64 := add32 (sbW L) (andi (shl (tidW L g) 7) 16256)
/-- The stage's bias offset (`%r1723`) and the swizzled bias address at offset `n`. -/
abbrev bOff (L : Launch) (g : Nat) : BitVec 64 := sel (stg L g) (i32 32768) (i32 0)
abbrev swz (x : BitVec 64) : BitVec 64 := xor32 (andi (shru x 3) 112) x
abbrev bAddr (L : Launch) (g : Nat) (n : Int) : BitVec 64 :=
  swz (addi (add32 (rowSb L g) (bOff L g)) n)

/-- The offsets of the fifteen bias addresses after the first (the first is
`swz (rowSb + 166912) + bOff`, read twice with offset 16384). -/
def bOffs : List Int :=
  [183408, 183392, 183376, 183360, 183344, 183328, 183312, 167024, 167008, 166992, 166976,
    166960, 166944, 166928]

/-- The first bias address (`%r1724`, `%r3110`). -/
abbrev bAddr0 (L : Launch) (g : Nat) : BitVec 64 :=
  add32 (swz (addi (rowSb L g) 166912)) (bOff L g)

/-- The named barrier of the thread's warp group at the correction warps (`%r4067`). -/
abbrev nbW (L : Launch) (g : Nat) : BitVec 64 :=
  addi (add32 (sub32 (warpW L g) (andi (add32 (warpW L g)
    (shru (shrs (warpW L g) 31) 30)) (-4))) (sel (stg L g) (i32 4) (i32 0))) 3

/-- The stage's statistics address (`%r3511`, `%r4458`, `%r4754`). -/
abbrev statA (L : Launch) (g : Nat) : BitVec 64 :=
  add32 (sbW L) (shl (or32 (sel (stg L g) (i32 128) (i32 0)) (andi (tidW L g) 127)) 2)

/-! ### Sites -/

/-- The three kinds of rounds. -/
inductive Rd where
  | first | bias | plain
  deriving DecidableEq

inductive Site where
  | setmax | bar1
  | word (k : Scan)
  | down (k : Scan)
  | up (k : Scan) (j : Fin 5)
  | total (k : Scan)
  | vote (late : Bool)
  | pre (late : Bool)
  | tiles (late : Bool)
  | q0 | q1 | uk
  /-- The first round's extra poll. -/
  | wq
  /-- The poll for the scores of a round. -/
  | ws (r : Rd)
  /-- The score loads of a round, and the implicit waits of a plain round's loads. -/
  | sld (r : Rd) (c : Fin 4)
  | sldw (c : Fin 4)
  /-- The bias poll, the bias loads, the fence, the named barrier and the arrival of a round
  with bias (`b = false` the first round, `b = true` a later one). -/
  | wb (b : Bool)
  | bld (b : Bool) (c : Fin 16)
  | fence (b : Bool)
  | bsync (b : Bool)
  | barr (b : Bool)
  /-- The statistics store of a later round (`pl = false` with bias, `true` plain). -/
  | stat (pl : Bool)
  /-- The arrival at the correction warps' named barrier. -/
  | narr (r : Rd)
  /-- The P stores, the store waits, the arrival between them, the warp barrier, the
  election, the elected lane's arrival and the closing poll. -/
  | pst (r : Rd) (q : Fin 4)
  | pwst (r : Rd) (k : Fin 2)
  | parr (r : Rd)
  | pws (r : Rd)
  | pel (r : Rd)
  | parr2 (r : Rd)
  | pwend (r : Rd)
  /-- The row sum and maximum stores and the final named-barrier arrival. -/
  | fin (k : Fin 2)
  | finarr
  /-- The end, after the first pass (no tile, `late = false`) or the second. -/
  | wend (late : Bool) | barEnd (late : Bool) | exit (late : Bool)
  deriving DecidableEq

/-- A program counter of round kind `r`. -/
def Rd.pc (r : Rd) (a b c : Nat) : Nat := match r with | .first => a | .bias => b | .plain => c

def Site.pc : Site → Nat
  | .setmax => 3102
  | .bar1 => 3103
  | .word k => match k with | .first => 3110 | .loop => 3169 | .second => 7621 | .loop2 => 7677
  | .down k => match k with | .first => 3111 | .loop => 3171 | .second => 7622 | .loop2 => 7679
  | .up k j => match k with
    | .first => 3130 + 4 * j.val | .loop => 3192 + 3 * j.val
    | .second => 7642 + 3 * j.val | .loop2 => 7700 + 3 * j.val
  | .total k => match k with | .first => 3150 | .loop => 3207 | .second => 7657 | .loop2 => 7715
  | .vote l => if l then 7726 else 3220
  | .pre l => if l then 7731 else 3227
  | .tiles l => if l then 7732 else 3231
  | .q0 => 3369
  | .q1 => 3370
  | .uk => 3373
  | .wq => 3420
  | .ws r => r.pc 3425 5109 6676
  | .sld r c => r.pc 3428 5112 6679 + (match r with
      | .first => [0, 18, 35, 53] | _ => [0, 17, 34, 51]).getD c.val 0
  | .sldw c => 6679 + [0, 17, 34, 51].getD c.val 0
  | .wb b => if b then 5181 else 3498
  | .bld b c => (if b then 5189 else 3501) + 5 * c.val
  | .fence b => if b then 5269 else 3581
  | .bsync b => if b then 5271 else 3583
  | .barr b => if b then 5278 else 3590
  | .stat pl => if pl then 6890 else 5682
  | .narr r => r.pc 4397 5683 6891
  | .pst r q => r.pc 4826 6508 7416 + [0, 9, 18, r.pc 30 33 30].getD q.val 0
  | .pwst r k => r.pc 4845 6527 7435 + r.pc 12 15 12 * k.val
  | .parr r => r.pc 4847 6532 7437
  | .pws r => r.pc 4858 6543 7448
  | .pel r => r.pc 4859 6544 7449
  | .parr2 r => r.pc 4867 6552 7457
  | .pwend r => r.pc 4874 6558 7463
  | .fin k => 7614 + k.val
  | .finarr => 7616
  | .wend _ => 7738
  | .barEnd _ => 7741
  | .exit _ => 9205

/-! ### States -/

/-- The values a state records. -/
structure V where
  /-- The scheduler's scan: the words its events returned and its loop state (its `site` is
  not read). -/
  sc : Epilogue.D := { site := .start }
  /-- The request's used-K length. -/
  ukw : BitVec 64 := 0
  /-- The bias rounds' counter `%r6188` (counts up to `-1`) and round index `%r6189`, the bias
  poll parity `%r6190`, the score poll parity `%r6193`, the statistics poll parity `%r6198`,
  and the plain rounds' counter `%r6194` (counts up to `0`). -/
  nb : BitVec 64 := 0
  bt : BitVec 64 := 0
  bpar : BitVec 64 := 0
  spar : BitVec 64 := 0
  ppar : BitVec 64 := 0
  pl : BitVec 64 := 0
  /-- The reals the current round's score loads returned (element `i` of load `c`), and the
  halves of its bias loads (data plane): half `i` (0 to 7; the low half of word `i / 2` when `i`
  is even) of load `c` is the `bf16` payload `br c i` when `bk c i`, else the masked pattern. -/
  sv : Fin 4 → Nat → ℝ := fun _ _ => 0
  bk : Fin 16 → Nat → Bool := fun _ _ => false
  br : Fin 16 → Nat → ℝ := fun _ _ => 0
  /-- The row maximum and row sum before the current round (data plane): the maximum is finite
  with the real `mr` when `mf`, else `-∞` (`%r6191` in a bias round, `%r6195` in a plain round,
  `%r6196` at the final stores); the sum is `%r6197`. -/
  mf : Bool := false
  mr : ℝ := 0
  rs : ℝ := 0

/-- Score element `n` (0 to 127) of the current round: element `n mod 32` of load `n / 32`. -/
def V.score (v : V) (n : Nat) : ℝ := v.sv ⟨n / 32 % 4, Nat.mod_lt _ (by decide)⟩ (n % 32)

/-- The exponent scale: the number of the parameter word 12 (`Pre.scales` makes it a positive
finite `f32`). -/
def scl (p : Params) : ℚ := (f32Value p.scaleLog2Bits).getD 0

/-- Whether a plain round keeps the row maximum before it (`setp.ge.f32` at pc 6882: the scaled
difference to the round's maximum is at least `-8`), when that maximum is finite. -/
def keepP (p : Params) (v : V) : Bool :=
  Assumption.erealCompare .ge
    (((scl p : ℝ) * (v.mr + -foldPT v.mr v.score) : ℝ) : EReal) ((-(8 : ℝ) : ℝ) : EReal)

/-- A plain round's row maximum after its fourth load, as a number (the value `maxP` of the
table: the maximum before the round when it is finite and kept, else the round's fold). -/
abbrev maxR (p : Params) (v : V) : ℝ :=
  match v.mf with
  | true => if keepP p v = true then v.mr else foldPT v.mr v.score
  | false => foldPF v.score

/-- Weight `i` of a plain round (column `i`, hardware or software `exp2`, both read as the
exact power): `2 ^ (x_i s - M s)` with `M` the maximum the exponents subtract. -/
def probR (p : Params) (v : V) (i : Nat) : ℝ :=
  match v.mf with
  | true =>
    if keepP p v = true then Real.rpow 2 (v.score i * (scl p : ℝ) + v.mr * -(scl p : ℝ))
    else Real.rpow 2 (v.score i * (scl p : ℝ) + foldPT v.mr v.score * -(scl p : ℝ))
  | false => Real.rpow 2 (v.score i * (scl p : ℝ) + foldPF v.score * -(scl p : ℝ))

/-- A plain round's row sum after the round (`%r6197`, pc 7598): the sum before rescaled by the
factor (`facP`: one when the maximum is kept, the exact power otherwise, zero after `-∞`) plus
the weights, as the code adds them. -/
abbrev rsP (p : Params) (v : V) : ℝ :=
  match v.mf with
  | true =>
    if keepP p v = true then rowSumT v.rs (probR p v)
    else rowSumT (v.rs * Real.rpow 2 ((scl p : ℝ) * (v.mr + -foldPT v.mr v.score))) (probR p v)
  | false => rowSumT (v.rs * 0) (probR p v)

/-- A state: the site, the recorded values, the sub-step of its instruction and the values a
vector load has returned so far. -/
structure D where
  site : Site
  v : V
  k : Fin 4 := 0
  acc : List Value := []

/-- A state at sub-step 0. -/
abbrev D.mk' (s : Site) (v : V) : D := ⟨s, v, 0, []⟩

/-- A conditional successor (both branches at sub-step 0). -/
abbrev D.ite (c : Bool) (a b : D) : D := if c = true then a else b

/-! ### Register values -/

/-- The parameters the role loads after its start, by their names in the code: the exponent
scale (12) and the bias scale (14) besides the output warp's. -/
def ps (p : Params) : List (String × Nat) :=
  ("kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
      ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
      ptrbf16gmemalign16o1i64div8_0_param_12", p.scaleLog2Bits) ::
  ("kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
      ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
      ptrbf16gmemalign16o1i64div8_0_param_14", p.invScaleBits) :: Epilogue.ps p

/-- The CTA index as the second pass's `%ctaid.x` reads it, under the launch with the role's
parameters explicit (the launch the role's segments run on). -/
abbrev ctaR (p : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  truncBits 32 (BitVec.ofNat 64 (((explicitParams L (ps p)).ctaidOf
    (g / (explicitParams L (ps p)).block)).get .x))

/-- The registers of the launch the role keeps throughout. -/
def valuesStart (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1062, b32 (g % L.block / 32)), (1069, b32 (L.sharedBase + 192)), (1072, .bits 32 (ctaW L g)),
   (2390, b32 (L.sharedBase + 208)), (2535, b32 L.sharedBase),
   (6495, b32 (L.sharedBase + 144)), (6497, b32 (L.sharedBase + 224)), (7500, b64 p.lseBase),
   (7501, b64 p.lseStride), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
   (7506, b64 p.cuQBase)]

/-- The registers that keep one value wherever they are live: the lane, the first pass's skip
predicate, the heads, the stage predicate, the stage's barrier base and its derived words, the
named barrier of the warp group, the score column base and the bias addresses. -/
def valuesRole (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1215, .bits 32 (laneW L g)), (441, .pred (skipFirst p L g)), (7140, .bits 32 (headsW p)),
   (7141, .bits 32 (headsW p)),
   (481, .pred (stg L g)), (482, .pred (scmpi .ne .b (andi (tidW L g) 31) 0)),
   (2772, .bits 32 (sel (stg L g) (i32 1) (i32 0))), (2774, .bits 32 (sbS L g)),
   (2769, sbSi L g 80), (2771, sbSi L g 320), (2784, .bits 32 (bAddr0 L g)),
   (2788, .bits 32 (tmS L g)), (2789, .bits 32 (ori (tmS L g) 64)),
   (5127, .bits 32 (nbW L g))] ++
  (List.range 14).map fun i => (2794 + 4 * i, .bits 32 (bAddr L g (bOffs.getD i 0)))

/-- The registers of a scan round of the first pass (whose CTA index is `%r12`). -/
def valuesScan (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : Scan → List (Nat × Value)
  | .first =>
    [(7888, addrU p.cuQBase (laneW L g)), (7237, .bits 32 c.w), (7240, .bits 32 c.tl),
     (7247, b32 p.batch)] ++ partials L g c 2692 3 7241
  | .loop =>
    Epilogue.loopRegs p L g false c 1217 7238 7243 7890 ++
    [(453, .pred (scmpi .eq .b (laneW L g) 31)), (7239, .bits 32 c.w), (7240, .bits 32 c.tl),
     (7247, b32 p.batch)] ++ lanePreds L g 459 ++ partials L g c 2713 3 7241
  | .second =>
    [(8982, addrU p.cuQBase (laneW L g)), (7259, .bits 32 c.w), (7262, .bits 32 c.tl),
     (7151, .bits 32 (paramW p.batch))] ++ lanePreds L g 657 ++ partials L g c 5824 3 7263
  | .loop2 =>
    [(1606, .bits 32 (ctaR p L g)), (1607, .bits 32 (addi (ctaR p L g) 1)),
     (1609, .bits 32 (reqOf L g c.grp)), (7260, .bits 32 c.acc),
     (7265, .bits 32 (min32 (addi c.grp 31) (batchOf p true))),
     (8984, addrS p.cuQBase (reqOf L g c.grp)),
     (665, .pred (scmpi .eq .b (laneW L g) 31)), (7261, .bits 32 c.w), (7262, .bits 32 c.tl),
     (7151, .bits 32 (paramW p.batch))] ++
      lanePreds L g 671 ++ partials L g c 5845 3 7263

/-- The registers of the choice of a request, in the first pass. -/
def valuesSelect (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  let r161 := sub32 c.cur (mul32 c.tot (headsW p))
  [(466, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p) r161) (ctaW L g))),
   (1221, .bits 32 r161), (7243, .bits 32 c.gx), (7240, .bits 32 c.tl),
   (7241, .bits 32 (prefixD L g c)), (1222, .bits 32 (popc c.bal)),
   (2728, .bits 32 (addi (popc c.bal) (-1))), (7247, .bits 32 (chosen c)),
   (7245, .bits 32 c.pv), (7150, .bits 32 (paramW p.batch)), (7157, .bits 32 (paramW 800))]

/-- The registers of the second pass's ballot. -/
def valuesSelect2 (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  [(678, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p)
      (sub32 c.cur (mul32 c.tot (headsW p)))) (ctaR p L g))),
   (7262, .bits 32 c.tl), (7263, .bits 32 (prefixD L g c)), (1611, .bits 32 (popc c.bal)),
   (5861, .bits 32 (addi (popc c.bal) (-1)))]

/-- The chosen request's row offset `%r6186`: the MMA warp's coordinates without its shift
and offset. -/
def rowOff (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : BitVec 64 :=
  let co := Mma.coords p L g c
  let q := sdiv co.n2 co.d2
  add32 (sub32 c.nt q)
    (sel (scmp .eq .b co.n2 (mul32 co.d2 q) || scmpi .gt .s (xor32 co.d2 co.n2) (-1))
      (i32 (-1)) (i32 0))

/-- The registers of the request's reads. -/
def valuesReq (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let c := v.sc
  [(7246, .bits 32 (rowOff p L g c)), (7891, wideS (chosen c)),
   (7892, addrS p.cuQBase (chosen c)), (2848, .bits 32 c.c0),
   (1223, .bits 32 (sub32 c.c0 c.c1)), (7893, addrS p.usedKBase (chosen c))]

/-- The tile's registers (`%r163` … `%r169`): the K/V blocks (`r166`), the blocks before the
diagonal (`r168`), the last block (`r169`). -/
def r165 (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  addi (add32 (add32 (shl (rowOff p L g v.sc) 8) v.ukw) (sub32 v.sc.c0 v.sc.c1)) 256
def r166 (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  min32 (ceil128 v.ukw) (ceil128 (r165 p L g v))
def r1808 (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  shl (or32 (shl (rowOff p L g v.sc) 1) (sel (stg L g) (i32 1) (i32 0))) 7
def r168 (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  addi (sub32 (r166 p L g v) (min32 (ceil128 v.ukw)
    (ceil128 (addi (add32 (add32 (r1808 p L g v) v.ukw) (sub32 v.sc.c0 v.sc.c1)) 128)))) 10
def r169 (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 := addi (r166 p L g v) (-1)
def r299 (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  maxi (sub32 (r166 p L g v) (min32 (r168 p L g v) (r166 p L g v))) 0
def r301 (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  let x := addi (r165 p L g v) (-256)
  let s := add32 x (shru (shrs x 31) 25)
  maxi (add32 (shrs s 7) (sel (scmpi .lt .s x 0 && scmp .ne .b x (andi s (-128)))
    (i32 (-1)) (i32 0))) 0
/-- The number of plain rounds (`%r431`). -/
def r431 (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  min32 (r169 p L g v) (r299 p L g v)

/-- The pattern of `-∞` as the code writes it (`0fFF800000`). -/
abbrev ninf32 : Value := .bits 32 (BitVec.ofNat 64 4286578688)

/-- The register of the score pair `j` (elements `2j` and `2j + 1`) of a round of kind `r`. -/
def pairReg : Rd → Nat → Nat
  | .first, j => 7303 + j
  | .bias, j => 7367 + j
  | .plain, j => if j < 4 then 8690 - j else 7427 + j

/-- The score pairs `0` to `n - 1` of a round of kind `r`. -/
def valuesPairs (r : Rd) (v : V) (n : Nat) : List (Nat × Value) :=
  (List.range n).map fun j =>
    (pairReg r j, .pair (.float .f32 (v.score (2 * j))) (.float .f32 (v.score (2 * j + 1))))

/-- The 32 registers that a plain round's score load `c` writes, before the code packs them. -/
def valuesLoaded (v : V) (c : Fin 4) : List (Nat × Value) :=
  (List.range 32).map fun i => (5188 + 32 * c.val + i, .float .f32 (v.sv c i))

/-- The row maximum before the round, as the code holds it: the number `mr` when finite, else the
pattern of `-∞` (a reducible match on `mf`, so that the segment tactics read the value of a state
whose `mf` is a literal). -/
abbrev mxVal (v : V) : Value :=
  match v.mf with
  | true => .float .f32 v.mr
  | false => ninf32

/-- A plain round's fold (`%r4449`, pc 6876): from the finite maximum before the round, or from
`-∞`. -/
abbrev foldP (v : V) : ℝ :=
  match v.mf with
  | true => foldPT v.mr v.score
  | false => foldPF v.score

/-- A plain round's row maximum after its fourth load (`%r6196`, and `%r4454`, the maximum its
exponents subtract): the maximum before the round when it is finite and kept, else the round's
fold. -/
abbrev maxP (p : Params) (v : V) : Value :=
  match v.mf with
  | true => if keepP p v = true then .float .f32 v.mr else .float .f32 (foldPT v.mr v.score)
  | false => .float .f32 (foldPF v.score)

/-- A plain round's rescaling factor of the row sum (`%r432`, stored at pc 6890): one (the
pattern `0f3F800000`) when the maximum is kept, else `2 ^ (s · (mr - F))` (`ex2.approx` read
exactly), and zero when the maximum before the round is `-∞`. -/
abbrev facP (p : Params) (v : V) : Value :=
  match v.mf with
  | true =>
    if keepP p v = true then .bits 32 (BitVec.ofNat 64 1065353216)
    else .float .f32 (Real.rpow 2 ((scl p : ℝ) * (v.mr + -foldPT v.mr v.score)))
  | false => .float .f32 0

/-- The negated exponent scale `%r170` (pc 4398, `neg_scale`), live from the first round's P part
to the end of the rounds. -/
abbrev negS (p : Params) : Value := .float .f32 ((-scl p : ℚ) : ℝ)

/-! ### The first round's masked products and its P part -/

/-- The registers of the first round's 128 masked bias products at its named-barrier arrival
(product `n` is the `n`-th). -/
def elemRegs : List Nat :=
  [3240, 3242, 3246, 3248, 3252, 3254, 3258, 3260, 3264, 3266, 3270, 3272, 3276, 3278, 3282, 3284,
   3288, 3290, 3294, 3296, 3300, 3302, 3306, 3308, 3312, 3314, 3318, 3320, 3324, 3326, 3330, 3331,
   3336, 3338, 3342, 3344, 3348, 3350, 3354, 3356, 3360, 3362, 3366, 3368, 3372, 3374, 3378, 3380,
   3384, 3386, 3390, 3392, 3396, 3398, 3402, 3404, 3408, 3410, 3414, 3416, 3420, 3422, 3426, 3427,
   3432, 3434, 3438, 3440, 3444, 3446, 3450, 3452, 3456, 3458, 3462, 3464, 3468, 3470, 3474, 3476,
   3480, 3482, 3486, 3488, 3492, 3494, 3498, 3500, 3504, 3506, 3510, 3512, 3516, 3518, 3522, 3523,
   3528, 3530, 3534, 3536, 3540, 3542, 3546, 3548, 3552, 3554, 3558, 3560, 3564, 3566, 3570, 3572,
   3576, 3578, 3582, 3584, 3588, 3590, 3594, 3596, 3600, 3602, 3606, 3608, 3612, 3614, 3618, 3619]

/-- The bias scale (parameter word 14). -/
def s14 (p : Params) : ℚ := (f32Value p.invScaleBits).getD 0

/-- Whether bias product `n` is finite (its bias half is a payload). -/
abbrev bpf (v : V) (n : Nat) : Bool := v.bk ⟨n / 8 % 16, Nat.mod_lt _ (by decide)⟩ (n % 8)
/-- Bias product `n`: the scaled bias plus the score. -/
abbrev bps (p : Params) (v : V) (n : Nat) : ℝ :=
  v.br ⟨n / 8 % 16, Nat.mod_lt _ (by decide)⟩ (n % 8) * (s14 p : ℝ) + v.score n

/-- The first round's mask count `%r2175` (pcs 3863 to 3871): the row's diagonal offset from the
tile, the used-K length and the request's row offsets. -/
def mcnt (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  let r2169 := sub32 v.ukw (shl (maxi (r169 p L g v) 0) 7)
  min32 (addi (add32 (add32 (or32 (andi (tidW L g) 127) (r1808 p L g v))
    (sub32 v.sc.c0 v.sc.c1)) r2169) 1) r2169

/-- Masked product `n` (`n = 32 k + i`) as the code's select writes it (the mask word's bit `i`
keeps the product or selects `-∞`). -/
def elemVal (m : BitVec 64) (bf : Nat → Bool) (sc : Nat → ℝ) (n : Nat) : Value :=
  if n % 32 = 0 then (if mkeep0 (n / 32) m = true then bv32 bf sc n else ninf32)
  else if n % 32 < 31 then (if mdrop (n / 32) m (n % 32) = true then ninf32 else bv32 bf sc n)
  else if mdrop31 (n / 32) m = true then ninf32 else bv32 bf sc n

/-- The first round's row maximum (the fold of the masked products). -/
def foldF (p : Params) (L : Launch) (g : Nat) (v : V) : EReal :=
  foldM (mcnt p L g v) (bpe (bpf v) (bps p v))

/-- The maximum the exponents subtract (`%r2625`, pc 4396): the row maximum, or `0` when it is
`-∞`. -/
def selMax (x : EReal) : Value :=
  if x = ⊥ then .bits 32 (BitVec.ofNat 64 0) else Assumption.erealValue .f32 x

/-- The first round's data at its named-barrier arrival: the masked products, the maximum the
exponents subtract and the row maximum. -/
def valuesNarr1 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  (3685, selMax (foldF p L g v)) :: (7256, Assumption.erealValue .f32 (foldF p L g v)) ::
    (List.range 128).map
      (fun n => (elemRegs.getD n 0, elemVal (mcnt p L g v) (bpf v) (bps p v) n))

/-- The values the first round's exponent stretch reads at pc 4399 (after the negated scale at
pc 4398): the arrival state's data, `%r170` and the exponent scale word. -/
def vExpo1 (p : Params) (L : Launch) (g : Nat) (v : V) : Nat → Value := fun r =>
  ((valuesNarr1 p L g v ++ [(1230, negS p), (7132, .bits 32 (paramW p.scaleLog2Bits))]).lookup
    r).getD (.pred false)

/-- The first round's exponent stretch's values at its first P store (pc 4826): the generated
run's terms (`Gen/Expo1.lean`, pcs 4399 to 4825) over the values at pc 4399. -/
def expoE (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  Gen.expo1_facts14 (vExpo1 p L g v)

/-- Whether an extended real is not `-∞` (the row maximum's flag). -/
def finE (x : EReal) : Bool := decide (x ≠ ⊥)

/-- The real of an `f32` number value (`0` for any other value). -/
def valR : Value → ℝ
  | .float .f32 r => r
  | _ => 0

/-- The first round's row sum (`%r6197` at pc 5006): the generated row sum (`Gen/Rsum1.lean`) of
the exponent stretch's weights. -/
def rs1 (p : Params) (L : Launch) (g : Nat) (v : V) : ℝ :=
  valR (Gen.rsum1_v5005 (lookupD (expoE p L g v)))

/-- The values a plain round's exponent stretch reads at pc 6892 (its first generated run,
`Gen/ExpoP.lean`): `%r170`, the maximum the exponents subtract (`%r4454`) and the round's
maximum, the factor, the row sum, the scale word's pair and the 64 score pairs. -/
def vExpoP (p : Params) (v : V) (r : Nat) : Value :=
  if r = 1230 then negS p
  else if r = 5514 ∨ r = 7256 then maxP p v
  else if r = 1492 then facP p v
  else if r = 7257 then .float .f32 v.rs
  else if r = 8692 then
    joinValue (.bits 32 (paramW p.scaleLog2Bits)) (.bits 32 (paramW p.scaleLog2Bits))
  else if 8687 ≤ r ∧ r ≤ 8690 then
    .pair (.float .f32 (v.score (2 * (8690 - r)))) (.float .f32 (v.score (2 * (8690 - r) + 1)))
  else if 7431 ≤ r ∧ r ≤ 7490 then
    .pair (.float .f32 (v.score (2 * (r - 7427)))) (.float .f32 (v.score (2 * (r - 7427) + 1)))
  else .pred false

/-- The number a software `exp2` lane writes for its input (`swExp2Lane`; `0` if it declines). -/
def laneR (x : Value) : ℝ :=
  match Assumptions.swExp2Lane x with
  | .ok y => y
  | .error _ => 0

/-- The constants the defining software `exp2` site (pc 7090) sets, as the template states them. -/
def cuteConsts : List (Nat × Value) :=
  [(5666, Assumption.cuteBits 0x4B400000), (8766, Assumption.cutePair 0x4B400000),
   (5667, Assumption.cuteBits 0x3E6906A4), (8770, Assumption.cutePair 0x3E6906A4),
   (5668, Assumption.cuteBits 0x3D9DF09D), (8771, Assumption.cutePair 0x3D9DF09D),
   (5669, Assumption.cuteBits 0x3F31F519), (8773, Assumption.cutePair 0x3F31F519),
   (5670, Assumption.cuteBits 0x3F800000), (8775, Assumption.cutePair 0x3F800000)]

/-- The values a software `exp2` site writes: its two outputs from its two inputs' values. -/
def swOut (V : Nat → Value) (i₀ i₁ o₀ o₁ : Nat) : List (Nat × Value) :=
  [(o₀, .float .f32 (laneR (V i₀))), (o₁, .float .f32 (laneR (V i₁)))]

/-- The values of a plain round's exponent stretch along its runs and template sites: the
generated runs' end facts and the sites' outputs, each over the lookup in the lists before. -/
def expoPS0 (p : Params) (v : V) : List (Nat × Value) := Gen.expoP0_facts7 (vExpoP p v)
def expoPS1 (p : Params) (v : V) : List (Nat × Value) :=
  let a := swOut (lookupD (expoPS0 p v)) 5564 5565 5128 5131 ++ cuteConsts ++ expoPS0 p v
  swOut (lookupD a) 5566 5567 5134 5137 ++ a
def expoPS2 (p : Params) (v : V) : List (Nat × Value) :=
  Gen.expoP1_facts1 (lookupD (expoPS1 p v))
def expoPS3 (p : Params) (v : V) : List (Nat × Value) :=
  let a := swOut (lookupD (expoPS2 p v)) 5580 5581 5140 5143 ++ expoPS2 p v
  swOut (lookupD a) 5582 5583 5146 5149 ++ a
def expoPS4 (p : Params) (v : V) : List (Nat × Value) :=
  Gen.expoP2_facts2 (lookupD (expoPS3 p v))
def expoPS5 (p : Params) (v : V) : List (Nat × Value) :=
  let a := swOut (lookupD (expoPS4 p v)) 5596 5597 5152 5155 ++ expoPS4 p v
  swOut (lookupD a) 5598 5599 5158 5161 ++ a
def expoPS6 (p : Params) (v : V) : List (Nat × Value) :=
  Gen.expoP3_facts1 (lookupD (expoPS5 p v))
def expoPS7 (p : Params) (v : V) : List (Nat × Value) :=
  let a := swOut (lookupD (expoPS6 p v)) 5612 5613 5164 5167 ++ expoPS6 p v
  swOut (lookupD a) 5614 5615 5170 5173 ++ a
/-- **The plain round's exponent stretch's values at its first P store** (pc 7416). -/
def expoPE (p : Params) (v : V) : List (Nat × Value) :=
  Gen.expoP4_facts3 (lookupD (expoPS7 p v))

/-- The unpacks before a plain round's second to fourth P stores (pcs 7417 to 7424, 7426 to
7433, 7438 to 7445): low half, high half, the packed word. -/
def unpackSpecP : List (Nat × Nat × Nat) :=
  [(5749, 5750, 8799), (5751, 5752, 8798), (5753, 5754, 8805), (5755, 5756, 8804),
   (5757, 5758, 8803), (5759, 5760, 8802), (5761, 5762, 8801), (5763, 5764, 8800),
   (5765, 5766, 8835), (5767, 5768, 8834), (5769, 5770, 8841), (5771, 5772, 8840),
   (5773, 5774, 8839), (5775, 5776, 8838), (5777, 5778, 8837), (5779, 5780, 8836),
   (5782, 5783, 8849), (5784, 5785, 8848), (5786, 5787, 8847), (5788, 5789, 8846),
   (5790, 5791, 8845), (5792, 5793, 8844), (5794, 5795, 8843), (5796, 5797, 8842)]

/-- **A plain round's P part's data**: the exponent stretch's terms (`expoPE`) and the halves the
store unpacks write, as splits of the packed words' terms. -/
def pPData (p : Params) (v : V) : List (Nat × Value) :=
  expoPE p v ++ unpackSpecP.flatMap fun (lo, hi, w) =>
    [(lo, (splitValue 64 (lookupD (expoPE p v) w)).1),
     (hi, (splitValue 64 (lookupD (expoPE p v) w)).2)]

/-- **A plain round's row sum** (`%r6197` at pc 7599): the generated row sum (`Gen/RsumP.lean`)
of the row sum before the round rescaled by the factor and the 128 weights, over the P part's
data with the zero the move at pc 7467 writes. -/
def rsPG (p : Params) (v : V) : ℝ :=
  valR (Gen.rsumPb_v7598 (lookupD ((5806, .bits 32 (BitVec.ofNat 64 0)) ::
    Gen.rsumPa_facts1 (lookupD (pPData p v)))))

/-- The registers of the tile from the request's last read to the end of the rounds. -/
def valuesTile (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  [(1223, .bits 32 (sub32 v.sc.c0 v.sc.c1)), (1224, .bits 32 v.ukw),
   (1225, .bits 32 (r165 p L g v)), (1226, .bits 32 (r166 p L g v)),
   (1228, .bits 32 (r168 p L g v)), (1229, .bits 32 (r169 p L g v)),
   (2868, .bits 32 (r1808 p L g v)), (2767, sbSi L g 192), (2768, w32 (i32 1)),
   (2770, w32 (i32 0)), (2913, .bits 32 (ori (tmS L g) 32)),
   (2978, .bits 32 (ori (tmS L g) 96)), (3075, .bits 32 (sel (stg L g) (i32 12) (i32 11))),
   (3077, .bits 32 (sbS L g)), (3078, w32 (i32 1)),
   (7132, .bits 32 (paramW p.scaleLog2Bits))]

/-- The registers of the first round's P part (store addresses, barrier words, the bias
scale's pair). -/
def valuesP1 (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(7896, joinValue (.bits 32 (paramW p.invScaleBits)) (.bits 32 (paramW p.invScaleBits))),
   (3217, .bits 32 (sbS L g)), (3223, .bits 32 (ori (tmS L g) 64)),
   (3224, .bits 32 (ori (tmS L g) 112)), (3225, .bits 32 (ori (tmS L g) 96)),
   (3226, .bits 32 (ori (tmS L g) 80)), (3927, w32 (i32 1)), (3946, .bits 32 (sbS L g)),
   (3947, w32 (i32 1)), (3948, sbSi L g 192), (3949, w32 (i32 0))]

/-- The registers of a bias round (the loop at pcs 5032 to 6653). -/
def valuesBias (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  [(631, .pred (stg L g)), (632, .pred (scmpi .ne .b (andi (tidW L g) 31) 0)),
   (1359, .bits 32 (r299 p L g v)), (1361, .bits 32 (r301 p L g v)),
   (3964, sbSi L g 80), (3965, sbSi L g 320), (3970, .bits 32 (tmS L g)),
   (3971, .bits 32 (ori (tmS L g) 96)), (3972, .bits 32 (ori (tmS L g) 32)),
   (3973, .bits 32 (ori (tmS L g) 64)), (3976, .bits 32 (rowSb L g)),
   (3977, .bits 32 (bOff L g)), (4037, .bits 32 (sbS L g)), (4170, .bits 32 (bAddr0 L g)),
   (4235, .bits 32 (sel (stg L g) (i32 12) (i32 11))), (4237, .bits 32 (sbS L g)),
   (4238, w32 (i32 1)), (634, .pred (scmp .lt .u v.bt (r301 p L g v))),
   (637, .pred (stg L g)), (4571, .bits 32 (statA L g)),
   (4821, .bits 32 (ori (tmS L g) 64)), (4822, .bits 32 (ori (tmS L g) 112)),
   (4823, .bits 32 (ori (tmS L g) 96)), (4824, .bits 32 (ori (tmS L g) 80)),
   (5097, .bits 32 (sbS L g)), (5098, w32 (i32 1)), (5117, .bits 32 (sbS L g)),
   (5118, w32 (i32 1)), (5119, sbSi L g 192),
   (7248, w32 v.nb), (7249, w32 v.bt), (7250, w32 v.bpar), (7253, w32 v.spar), (7258, w32 v.ppar),
   (7132, .bits 32 (paramW p.scaleLog2Bits)),
   (7896, joinValue (.bits 32 (paramW p.invScaleBits)) (.bits 32 (paramW p.invScaleBits)))] ++
  (List.range 14).map fun i => (3982 + 4 * i, .bits 32 (bAddr L g (bOffs.getD i 0)))

/-- The registers of a plain round (the loop at pcs 6661 to 7604). -/
def valuesPlain (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  [(5126, sbSi L g 80), (5176, .bits 32 (sel (stg L g) (i32 128) (i32 0))),
   (5177, .bits 32 (tidW L g)), (5180, .bits 32 (tmS L g)),
   (5181, .bits 32 (ori (tmS L g) 96)), (5182, .bits 32 (ori (tmS L g) 32)),
   (5183, .bits 32 (ori (tmS L g) 64)), (5184, .bits 32 (ori (tmS L g) 112)),
   (5185, .bits 32 (ori (tmS L g) 80)), (5187, .bits 32 (sbS L g)),
   (7133, .bits 32 (paramW p.scaleLog2Bits)),
   (8692, joinValue (.bits 32 (paramW p.scaleLog2Bits)) (.bits 32 (paramW p.scaleLog2Bits))),
   (5518, .bits 32 (statA L g)), (5781, w32 (i32 1)), (5800, .bits 32 (sbS L g)),
   (5801, w32 (i32 1)), (5802, sbSi L g 192),
   (7253, w32 v.spar), (7254, w32 v.pl), (7258, w32 v.ppar)]

/-- The registers of the final stores. -/
def valuesFin (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  [(652, .pred (scmp .gt .s (laneW L g) (paramW p.batch))), (5814, .bits 32 (statA L g)),
   (7151, .bits 32 (paramW p.batch)), (7258, w32 v.ppar)]

/-- The registers at state `d`. -/
def values (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let v := d.v
  match d.site with
  | .setmax | .bar1 => [(7247, b32 p.batch)]
  | .word k | .down k | .up k _ | .total k => valuesScan p L g v.sc k ++ [(7258, w32 v.ppar)]
  | .vote false | .pre false | .tiles false => valuesSelect p L g v.sc
  | .vote true | .pre true | .tiles true => valuesSelect2 p L g v.sc ++ [(7258, w32 v.ppar)]
  | .q0 | .q1 | .uk => valuesReq p L g v
  | .wq | .ws .first | .sld .first _ | .wb false | .bld false _ | .fence false
  | .bsync false | .barr false => valuesTile p L g v
  | .narr .first | .pst .first _ | .pwst .first _ | .parr .first | .pws .first
  | .pel .first | .parr2 .first | .pwend .first => valuesP1 p L g ++ valuesTile p L g v
  | .ws .plain | .sld .plain _ | .sldw _ | .stat true | .narr .plain | .pst .plain _
  | .pwst .plain _ | .parr .plain | .pws .plain | .pel .plain | .parr2 .plain
  | .pwend .plain => valuesPlain p L g v
  | .fin _ | .finarr => valuesFin p L g v
  | .wend _ | .barEnd _ | .exit _ => [(7258, w32 v.ppar), (5864, sbSi L g 192)]
  | _ => valuesBias p L g v ++ valuesTile p L g v

/-- The value of register `r` at state `d`. -/
def valueOf (p : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values p L g d).lookup r).getD (((valuesRole p L g).lookup r).getD
    (((valuesStart p L g).lookup r).getD (.pred false)))

/-- The row maximum before the round (`%r6191` in a bias round, `%r6195` in a plain round), the
row sum (`%r6197`) and the negated scale. -/
def valuesRun (p : Params) (v : V) : List (Nat × Value) :=
  [(7251, mxVal v), (7255, mxVal v), (7257, .float .f32 v.rs), (1230, negS p)]

/-! ### A bias round after its maximum -/

/-- The readings of a bias round's 128 products (a real, or `-∞` for a masked bias half). -/
abbrev bpeB (p : Params) (v : V) : Nat → EReal := bpe (bpf v) (bps p v)

/-- The row maximum before the round as an extended real. -/
abbrev mxE (v : V) : EReal := if v.mf = true then (v.mr : EReal) else ⊥

/-- A bias round's maximum before its keep test (`%r3500`, `foldB`). -/
abbrev foldBE (p : Params) (v : V) : EReal := foldB (mxE v) (bpeB p v)

/-- The fold as a number (it is one when the maximum before the round is finite). -/
abbrev foldBR (p : Params) (v : V) : ℝ := (foldBE p v).toReal

/-- Whether a bias round keeps the row maximum before it (`setp.ge.f32` at pc 5671), when that
maximum is finite; stated in the walk's form, as `keepP`. -/
def keepB (p : Params) (v : V) : Bool :=
  Assumption.erealCompare .ge
    (((scl p : ℝ) * (v.mr + -foldBR p v) : ℝ) : EReal) ((-(8 : ℝ) : ℝ) : EReal)

/-- A bias round's products (pcs 5279 to 5534): the scaled bias plus the score, `-∞` for a
masked half. -/
def valuesProdB (p : Params) (v : V) : List (Nat × Value) :=
  (List.range 64).map fun j =>
    (8317 + 2 * j, .pair (bv32 (bpf v) (bps p v) (2 * j)) (bv32 (bpf v) (bps p v) (2 * j + 1)))

/-- A bias round after its maximum (pcs 5666 to 5674): the row maximum (`%r6196`), the maximum
the exponents subtract (`%r3505`) and the row sum's rescaling factor (`%r302`), each per kind of
the maximum before the round (`bif v.mf`, so that the list's spine is literal and a walk that
carries the entries reads them for any `v`). -/
def valuesBiasM (p : Params) (v : V) : List (Nat × Value) :=
  [(7256, bif v.mf then (if keepB p v = true then .float .f32 v.mr else .float .f32 (foldBR p v))
     else Assumption.erealValue .f32 (foldBE p v)),
   (4565, bif v.mf then (if keepB p v = true then .float .f32 v.mr else .float .f32 (foldBR p v))
     else (if foldBE p v = ⊥ then .bits 32 (BitVec.ofNat 64 0)
       else Assumption.erealValue .f32 (foldBE p v))),
   (1362, bif v.mf then (if keepB p v = true then .bits 32 (BitVec.ofNat 64 1065353216)
       else .float .f32 (Real.rpow 2 ((scl p : ℝ) * (v.mr + -foldBR p v))))
     else .float .f32 0)]

/-! ### A bias round's P part -/

/-- The start values of a bias round's exponent stretch's software and hardware paths (the
scaled-product run's end values from the named-barrier arrival's). -/
def vExpoB (p : Params) (L : Launch) (g : Nat) (v : V) : Nat → Value :=
  let d := D.mk' (.narr .bias) v
  let data := valuesRun p v ++ valuesBiasM p v ++ valuesProdB p v
  lookupD (Gen.expoB0_facts5 fun r => (data.lookup r).getD (valueOf p L g d r))

/-- The values at the tail's second run's start: per path (`%p632`: the round index below
`%r301` runs the software path). -/
def vTailB (p : Params) (L : Launch) (g : Nat) (v : V) : Nat → Value :=
  bif Epilogue.scmp .lt .u v.bt (r301 p L g v) then
    nextTB (lookupD (Gen.expoBB8_facts1 (vB8 (vExpoB p L g v))))
  else nextTA (lookupD (Gen.expoBA_facts5 (vExpoB p L g v)))

/-- The exponent stretch's end facts (the tail's second run). -/
def tailB (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  Gen.expoBTA1_facts4 (vTailB p L g v)

/-- The unpacks before a bias round's second to fourth P stores (pcs 6509 to 6540): low half, high
half, the packed word. -/
def unpackSpecB : List (Nat × Nat × Nat) :=
  [(5064, 5065, 8594), (5066, 5067, 8593), (5068, 5069, 8592), (5070, 5071, 8591),
   (5072, 5073, 8590), (5074, 5075, 8589), (5076, 5077, 8588), (5078, 5079, 8587),
   (5080, 5081, 8586), (5082, 5083, 8585), (5084, 5085, 8584), (5086, 5087, 8583),
   (5088, 5089, 8582), (5090, 5091, 8581), (5092, 5093, 8580), (5094, 5095, 8579),
   (5099, 5100, 8578), (5101, 5102, 8577), (5103, 5104, 8576), (5105, 5106, 8575),
   (5107, 5108, 8574), (5109, 5110, 8573), (5111, 5112, 8572), (5113, 5114, 8571)]

/-- The halves those unpacks write, as the splits of the packed words' terms. -/
def halvesB (E : List (Nat × Value)) : List (Nat × Value) :=
  unpackSpecB.flatMap fun (lo, hi, w) =>
    [(lo, (splitValue 64 (lookupD E w)).1), (hi, (splitValue 64 (lookupD E w)).2)]

/-- A bias round's P part's data: the running values, the maximum's, the exponent stretch's end
and the store halves. -/
def pBData (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  tailB p L g v ++ halvesB (tailB p L g v) ++ valuesRun p v ++ valuesBiasM p v

/-- The start values after the row-sum rescale and the zero move at pc 6562. -/
abbrev rsumBbStart (p : Params) (L : Launch) (g : Nat) (v : V) : Nat → Value :=
  lookupD ((5123, .bits 32 0) :: Gen.rsumBa_facts1 (lookupD (pBData p L g v)))

/-- The bias round's new row sum (pc 6647). -/
def rsB (p : Params) (L : Launch) (g : Nat) (v : V) : ℝ :=
  valR (Gen.rsumBb_v6646 (rsumBbStart p L g v))

/-- The bias round's maximum after the keep test. -/
def maxB (p : Params) (v : V) : EReal :=
  if v.mf && keepB p v then (v.mr : EReal) else foldBE p v

/-- The registers whose facts a state states: the control registers live at its instruction
(at the implicit wait of a plain round's score load, sub-step 1, those after the load). -/
def livePc (d : D) : Nat :=
  match d.site with
  | .sldw _ => if d.k = 1 then d.site.pc + 1 else d.site.pc
  | _ => d.site.pc

abbrev facts (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (ctlLive (livePc d)) (valueOf p L g d)

/-! ### Transitions -/

/-- The real number of an `f32` payload. -/
def fl32 (v : Value) : Option ℝ :=
  match v with
  | .float .f32 x => some x
  | _ => none

/-- The reals of a Tensor Memory load's elements, when every element is an `f32` payload. -/
def flAll (vals : List Value) : Option (Nat → ℝ) :=
  if vals.all fun v => (fl32 v).isSome then
    some fun i => (fl32 (vals.getD i (.pred false))).getD 0
  else none

/-! ### The reals of a score load -/

theorem flAll_get {vals : List Value} {xs : Nat → ℝ} (h : flAll vals = some xs) {i : Nat}
    (hi : i < vals.length) (dflt : Value) : vals.getD i dflt = .float .f32 (xs i) := by
  unfold flAll at h
  split at h
  · rename_i hall
    obtain rfl := Option.some.inj h
    have hm : vals[i] ∈ vals := List.getElem_mem hi
    have hs := List.all_eq_true.mp hall _ hm
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    revert hs
    cases vals[i] with
    | float f x => cases f <;> simp [fl32]
    | _ => simp [fl32]
  · cases h

theorem flAll_eq_none_iff {vals : List Value} :
    flAll vals = none ↔ ¬ ∀ v ∈ vals, ∃ x, v = .float .f32 x := by
  have key : ∀ v : Value, (fl32 v).isSome = true ↔ ∃ x, v = .float .f32 x := by
    intro v
    cases v with
    | float f x => cases f <;> simp [fl32]
    | _ => simp [fl32]
  unfold flAll
  split
  · rename_i hall
    simp only [reduceCtorEq, false_iff, not_not]
    intro v hv
    exact (key v).mp (List.all_eq_true.mp hall v hv)
  · rename_i hall
    simp only [true_iff]
    intro hc
    apply hall
    exact List.all_eq_true.mpr fun v hv => (key v).mpr (hc v hv)

theorem flAll_some_of {vals : List Value} (h : ∀ v ∈ vals, ∃ x, v = .float .f32 x) :
    ∃ xs, flAll vals = some xs := by
  cases hf : flAll vals with
  | none => exact absurd h (flAll_eq_none_iff.mp hf)
  | some xs => exact ⟨xs, rfl⟩

/-- A bias word the machine accepts: two `bf16` elements, each a payload or the masked pattern
`0xFF80` (two masked halves may come merged into one word). -/
abbrev biasOk (x : Value) : Bool := packedWithVal .bf16 (maskedElem .bf16 0xFF80) x

/-- Half `i` of the words `ws` of a bias load, as recorded: the payload, or `none` for the mask
(low half first, `maskedPair`). -/
def halfOf (ws : List Value) (i : Nat) : Option ℝ :=
  let pr := maskedPair .bf16 (ws.getD (i / 2) (.pred false))
  if i % 2 = 0 then pr.1 else pr.2

/-- Record the halves of bias load `c` from its four words. -/
def recordBias (v : V) (c : Fin 16) (ws : List Value) : V :=
  { v with
    bk := Function.update v.bk c fun i => (halfOf ws i).isSome
    br := Function.update v.br c fun i => (halfOf ws i).getD 0 }

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- A state at site `s` with the scan state changed by `f`. -/
abbrev scAt (d : D) (s : Site) (f : Epilogue.D → Epilogue.D) : D :=
  D.mk' s { d.v with sc := f d.v.sc }

/-- The end of the scan of pass `late`, with the last group's capped first request `gx` and the
tiles `cur` through it: past the batch, no tile (the final poll); else the ballot. -/
def scanExit (p : Params) (late : Bool) (d : D) (gx cur : BitVec 64) : D :=
  D.ite (scmp .ge .s gx (batchOf p late))
    (D.mk' (.wend late) (if late then d.v else { d.v with ppar := i32 1 }))
    (scAt d (.vote late) fun c => { c with gx := gx, cur := cur })

/-- The CTA index a pass compares with: `%r12` in the first, `%ctaid.x` in the second. -/
abbrev ctaOf (p : Params) (L : Launch) (g : Nat) (late : Bool) : BitVec 64 :=
  if late then ctaR p L g else ctaW L g

/-- The loop head of pass `late` with group start `grp` and tiles `acc` before it. -/
def loopHead (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) (grp acc : BitVec 64) :
    D :=
  D.ite (scmp .ge .s (addi grp 31) (batchOf p late))
    (scanExit p late d (min32 (addi grp 31) (batchOf p late)) (addi (ctaOf p L g late) 1))
    (D.ite (scmp .gt .s (reqOf L g grp) (batchOf p late))
      (scAt d (.down (loopOf late)) fun c => { c with grp := grp, acc := acc, w := i32 0 })
      (scAt d (.word (loopOf late)) fun c => { c with grp := grp, acc := acc }))

/-- After lane 31's prefix sum `x` of a round of scan `k`. -/
def afterTotal (p : Params) (L : Launch) (g : Nat) (k : Scan) (d : D) (x : BitVec 64) : D :=
  let d := scAt d d.site fun c => { c with tot := x }
  match k with
  | .first | .second =>
    D.ite (scmp .gt .s (mul32 x (headsW p)) (ctaOf p L g k.late))
      (scanExit p k.late d (i32 0) (mul32 x (headsW p)))
      (loopHead p L g k.late d (i32 0) (mul32 x (headsW p)))
  | .loop | .loop2 =>
    D.ite (scmp .le .s (mad32 x (headsW p) d.v.sc.acc) (ctaOf p L g k.late))
      (loopHead p L g k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.v.sc.acc))
      (scanExit p k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.v.sc.acc))

/-- After the chosen request's tile count `x`: the coordinates, then the request's reads if
the request exists. A division without a rule faults the thread. -/
def afterTiles (p : Params) (L : Launch) (g : Nat) (d : D) (x : BitVec 64) : Option D :=
  let d := scAt d d.site fun c => { c with nt := x }
  let co := Mma.coords p L g d.v.sc
  if divOk co.n1 co.d1 then
    if divOk co.n2 co.d2 then
      some (D.ite (scmp .lt .s (chosen d.v.sc) (paramW p.batch)) (D.mk' .q0 d.v)
        (D.mk' (.wend false) { d.v with ppar := i32 1 }))
    else none
  else none

/-- The start of a scheduler pass: lanes past the batch skip their read. -/
def passStart (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) : D :=
  let k : Scan := if late then .second else .first
  D.ite (scmp .gt .s (laneW L g) (if late then paramW p.batch else BitVec.ofNat 64 p.batch))
    (scAt d (.down k) fun c => { c with w := i32 0 }) (D.mk' (.word k) d.v)

/-- After the first round: the bias rounds when the tile has blocks before the diagonal
beyond the first, else the plain rounds' entry. -/
def plainEntry (p : Params) (L : Launch) (g : Nat) (v : V) : D :=
  D.ite (scmpi .lt .s (r431 p L g v) 1) (D.mk' (.fin 0) v)
    (D.mk' (.ws .plain) { v with pl := neg32 (r431 p L g v) })

def afterFirst (p : Params) (L : Launch) (g : Nat) (d : D) : D :=
  let v := { d.v with
    ppar := i32 1, spar := i32 1, mf := finE (foldF p L g d.v),
    mr := EReal.toReal (foldF p L g d.v), rs := rs1 p L g d.v }
  D.ite (scmpi .lt .s (sub32 (r169 p L g d.v) (r299 p L g d.v)) 1) (plainEntry p L g v)
    (D.mk' (.ws .bias) { v with
      nb := sub32 (r299 p L g d.v) (r166 p L g d.v), bt := addi (r169 p L g d.v) (-1),
      bpar := i32 1 })

/-- The end of a bias round: another bias round or the plain rounds' entry. -/
def afterBias (p : Params) (L : Launch) (g : Nat) (d : D) : D :=
  let v := { d.v with
    ppar := xor32 d.v.ppar (i32 1), bpar := xor32 d.v.bpar (i32 1),
    spar := xor32 d.v.spar (i32 1), nb := addi d.v.nb 1,
    mf := finE (maxB p d.v), mr := (maxB p d.v).toReal, rs := rsB p L g d.v }
  D.ite (scmpi .ne .b (addi d.v.nb 1) (-1)) (D.mk' (.ws .bias) { v with bt := addi d.v.bt (-1) })
    (plainEntry p L g v)

/-- The end of a plain round: another plain round or the final stores. -/
def afterPlain (d : D) : D :=
  let v := { d.v with
    spar := xor32 d.v.spar (i32 1), ppar := xor32 d.v.ppar (i32 1), pl := addi d.v.pl 1 }
  D.ite (scmpi .ne .b (addi d.v.pl 1) 0) (D.mk' (.ws .plain) v) (D.mk' (.fin 0) v)

/-- The site after the last score load of a round. -/
def afterLoads : Rd → Site
  | .first => .wb false
  | .bias => .wb true
  | .plain => .stat true

/-- The site after the P part's closing poll. -/
def afterRound (p : Params) (L : Launch) (g : Nat) (d : D) : Rd → D
  | .first => afterFirst p L g d
  | .bias => afterBias p L g d
  | .plain => afterPlain { d with v := { d.v with
      mf := true, mr := maxR p d.v, rs := rsPG p d.v } }

/-- The site after P store `q` of a round. -/
def pstNext (r : Rd) : Fin 4 → Site
  | 0 => .pst r 1
  | 1 => .pst r 2
  | 2 => .pwst r 0
  | 3 => .pwst r 1

/-- The round of a site with bias. -/
abbrev rdOf (b : Bool) : Rd := if b then .bias else .first

/-- The successor after event `e` (at sub-step 0 unless stated). -/
def succ (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  let go (s : Site) : Option (Option D) := some (some (D.mk' s d.v))
  let poll (s : Site) : Option (Option D) :=
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then D.mk' s d.v else d))
    | _ => none
  match d.site with
  | .setmax => go .bar1
  | .bar1 => some (some (passStart p L g false d))
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
      if late then D.mk' (.tiles true) d.v
      else scAt d (.tiles false) fun c => { c with pv := mul32 x (headsW p) }
    | _ => none
  | .tiles late =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match v with
      | .bits 32 x =>
        if late then some (some (D.mk' (.wend true) d.v))
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
      | .ok v => word32 v fun x => D.mk' .wq { d.v with ukw := x }
      | .error _ => none
    | _ => none
  | .wq => poll (.ws .first)
  | .ws r => poll (.sld r 0)
  | .sld r c =>
    match e.kind with
    | .tc (.ld _ vals _) =>
      match flAll vals with
      | some xs =>
        let v := { d.v with sv := Function.update d.v.sv c xs }
        match r with
        | .plain => some (some ⟨.sldw c, v, 1, []⟩)
        | r => some (some (D.mk' (if c.val = 3 then afterLoads r else .sld r (c + 1)) v))
      | none => some none
    | _ => none
  | .sldw c => if d.k = 1 then go (if c.val = 3 then .stat true else .sld .plain (c + 1))
    else some none
  | .wb b => poll (.bld b 0)
  | .bld b c =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok x =>
        if biasOk x = true then
          if d.k.val < 3 then some (some { d with k := d.k + 1, acc := d.acc ++ [x] })
          else some (some (D.mk' (if c.val = 15 then .fence b else .bld b (c + 1))
            (recordBias d.v c (d.acc ++ [x]))))
        else some none
      | .error _ => none
    | _ => none
  | .fence b => go (.bsync b)
  | .bsync b =>
    some (some (D.ite (scmpi .ne .b (andi (tidW L g) 31) 0)
      (D.mk' (if b then .stat false else .narr .first) d.v) (D.mk' (.barr b) d.v)))
  | .barr b => go (if b then .stat false else .narr .first)
  | .stat pl => go (.narr (if pl then .plain else .bias))
  | .narr r => go (.pst r 0)
  | .pst .plain q => go (pstNext .plain q)
  | .pst r 0 => if d.k = 0 then some (some { d with k := 1 }) else go (.pst r 1)
  | .pst r q => go (pstNext r q)
  | .pwst r k => go (if k.val = 0 then .parr r else .pws r)
  | .parr r => go (.pst r 3)
  | .pws r => go (.pel r)
  | .pel r =>
    match e.kind with
    | .elect _ _ ld => go (if laneOf L g = ld then .parr2 r else .pwend r)
    | _ => none
  | .parr2 r => go (.pwend r)
  | .pwend r =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then afterRound p L g d r else d))
    | _ => none
  | .fin 0 => go (.fin 1)
  | .fin 1 => go .finarr
  | .finarr => some (some (passStart p L g true d))
  | .wend late => poll (.barEnd late)
  | .barEnd late => go (.exit late)
  | .exit _ => none

/-- The midway sub-steps a state may have, with the values its instruction has returned so far:
the elements of a bias load (one accepted word per element read), the implicit wait of a plain
round's score load and the store after the implicit wait of a round's first P store (sub-step 1,
no value). -/
def Site.midOk : Site → Fin 4 → List Value → Prop
  | .bld _ _, k, acc => acc.length = k.val ∧ acc.all biasOk = true
  | .sldw _, k, acc => k = 1 ∧ acc = []
  | .pst .first 0, k, acc => k = 1 ∧ acc = []
  | .pst .bias 0, k, acc => k = 1 ∧ acc = []
  | _, _, _ => False

/-- Whether a site is entered at sub-step 0: every site but a plain round's implicit wait, which
the machine enters at sub-step 1 after the load. -/
def Site.first : Site → Bool
  | .sldw _ => false
  | _ => true

/-- The softmax warps as a code machine. -/
@[reducible] def code (p : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := D.mk' .setmax {}
  pc := (·.site.pc)
  facts := facts p L g
  sub := (·.k.val)
  acc := (·.acc)
  inv := fun d => (d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc
  next := succ p L g

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
