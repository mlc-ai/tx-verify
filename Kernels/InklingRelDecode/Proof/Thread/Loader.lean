-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Flow.Sites
public import Kernels.InklingRelDecode.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Async
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.SignedBits
public import Kernels.InklingRelDecode.Proof.Thread.RawWord

@[expose] public section

/-! # The loader warp as abstract states

Warp 6 of a CTA (all 32 lanes) is the KV loader of `_rel_verify_kernel`: the worker dispatch
(`brx.idx` at pc 2343) sends it to pc 2344. It lowers its register budget (`setmaxnreg.dec 24`),
reads `(num_pre, num_iters)` from `global_smem + 212992` (a two-element vector load: two events)
and waits at the named barrier 1 for the default partition's write. If `num_pre >= num_iters` it
skips the loop. Otherwise, for each iteration `i = num_pre, …, num_iters - 1` it

* polls the `kv_empty` barrier of ring slot `i % 3` for parity `1 - (i / 3) % 2` (`wait`, a poll
  loop; a failed poll returns to the site),
* synchronises the warp (`wb0`), and lane 0 arrives on the slot's `kv_ready` barrier expecting
  65536 bytes (`arrive`, guarded by `%p20`: the other lanes skip it),
* loads the two block-table words of the iteration's two 64-key slabs (`ldb0`, `ldb1`),
* issues eight TMA tile copies into the slot (K low and high half and V low and high half of
  slab 0, then the same of slab 1), each pair by the lane that `elect.sync` elects (`el`,
  `cp`; the pair is guarded by the election's predicate, so the other lanes skip it), with a
  `bar.warp.sync` before each election after the first (`wb1` … `wb4`),

and after the last iteration it waits at the named barrier 1 again (`bar1`) and raises its
register budget (`setmaxnreg.inc 256`, `setMaxInc`), which is the end of the role: the next
instruction is the dispatch loop's, which another role file owns.

A state is the next event with the loop variables the code carries: the iteration counter
`i` (`%r1444`, starting at `num_pre`), `num_iters` (`n`, `%r6`) and the two block-table words
(`p0`, `p1`: `%r120` and `%r130`). The counters are 32-bit words: the two loaded values are kept
as they are in the state's registers (`pro`, at `%r1444` and `%r6`; the code reads them as bits,
`Raw.word32Of`), `i` and `n` are the numbers they read as, the loop's entry test is signed
(`setp.ge.s32`), and the increment wraps around (`afterIter`). The registers `%r1441 … %r1443`
(the next block's key row, the slot's shared offsets) and all the other registers of the loop
are functions of these (`table`): the code adds a constant per iteration, which the table states
in closed form
(`%r1443 = 8 i`, `%r1442 = 32768 i`, `%r1441 = 128 (num_splits i + ctaid.x)`, all modulo
`2 ^ 32`). The ring is `i % 3` and the parity `1 - (i / 3) % 2`, which the code computes
by `mul.hi.s32` with `1431655766` and `mad.lo` with `-24` and `-98304`: for a counter below
`2 ^ 31` they are exact (`LoaderRing`); for a larger word the code's slot remainder is in
`-2 … 0` (`Loader.remI`). The registers the role inherits from the dispatch
and the prologue are `pro` (`Pro.val`): the registers the loop reads are numbers (the strides
`%r67 … %r71`, `%r5 = %r71 << 7`, the block-table base `%rd72`, the thread index `%r1`); the
others are carried unchanged (`Pro.rest`).

The machine follows every loaded value: a `(num_pre, num_iters)` element that the code cannot
read as bits faults at the compare after the named barrier (`none` at `bar0`), a load whose bytes
do not rebuild faults (`none`), and a block-table word is followed for every value. The facts
about the whole execution (the default partition's write of `(num_pre, num_iters)`, the block
table's contents) are the protocol layer's; `Rng` states the counter bounds they give. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-! ### The event instructions of the loader -/

/-- The event instructions of the loader (the 26 sites of `Flow.Sites` at pcs 2344 to 2420,
with the two elements of the vector load told apart). -/
inductive Site where
  | setMaxDec
  /-- Element 0 of `ld.shared.v2.b32 {num_pre, num_iters}`. -/
  | ld0
  /-- Element 1 of the same load (`sub = 1`, `acc = [num_pre]`). -/
  | ld1
  | bar0
  /-- The poll of the slot's `kv_empty` barrier. -/
  | wait
  | wb0
  /-- The arrival on the slot's `kv_ready` barrier (lane 0). -/
  | arrive
  | ldb0
  | wb1
  | el0 | cp0a | cp0b
  | wb2
  | el1 | cp1a | cp1b
  | ldb1
  | wb3
  | el2 | cp2a | cp2b
  | wb4
  | el3 | cp3a | cp3b
  | bar1
  | setMaxInc
  deriving DecidableEq

def Site.pc : Site → Nat
  | .setMaxDec => Flow.setMaxReg_5
  | .ld0 | .ld1 => Flow.load_204
  | .bar0 => Flow.bar_28
  | .wait => Flow.mbarWait_2
  | .wb0 => Flow.warpBar_0
  | .arrive => Flow.mbarArrive_4
  | .ldb0 => Flow.load_205
  | .wb1 => Flow.warpBar_1
  | .el0 => Flow.elect_24 | .cp0a => Flow.tensorCopy_12 | .cp0b => Flow.tensorCopy_13
  | .wb2 => Flow.warpBar_2
  | .el1 => Flow.elect_25 | .cp1a => Flow.tensorCopy_14 | .cp1b => Flow.tensorCopy_15
  | .ldb1 => Flow.load_206
  | .wb3 => Flow.warpBar_3
  | .el2 => Flow.elect_26 | .cp2a => Flow.tensorCopy_16 | .cp2b => Flow.tensorCopy_17
  | .wb4 => Flow.warpBar_4
  | .el3 => Flow.elect_27 | .cp3a => Flow.tensorCopy_18 | .cp3b => Flow.tensorCopy_19
  | .bar1 => Flow.bar_29
  | .setMaxInc => Flow.setMaxReg_6

/-- The sites of the iteration loop. -/
def Site.inLoop : Site → Bool
  | .setMaxDec | .ld0 | .ld1 | .bar0 | .bar1 | .setMaxInc => false
  | _ => true

/-! ### The inherited registers -/

/-- What the loop reads of the registers the role inherits: the strides and counts the
prologue loaded from the parameters (`%r67 … %r71`; `%r5` is `%r71 << 7`), the base of the
block table (`%rd72`), and the thread index (`%r1`, from `L` and `g`). The other inherited
registers (`%p3`, `%r2 … %r4`, `%r73`, `%rd1`) are carried unchanged (`rest`). -/
structure Pro where
  rest : Nat → Value
  w67 : Nat
  w68 : Nat
  w69 : Nat
  w70 : Nat
  w71 : Nat
  bt : Nat

/-- The registers of `Pro`, as a table. -/
def Pro.table (L : Launch) (g : Nat) (P : Pro) : List (Nat × Value) :=
  [(462, b32 (g % L.block)), (466, b32 (P.w71 * 128 % 2 ^ 32)), (528, b32 P.w67),
   (529, b32 P.w68), (530, b32 P.w69), (531, b32 P.w70), (532, b32 P.w71), (2020, b64 P.bt)]

def Pro.val (L : Launch) (g : Nat) (P : Pro) (r : Nat) : Value :=
  ((P.table L g).lookup r).getD (P.rest r)

/-- The 32 low bits of a stored register value, as a number. -/
def natOf : Value → Nat
  | .bits _ x => x.toNat % 2 ^ 32
  | _ => 0

/-- The 64 bits of a stored register value, as a number. -/
def natOf64 : Value → Nat
  | .bits _ x => x.toNat
  | _ => 0

/-- A 32-bit two's complement word `x` sign-extended to 64 bits, as a number. -/
def sx32 (x : Nat) : Nat := x % 2 ^ 32 + x % 2 ^ 32 / 2 ^ 31 * (2 ^ 64 - 2 ^ 32)

/-! ### The code's integer operations on the ring registers

The registers that depend on the ring slot `i % 3` are stated as the code's terms: each
function mirrors the evaluator's rule for one 32-bit instruction on the stored bits of its
operands (`rdW` is the read of a register: its low 32 bits), so that a segment's computed value
and the table's agree by unfolding. `LoaderRing` says what they mean for a counter below
`2 ^ 31` (`quotW_eq`, `slotW_eq`, `parity_eq`, …). -/

/-- The 32-bit read of a register's stored bits. -/
abbrev rdW (x : BitVec 64) : BitVec 64 := truncBits 32 x
/-- `add.s32`. -/
def addW (a b : BitVec 64) : BitVec 64 := truncBits 32 (rdW a + rdW b)
/-- `mad.lo.s32`. -/
def madLoW (a b c : BitVec 64) : BitVec 64 := truncBits 32 (rdW a * rdW b + rdW c)
/-- `2 ^ 32` as an `Int` with the core's power instance, the one the evaluator's terms carry. -/
abbrev pow32 : Int :=
  @HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow)) 2 32
/-- `mul.hi.s32`. -/
def mulHiW (a b : BitVec 64) : BitVec 64 :=
  truncBits 32 (BitVec.ofInt 64 (toSigned 32 (rdW a) * toSigned 32 (rdW b) / pow32))
/-- `shr.u32` by a register or an immediate. -/
def shrW (a s : BitVec 64) : BitVec 64 := if (rdW s).toNat ≥ 32 then 0 else rdW a >>> (rdW s).toNat
/-- `not.b32`. -/
def notW (a : BitVec 64) : BitVec 64 := truncBits 32 (~~~ rdW a)
/-- `and.b32`. -/
def andW (a b : BitVec 64) : BitVec 64 := rdW a &&& rdW b

/-- `2 ^ n` as an `Int` with the core's power instance. -/
abbrev pw (n : Nat) : Int :=
  @HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow)) 2 n
/-- `shr.s32` by an immediate. -/
def sarW (a s : BitVec 64) : BitVec 64 :=
  truncBits 32 (BitVec.ofInt 64 (toSigned 32 (rdW a) / pw (min (rdW s).toNat 32)))
/-- `mad.wide.s32`: the signed product of two 32-bit words plus a 64-bit word. -/
def madWideW (a b c : BitVec 64) : BitVec 64 :=
  intBits 64 (intOf .s 32 (rdW a) * intOf .s 32 (rdW b) + intOf .s 64 (truncBits 64 c))
/-- `add.s64`. -/
def add64W (a b : BitVec 64) : BitVec 64 := truncBits 64 (truncBits 64 a + truncBits 64 b)

/-- The counter's low 32 bits as a signed integer. -/
def sxI (i : Nat) : Int := if i % 2 ^ 32 < 2 ^ 31 then ((i % 2 ^ 32 : Nat) : Int) else
  ((i % 2 ^ 32 : Nat) : Int) - 2 ^ 32

/-- The signed counter divided by 3, rounded toward zero. -/
def quoI (i : Nat) : Int := if 0 ≤ sxI i then sxI i / 3 else -((-sxI i) / 3)

/-- The slot remainder the code computes: the signed counter minus three times `quoI`. -/
def remI (i : Nat) : Int := sxI i - 3 * quoI i

/-- The register `%r138` (`mul.hi.s32` of the counter by `1431655766`, plus its sign bit). -/
def quotW (i : Nat) : BitVec 64 :=
  addW (mulHiW (BitVec.ofNat 64 i) (BitVec.ofInt 64 1431655766))
    (shrW (mulHiW (BitVec.ofNat 64 i) (BitVec.ofInt 64 1431655766)) (BitVec.ofInt 64 31))
/-- The slot offset registers `%r140` (`mad.lo` with `-24`) and `%r144` (with `-98304`), from the
registers `%r1443 = 8 i` and `%r1442 = 32768 i` (the table's closed forms). -/
def slotW (i : Nat) : BitVec 64 :=
  madLoW (quotW i) (BitVec.ofInt 64 (-24)) (BitVec.ofNat 64 (8 * i % 2 ^ 32))
def slotKW (i : Nat) : BitVec 64 :=
  madLoW (quotW i) (BitVec.ofInt 64 (-98304)) (BitVec.ofNat 64 (32768 * i % 2 ^ 32))
/-- The shared base: `mov.b32 %r141, global_smem`. -/
def baseW (L : Launch) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0))
/-- The shared base plus the slot offset. -/
def barW (L : Launch) (i : Nat) : BitVec 64 := addW (baseW L) (slotW i)
def kvW (L : Launch) (i : Nat) : BitVec 64 := addW (baseW L) (slotKW i)

/-- A thread's CTA coordinates (`%ctaid.x`, `.y`, `.z`), as the 32-bit words `mov.u32` makes
of them. -/
def ctaX (L : Launch) (g : Nat) : Nat := (L.ctaidOf (g / L.block)).get .x % 2 ^ 32
def ctaY (L : Launch) (g : Nat) : Nat := (L.ctaidOf (g / L.block)).get .y % 2 ^ 32
def ctaZ (L : Launch) (g : Nat) : Nat := (L.ctaidOf (g / L.block)).get .z % 2 ^ 32

/-! ### The states -/

/-- A loader state: the next event, the inherited registers, the loop counter, `num_iters`, the
two block-table words and whether the thread is lane 0 of its warp (`%p20`, which guards the
arrival; `Inv.ln` ties it to the thread's lane). -/
structure D where
  site : Site
  pro : Nat → Value
  i : Nat
  n : Nat
  p0 : Nat
  p1 : Nat
  ln : Bool

/-- The first state of the role, from the inherited registers `P`. -/
def D.start (L : Launch) (g : Nat) (P : Pro) : D :=
  ⟨.setMaxDec, Pro.val L g P, 0, 0, 0, 0, decide (laneOf L g = 0)⟩

/-- The registers of the loader at state `d`: the loop's, as functions of `d.i`, `d.n` and the
block-table words. The ring slot is `i % 3`; `r138 = i / 3`. -/
def table (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let w68 := natOf (d.pro 529)
  let w69 := natOf (d.pro 530)
  let w70 := natOf (d.pro 531)
  let w71 := natOf (d.pro 532)
  let w67 := natOf (d.pro 528)
  let bt := natOf64 (d.pro 2020)
  let r1441 := 128 * ((w71 * d.i + ctaX L g) % 2 ^ 32) % 2 ^ 32
  let rd2 := (bt + 4 * sx32 (w67 * ctaZ L g)) % 2 ^ 64
  let rd105 := madWideW (sarW (BitVec.ofNat 64 r1441) (BitVec.ofInt 64 6)) (BitVec.ofInt 64 4)
    (BitVec.ofNat 64 rd2)
  [(19, .pred (decide (sxI d.n ≤ sxI d.i))), (25, .pred (decide (d.n ≠ d.i % 2 ^ 32))),
   (20, .pred d.ln),
   (21, .pred true), (22, .pred true), (23, .pred true), (24, .pred true),
   (469, b32 (g % L.block % 32)),
   (1904, b32 (8 * d.i % 2 ^ 32)), (1903, b32 (32768 * d.i % 2 ^ 32)),
   (1902, b32 r1441),
   (470, b32 (w69 * ctaY L g % 2 ^ 32)), (583, b32 (w70 * ctaY L g % 2 ^ 32)),
   (586, b32 ((w70 * ctaY L g + 64) % 2 ^ 32)), (588, b32 ((w70 * ctaY L g + 128) % 2 ^ 32)),
   (590, b32 ((w70 * ctaY L g + 192) % 2 ^ 32)),
   (599, .bits 32 (quotW d.i)), (602, .bits 32 (baseW L)), (603, .bits 32 (barW L d.i)),
   (578, .bits 32 (addW (barW L d.i) (BitVec.ofInt 64 213248))),
   (579, .bits 32 (andW (notW (quotW d.i)) (BitVec.ofInt 64 1))),
   (580, .bits 32 (addW (barW L d.i) (BitVec.ofInt 64 213216))),
   (582, .bits 32 (kvW L d.i)),
   (585, .bits 32 (addW (kvW L d.i) (BitVec.ofInt 64 16384))),
   (587, .bits 32 (addW (kvW L d.i) (BitVec.ofInt 64 98304))),
   (589, .bits 32 (addW (kvW L d.i) (BitVec.ofInt 64 114688))),
   (592, .bits 32 (addW (kvW L d.i) (BitVec.ofInt 64 8192))),
   (594, .bits 32 (addW (kvW L d.i) (BitVec.ofInt 64 24576))),
   (595, .bits 32 (addW (kvW L d.i) (BitVec.ofInt 64 106496))),
   (596, .bits 32 (addW (kvW L d.i) (BitVec.ofInt 64 122880))),
   (584, b32 ((d.p0 * w68 + w69 * ctaY L g) % 2 ^ 32)),
   (593, b32 ((d.p1 * w68 + w69 * ctaY L g) % 2 ^ 32)),
   (1950, b64 rd2), (2053, .bits 64 rd105),
   (2054, .bits 64 (add64W rd105 (BitVec.ofInt 64 4))),
   (468, b32 (ctaX L g)), (577, b32 ((w71 * d.i + ctaX L g) % 2 ^ 32)),
   (597, .bits 32 (mulHiW (BitVec.ofNat 64 d.i) (BitVec.ofInt 64 1431655766)))]

/-- The value of register `r` at state `d`: the loop's table, else the inherited one. -/
def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((table L g d).lookup r).getD (d.pro r)

/-- The registers live at `pc`, with their values in state `d`. -/
def factsAt (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

/-- The sites whose `num_iters` is bounded (the compare of the loop's entry, and the loop). -/
def Site.bounded : Site → Bool
  | .bar0 => true
  | s => s.inLoop

/-- The sites whose counter is bounded: those, and the second element of the vector load. -/
def Site.iBounded : Site → Bool
  | .ld1 => true
  | s => s.bounded

/-- The registers of a loader state: the inherited ones `P`, except `%r1444` and `%r6`, which hold
the two loaded values (`vi`, `vn`) and, from the end of the first iteration on, the counter. -/
def Pro.valW (L : Launch) (g : Nat) (P : Pro) (vi vn : Value) (r : Nat) : Value :=
  if r = 1905 then vi else if r = 467 then vn else Pro.val L g P r

/-- The registers of a loader state are the inherited `P`'s, except the two loaded words. -/
def ProEq (L : Launch) (g : Nat) (P : Pro) (d : D) : Prop :=
  ∀ r, r ≠ 1905 → r ≠ 467 → d.pro r = Pro.val L g P r

/-- The loaded counter register. -/
def wordI (d : D) : Value := d.pro 1905

/-- The loaded `num_iters` register. -/
def wordN (d : D) : Value := d.pro 467

/-- The loader's states: the inherited registers are `Pro`'s except the two loaded words; the
counters are the numbers the code reads the loaded words as (`Raw.word32Of`); in the loop the code
can read both, the counter register holds the counter modulo `2 ^ 32` (the machine counts the
iterations without wrapping, the register wraps), the counter register is not `num_iters`, and the
counter is less than `2 ^ 32` iterations past `num_iters`; `ln` is whether the thread is lane 0,
and lane 0 only is at the arrival. -/
structure Inv (L : Launch) (g : Nat) (d : D) : Prop where
  pro : ∃ P : Pro, ProEq L g P d
  wi : d.site = .ld1 ∨ d.site = .bar0 → (Raw.word32Of (wordI d)).getD 0 = d.i
  wn : d.site.bounded = true → (Raw.word32Of (wordN d)).getD 0 = d.n
  bits : d.site.inLoop = true → Raw.word32Of (wordI d) = some (d.i % 2 ^ 32) ∧
    Raw.word32Of (wordN d) = some d.n
  loop : d.site.inLoop = true → d.i % 2 ^ 32 ≠ d.n ∧ d.i < 2 ^ 32 + d.n
  ln : d.ln = decide (laneOf L g = 0)
  lane : d.site = .arrive → d.ln = true

/-- **The counter bounds of a state**: the counters are below `2 ^ 31` from the second load on,
the counter is below `num_iters` in the loop, and the two loaded words read as the counters. They
are not facts of the machine (it follows every loaded word); they hold in a consistent execution,
where the loaded words are the launch's (`Interface.LdRng`). -/
structure Rng (d : D) : Prop where
  bndI : d.site.iBounded = true → d.i < 2 ^ 31
  bndN : d.site.bounded = true → d.n < 2 ^ 31
  loop : d.site.inLoop = true → d.i < d.n
  wi : d.site.iBounded = true → Raw.word32Of (wordI d) = some d.i
  wn : d.site.bounded = true → Raw.word32Of (wordN d) = some d.n

/-! ### The abstract successor -/

/-- The state after the last copy of an iteration: the counter counts one more iteration, the
counter register holds it as a 32-bit word (it wraps); the next iteration, or the exit barrier
when the register is `num_iters`. -/
def afterIter (d : D) : D :=
  let i' := d.i + 1
  let pro' := Function.update d.pro 1905 (b32 (i' % 2 ^ 32))
  if d.n = i' % 2 ^ 32 then { d with site := .bar1, pro := pro', i := i' }
  else { d with site := .wait, pro := pro', i := i' }

/-- The state after the first element of the vector load: the counter register holds the loaded
value, and the counter is the number it reads as. -/
def readI (d : D) (v : Value) : D :=
  { d with site := .ld1, pro := Function.update d.pro 1905 v, i := (Raw.word32Of v).getD 0 }

/-- The state after the second element: the `num_iters` register holds the loaded value. -/
def readN (d : D) (v : Value) : D :=
  { d with site := .bar0, pro := Function.update d.pro 467 v, n := (Raw.word32Of v).getD 0 }

/-- The abstract successor after event `e`. The elected lane of an `elect.sync` goes on to the
guarded copies, the other lanes skip them; lane 0 goes on to the arrival, the other lanes skip
it. A failed poll returns to the poll. A load whose bytes do not rebuild faults (`none`). Every
loaded word is followed: the two counter words are kept as loaded and read as bits at the compare
after the named barrier, where a word without bits faults (`none`); a block-table word is read as
bits by the instruction after its load, and a word without bits faults there (`none`). -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .setMaxDec => some (some { d with site := .ld0 })
  | .ld0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v => some (some (readI d v))
      | .error _ => none
    | _ => none
  | .ld1 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v => some (some (readN d v))
      | .error _ => none
    | _ => none
  | .bar0 =>
    match Raw.word32Of (wordI d), Raw.word32Of (wordN d) with
    | some _, some _ =>
      some (some (if sxI d.n ≤ sxI d.i then { d with site := .bar1 }
        else { d with site := .wait }))
    | _, _ => none
  | .wait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .wb0 } else d))
    | _ => none
  | .wb0 => some (some { d with site := if d.ln then .arrive else .ldb0 })
  | .arrive => some (some { d with site := .ldb0 })
  | .ldb0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v => match Raw.word32Of v with
        | some x => some (some { d with site := .wb1, p0 := x })
        | none => none
      | .error _ => none
    | _ => none
  | .wb1 => some (some { d with site := .el0 })
  | .el0 =>
    match e.kind with
    | .elect _ _ ld => some (some { d with site := if laneOf L g = ld then .cp0a else .wb2 })
    | _ => none
  | .cp0a => some (some { d with site := .cp0b })
  | .cp0b => some (some { d with site := .wb2 })
  | .wb2 => some (some { d with site := .el1 })
  | .el1 =>
    match e.kind with
    | .elect _ _ ld => some (some { d with site := if laneOf L g = ld then .cp1a else .ldb1 })
    | _ => none
  | .cp1a => some (some { d with site := .cp1b })
  | .cp1b => some (some { d with site := .ldb1 })
  | .ldb1 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v => match Raw.word32Of v with
        | some x => some (some { d with site := .wb3, p1 := x })
        | none => none
      | .error _ => none
    | _ => none
  | .wb3 => some (some { d with site := .el2 })
  | .el2 =>
    match e.kind with
    | .elect _ _ ld => some (some { d with site := if laneOf L g = ld then .cp2a else .wb4 })
    | _ => none
  | .cp2a => some (some { d with site := .cp2b })
  | .cp2b => some (some { d with site := .wb4 })
  | .wb4 => some (some { d with site := .el3 })
  | .el3 =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (if laneOf L g = ld then { d with site := .cp3a } else afterIter d))
    | _ => none
  | .cp3a => some (some { d with site := .cp3b })
  | .cp3b => some (some (afterIter d))
  | .bar1 => some (some { d with site := .setMaxInc })
  | .setMaxInc => some none

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
