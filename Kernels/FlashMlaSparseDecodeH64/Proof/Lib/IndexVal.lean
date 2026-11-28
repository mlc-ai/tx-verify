-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexSites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Entry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Arith
public import Lemmas.Flow.DivStep
public import Lemmas.Flow.OrRaw

@[expose] public section

/-! # The index warp's control words, register table and first event

A state of the index warp's control machine (`Index/Machine.lean`) carries the control words
`IxCtl`: the two lengths (`l0`, `l1`: `%r2968`, `%r2969`, the parameters unless a length pointer
is set, then the loaded word), the main loop's block counter and negative counter (`cnt`, `neg`:
`%r2972`, `%r2970`), the ring's slot and parity (`slot`, `par`: `%r2977`, `%rs456`, shared by the
two loops; the code keeps them in `0..3` and `0..1`, so they are a `Fin 4` and a `Bool`: a step
proof splits on them where the code `selp`s on them, and every slot and parity word is a
literal), and the extra loop's block counter and negative counter (`xb`, `xn`: `%r2980`, which
starts as the main cache's block count, and `%r2978`). `ixVals` states each control register as
the code's term over the launch, the parameters and these words.

`ixFirst`: the warp's first event after the parameter prefix (pcs 2332–2359), which warpgroup 1's
head walks: the return for a CTA beyond the batch, else the first length load a set pointer asks
for, else the lengths are the parameters and the code's tests on them decide (`ixLens`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The index warp's control words. -/
structure IxCtl where
  l0 : BitVec 64 := 0
  l1 : BitVec 64 := 0
  cnt : BitVec 64 := 0
  neg : BitVec 64 := 0
  slot : Fin 4 := 0
  par : Bool := false
  xb : BitVec 64 := 0
  xn : BitVec 64 := 0
  /-- The main loop's position word (`%r2513`), its pair load's address (`%rd1040`) and the
  extra loop's position word (`%r2521`): set to their first values at the loops' entries,
  advanced by the code's own operations at a block's end. -/
  wpos : BitVec 64 := 0
  aptr : BitVec 64 := 0
  xa : BitVec 64 := 0
  /-- The main loop's current pair (`%r2516`, `%r2515`: `m0`, `m1`) and next pair (`%r2518`,
  `%r2517`: `n0`, `n1`), and the extra loop's (`%r2524`, `%r2523`: `e0`, `e1`; `%r2526`,
  `%r2525`: `f0`, `f1`): the words the pair loads returned. -/
  m0 : BitVec 64 := 0
  m1 : BitVec 64 := 0
  n0 : BitVec 64 := 0
  n1 : BitVec 64 := 0
  e0 : BitVec 64 := 0
  e1 : BitVec 64 := 0
  f0 : BitVec 64 := 0
  f1 : BitVec 64 := 0
  /-- The words the block's two shuffles received (`%r149`, `%r152` of the code's names; the
  registers 607 and 610, 646 and 649 of the extra loop): the partner lanes' sent words, kept raw
  because the machine does not know a received value to be a 32-bit word. -/
  rv1 : Value := .pred false
  rv2 : Value := .pred false

/-! ### The code's terms -/

/-- The padded length (pcs 2366–2370, 2372–2376), its floor at 64 (`%r568`), the padded total
(`%r576`), the block count (`%r503`), the main cache's block count (`%r2980`) and the main loop's
(`%r504`). -/
abbrev ixPad (a : BitVec 64) : BitVec 64 :=
  andi (add32 (addi a 63) (shru (shrs (addi a 63) 31) 26)) (-64)
abbrev ixMax (a : BitVec 64) : BitVec 64 := max32 (ixPad a) (i32 64)
abbrev ixTot (a b : BitVec 64) : BitVec 64 :=
  add32 (add32 (addi b 63) (ixMax a)) (sub32 (ixPad b) (addi b 63))
abbrev ixNblk (a b : BitVec 64) : BitVec 64 :=
  shrs (add32 (ixTot a b) (shru (shrs (ixTot a b) 31) 26)) 6
abbrev ixNmain (a : BitVec 64) : BitVec 64 := shru (ixMax a) 6
abbrev ixNmin (a b : BitVec 64) : BitVec 64 := min32 (ixNmain a) (ixNblk a b)

/-- The lane (`%r466`), the lane's coordinate pair in a slot (`%r505`), a slot's barrier base
(`%r507`, `%r510`), the parity word of a wait (`%r586`), and whether the lane skips the validity
byte (`%p20`, `%p35`: not `0 mod 4`). -/
abbrev ixLane (L : Launch) (g : Nat) : BitVec 64 := andi (tw L g) 31
abbrev ixRowB (L : Launch) (g : Nat) : BitVec 64 := add32 (sbw L) (shl (ixLane L g) 3)
abbrev ixSlotW (s : Fin 4) : BitVec 64 := i32 (s.val : Int)
@[reducible] def ixParB : Bool → BitVec 64
  | true => i16 1
  | false => i16 0
abbrev ixSlotB (L : Launch) (s : Fin 4) : BitVec 64 := add32 (sbw L) (shl (ixSlotW s) 3)
abbrev ixParW (p : Bool) : BitVec 64 := andi (zext16w (xor16 (ixParB p))) 255
abbrev ixSkipB (L : Launch) (g : Nat) : Bool := scmpi .ne .b (andi (tw L g) 3) 0

/-- The index rows' words (pcs 2335–2393, 2410–2413, 2504–2507): the CTA's offsets into the two
index arrays (`%rd24`, `%rd25`), a block's token row stride (`%r48`, `%r51`: the block stride
divided by 528) and the first pair loads' addresses (`%rd44`, `%rd52`). -/
abbrev ixCtaX (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (ctaidX L g)
abbrev ixRow0 (P : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  add64 (sext (mul32 (pw P.topk) (ixCtaX L g))) (sext (mul32 (pw (P.s_q * P.topk)) (r2W L g)))
abbrev ixRow1 (P : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  add64 (pw8 P.extraIndicesBase) (shl64 (add64 (sext (mul32 (pw P.extra_topk) (ixCtaX L g)))
    (mulWideR .s (pw (P.s_q * P.extra_topk)) (r2W L g))) 2)
abbrev ixDiv528 (x : BitVec 64) : BitVec 64 :=
  add32 (shrs (mulhi x 1041204193) 7) (shru (mulhi x 1041204193) 31)
abbrev ixLane2 (L : Launch) (g : Nat) : BitVec 64 := shl (ixLane L g) 1
abbrev ixAddr0 (P : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  add64 (add64 (pw8 P.indicesBase) (shl64 (ixRow0 P L g) 2)) (mulWide .u (ixLane2 L g) 4)
abbrev ixAddr1 (P : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  add64 (ixRow1 P L g) (mulWide .u (ixLane2 L g) 4)
/-- The first values of the loop words `wpos`, `aptr`, `xa` (pcs 2414–2419, 2508). -/
abbrev ixPos0 (L : Launch) (g : Nat) : BitVec 64 := addi (ixLane2 L g) 1
abbrev ixApB (P : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  add64 (add64 (mulWide .u (ixLane L g) 8) (shl64 (ixRow0 P L g) 2)) (pw8 P.indicesBase)
abbrev ixAp0 (P : Params) (L : Launch) (g : Nat) : BitVec 64 := addi64 (ixApB P L g) 256
abbrev ixXa0 (L : Launch) (g : Nat) : BitVec 64 := or32 (ixLane2 L g) (i32 64)

/-- The ring's parity after a block (pcs 2477–2481): it flips after slot 3. The slot advances
mod 4 (pcs 2482–2487). -/
def ixParNext (p : Bool) (s : Fin 4) : Bool := p != decide (s = 3)

/-! ### The register table -/

section
variable (P : Params) (L : Launch) (g : Nat) (c : IxCtl)

/-- The launch's and the set-up's control registers: the lane's words, the length pointers and
addresses, the lengths and block counts, and the branch predicates on them. -/
def ixSetup : List (Nat × Value) :=
  [(460, w32 (r2W L g)), (466, w32 (ixLane L g)), (2991, .ptr 64 false (.param (param "0")) 0),
   (459, w32 (BitVec.ofNat 64 (ctaidX L g))), (461, w32 (tw L g)), (559, w32 (pw P.b)),
   (499, w32 (shl (ixLane L g) 3)), (500, w32 (andi (tw L g) 3)),
   (498, w32 (andi (shl (tw L g) 1) 6)),
   (501, w32 (shru (ixLane L g) 2)), (505, w32 (ixRowB L g)),
   (20, .pred (ixSkipB L g)), (35, .pred (ixSkipB L g)),
   (14, .pred (scmp .ge .s (r2W L g) (pw P.b))),
   (3009, .bits 64 (pw8 (P.topkLenBase.getD 0))),
   (15, .pred (eqz64 (pw8 (P.topkLenBase.getD 0)))),
   (3010, .bits 64 (pw8 (P.extraTopkLenBase.getD 0))),
   (16, .pred (eqz64 (pw8 (P.extraTopkLenBase.getD 0)))),
   (3023, .bits 64 (add64 (pw8 (P.topkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (3025, .bits 64 (add64 (pw8 (P.extraTopkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (2968, w32 c.l0), (2969, w32 c.l1), (503, w32 (ixNblk c.l0 c.l1)),
   (504, w32 (ixNmin c.l0 c.l1)),
   (17, .pred (scmpi .lt .s (ixNmin c.l0 c.l1) 1)), (18, .pred (scmpi .lt .s (ixNmin c.l0 c.l1) 1)),
   (659, w32 (i32 12)), (660, w32 (i32 384)),
   (490, w32 (pw P.blockStride)), (491, w32 (pw P.extraBlockStride)),
   (492, w32 (pw (P.s_q * P.topk))), (493, w32 (mul32 (pw P.topk) (ixCtaX L g))),
   (494, w32 (pw (P.s_q * P.extra_topk))), (495, w32 (mul32 (pw P.extra_topk) (ixCtaX L g))),
   (496, w32 (ixLane2 L g)), (560, w32 (pw P.topk)), (561, w32 (pw P.extra_topk)),
   (497, w32 (pw P.page)),
   (502, w32 (pw P.extraPage)), (506, w32 (ixDiv528 (pw P.blockStride))),
   (509, w32 (ixDiv528 (pw P.extraBlockStride))),
   (3011, .bits 64 (pw8 P.indicesBase)), (3012, .bits 64 (pw8 P.extraIndicesBase)),
   (3013, .bits 64 (ixRow0 P L g)), (3014, .bits 64 (ixRow1 P L g)),
   (3033, .bits 64 (ixAddr0 P L g)), (3041, .bits 64 (ixAddr1 P L g))]

/-- The loops' control registers: counters, slot and parity, the waits' and arrivals' words, the
store addresses and the back-edges' tests. -/
def ixLoop : List (Nat × Value) :=
  [(456, .bits 16 (ixParB c.par)), (2977, w32 (ixSlotW c.slot)), (2970, w32 c.neg),
   (2972, w32 c.cnt),
   (2980, w32 c.xb), (2978, w32 c.xn),
   (19, .pred (scmp .ge .s c.cnt (ixNmin c.l0 c.l1))), (31, .pred (scmpi .ne .b c.neg 0)),
   (32, .pred (scmp .ge .s c.xb (ixNblk c.l0 c.l1))),
   (33, .pred (scmp .ge .s c.xb (ixNblk c.l0 c.l1))),
   (34, .pred (scmp .ge .s c.xb (ixNblk c.l0 c.l1))), (46, .pred (scmpi .ne .b c.xn 0)),
   (507, w32 (ixSlotB L c.slot)), (510, w32 (ixSlotB L c.slot)),
   (585, w32 (addi (ixSlotB L c.slot) 222872)), (623, w32 (addi (ixSlotB L c.slot) 222872)),
   (586, w32 (ixParW c.par)), (624, w32 (ixParW c.par)),
   (587, w32 (i32 10000000)), (625, w32 (i32 10000000)),
   (612, w32 (add32 (ixRowB L g) (shl (ixSlotW c.slot) 8))),
   (651, w32 (add32 (ixRowB L g) (shl (ixSlotW c.slot) 8))),
   (613, w32 (add32 (ixSlotB L c.slot) (shru (ixLane L g) 2))),
   (652, w32 (add32 (ixSlotB L c.slot) (shru (ixLane L g) 2))),
   (614, w32 (addi (ixSlotB L c.slot) 222840)), (653, w32 (addi (ixSlotB L c.slot) 222840)),
   (2979, w32 c.xa)]

/-- The extra loop's next pair's address (`%rd54`, pcs 2515–2516) for the position word `x`. -/
abbrev ixXad (x : BitVec 64) : BitVec 64 := add64 (ixRow1 P L g) (mulWide .u x 4)

/-- The loops' position words and next pairs' addresses. -/
def ixMainW : List (Nat × Value) :=
  [(2971, w32 c.wpos), (4029, .bits 64 c.aptr), (3043, .bits 64 (ixXad P L g c.xa))]

/-- The coordinate word the code stores for an index word `x` with the page size `pg`, the block's
token rows `bs` and the validity `ok` of its position: `x / pg * bs + (x - x / pg * pg)`, else
`-1` (pcs 2453-2454, 2460-2461, 2541-2542, 2549-2550). -/
abbrev ixCoord (x pg bs : BitVec 64) (ok : Bool) : BitVec 64 :=
  sel ok (mad32 (divu32 x pg) bs (sub32 x (mul32 (divu32 x pg) pg))) (i32 (-1))

/-- The validity of a main word at position `p`: the index is not `-1` and `p` is below the
length (pcs 2449-2451, 2455-2457). -/
abbrev ixOk (x p len : BitVec 64) : Bool := scmpi .ne .b x (-1) && scmp .lt .s p len

/-- The index pairs' words and what the code computes from them across an event: the positions
below the lengths (`%r588`, `%r626`), the quotients and remainders by the page size (pcs
2432-2437, 2520-2525) and the two stored coordinates (`%r142`, `%r146` and their extra twins). -/
def ixPairs : List (Nat × Value) :=
  [(2974, w32 c.m0), (2973, w32 c.m1), (2976, w32 c.n0), (2975, w32 c.n1),
   (2982, w32 c.e0), (2981, w32 c.e1), (2984, w32 c.f0), (2983, w32 c.f1),
   (588, w32 (addi c.wpos (-1))),
   (589, w32 (divu32 c.m0 (pw P.page))), (592, w32 (divu32 c.m1 (pw P.page))),
   (591, w32 (sub32 c.m0 (mul32 (divu32 c.m0 (pw P.page)) (pw P.page)))),
   (594, w32 (sub32 c.m1 (mul32 (divu32 c.m1 (pw P.page)) (pw P.page)))),
   (600, w32 (ixCoord c.m0 (pw P.page) (ixDiv528 (pw P.blockStride))
     (ixOk c.m0 (addi c.wpos (-1)) c.l0))),
   (604, w32 (ixCoord c.m1 (pw P.page) (ixDiv528 (pw P.blockStride)) (ixOk c.m1 c.wpos c.l0))),
   (626, w32 (addi c.xa (-64))),
   (627, w32 (divu32 c.e0 (pw P.extraPage))), (630, w32 (divu32 c.e1 (pw P.extraPage))),
   (629, w32 (sub32 c.e0 (mul32 (divu32 c.e0 (pw P.extraPage)) (pw P.extraPage)))),
   (632, w32 (sub32 c.e1 (mul32 (divu32 c.e1 (pw P.extraPage)) (pw P.extraPage)))),
   (638, w32 (ixCoord c.e0 (pw P.extraPage) (ixDiv528 (pw P.extraBlockStride))
     (ixOk c.e0 (addi c.xa (-64)) c.l1))),
   (643, w32 (ixCoord c.e1 (pw P.extraPage) (ixDiv528 (pw P.extraBlockStride))
     (ixOk c.e1 (addi c.xa (-63)) c.l1)))]

/-- The first and second positions' tests of the main loop's lane, of the extra loop's. -/
abbrev okM0 (c : IxCtl) : Bool := ixOk c.m0 (addi c.wpos (-1)) c.l0
abbrev okM1 (c : IxCtl) : Bool := ixOk c.m1 c.wpos c.l0
abbrev okE0 (c : IxCtl) : Bool := ixOk c.e0 (addi c.xa (-64)) c.l1
abbrev okE1 (c : IxCtl) : Bool := ixOk c.e1 (addi c.xa (-63)) c.l1

/-- The validity bits of a lane's pair of positions, shifted to its place in the quad's byte
(`%r140`-`%r147` of the code: `selp` 1 or 0 on the first position's test, 2 or 0 on the second's,
their `or`, shifted left by twice the lane's place in its quad (`%r498`)). -/
abbrev ixQuadW (L : Launch) (g : Nat) (a b : Bool) : BitVec 64 :=
  shlr (or32 (sel b (i32 2) (i32 0)) (sel a (i32 1) (i32 0))) (andi (shl (tw L g) 1) 6)

/-- The shuffled words and the validity byte (pcs 2462-2474, 2551-2563): the lane's shifted bits
(`%r605`, `%r644`), the word its first shuffle sends (`cvt.s32.s8` of it: `%r606`, `%r645`), the
word after the first received word (`%r608`, `%r647`) and the word its second shuffle sends
(`%r609`, `%r648`), and the byte the quad's lane stores (`%r508`, `%r511`). -/
def ixQuad : List (Nat × Value) :=
  let a := ixQuadW L g (okM0 c) (okM1 c)
  let x := ixQuadW L g (okE0 c) (okE1 c)
  [(598, w32 (sel (okM0 c) (i32 1) (i32 0))), (601, w32 (sel (okM1 c) (i32 2) (i32 0))),
   (602, w32 (or32 (sel (okM1 c) (i32 2) (i32 0)) (sel (okM0 c) (i32 1) (i32 0)))),
   (636, w32 (sel (okE0 c) (i32 1) (i32 0))), (640, w32 (sel (okE1 c) (i32 2) (i32 0))),
   (641, w32 (or32 (sel (okE1 c) (i32 2) (i32 0)) (sel (okE0 c) (i32 1) (i32 0)))),
   (605, w32 a), (606, cvts8 a), (608, w32 (or32 (rvw c.rv1) a)),
   (609, cvts8 (or32 (rvw c.rv1) a)), (508, w32 (or32 (or32 (rvw c.rv1) a) (rvw c.rv2))),
   (644, w32 x), (645, cvts8 x), (647, w32 (or32 (rvw c.rv1) x)),
   (648, cvts8 (or32 (rvw c.rv1) x)), (511, w32 (or32 (or32 (rvw c.rv1) x) (rvw c.rv2)))]

/-- **The register table.** -/
def ixVals : List (Nat × Value) :=
  ixLoop L g c ++ ixSetup P L g c ++ ixMainW P L g c ++ ixPairs P c ++ ixQuad L g c

/-- The value of register `r` for the control words `c`. A `match` rather than `Option.getD`: two
tables' values are compared after the lookups reduce, not by their lists' remaining entries. -/
def ixVal (r : Nat) : Value :=
  match (ixVals P L g c).lookup r with
  | some v => v
  | none => .pred false

/-- The facts at site `s` with the control words `c`: the control registers live there. -/
abbrev ixFacts (s : IxSite) : List (Nat × Value) := factsFrom (ixLive s.pc) (ixVal P L g c)
end

/-! ### The first event -/

/-- After the main cache's blocks (pcs 2495–2503; the extra loop's current pair is zeroed at
pcs 2496-2497): named barrier 12 when the extra cache has no block, else the extra cache's first
index pair. -/
@[irreducible] def ixMainDone (c : IxCtl) : IxSite × IxCtl :=
  let c1 := { c with e0 := 0, e1 := 0 }
  if scmp .ge .s c.xb (ixNblk c.l0 c.l1) then (.bar, c1) else (.xpre, c1)

/-- The main loop skipped (pcs 2406–2409): the ring at slot 0, parity 0. -/
@[irreducible] def ixNoMain (c : IxCtl) : IxSite × IxCtl :=
  ixMainDone { c with slot := 0, par := false }

/-- After the lengths (pcs 2366–2398): the extra loop's counter starts as the main cache's block
count, the main loop's current pair is zero (pcs 2396-2397); the first index pair when the main
loop has a block. -/
@[irreducible] def ixLens (c : IxCtl) : IxSite × IxCtl :=
  let c1 := { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 }
  if scmpi .lt .s (ixNmin c1.l0 c1.l1) 1 then ixNoMain c1 else (.pre, c1)

/-- After the first length (pcs 2361–2362): the second length's load if its pointer is set. -/
@[irreducible] def ixAfterA (P : Params) (c : IxCtl) : IxSite × IxCtl :=
  if eqz64 (pw8 (P.extraTopkLenBase.getD 0)) then ixLens c else (.lenB, c)

/-- The control words at the first event: the lengths are the parameters. -/
abbrev ixCtl0 (P : Params) : IxCtl where
  l0 := pw P.topk
  l1 := pw P.extra_topk

/-- **The index warp's first event** (pcs 2332–2359): the return beyond the batch, else the
length loads the set pointers ask for; the lengths start as the parameters. -/
@[irreducible] def ixFirst (P : Params) (L : Launch) (g : Nat) : IxSite × IxCtl :=
  let c : IxCtl := ixCtl0 P
  if scmp .ge .s (r2W L g) (pw P.b) then (.exit, c)
  else if eqz64 (pw8 (P.topkLenBase.getD 0)) then ixAfterA P c else (.lenA, c)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
