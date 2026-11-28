-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Sites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Live
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Entry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Arith
public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Arith32Wide

@[expose] public section

/-! # Warpgroup 0 as a control machine

One machine for the whole role (pcs 103–1841 and the `ret`), from its first event, the
`setmaxnreg` at pc 103. A state carries what decides control flow and the shapes of events:

* the site and the element of a vector access (`el`; the first element of a two-element shared
  read is the access's accumulator `a0`, a value the machine does not otherwise use);
* the two length words (`l0`, `l1`: `%r2423`, `%r2424`), loaded by `ld.global.nc` where their
  pointers are set, else the parameters;
* the block loop's registers: the negative block counter `cnt` (`%r2426`, from `1 - blocks` to
  `1`), the block number from one `bi` (`%r2425`), the valid-mask ring's slot and parity (`vs`,
  `%r2494`; `pv`, `%rs312`), the score ring's slot and parity (`sl`, `%r2495`; `ps`, `%rs313`) and
  the vote's result (`vt`, `%p1`).

The warp word `%r7` (the startup's second shuffle) is a parameter of the machine (`w`): the
startup records it, and the glue passes it.

Everything else is havocked: the data registers (`Live.lean`) are not stated, so the score words,
the peer reads, the row maxima and sums, the sink and the output words are free. The data loads
continue on any payload (bytes that do not rebuild fault in the concrete continuation, which the
UB-tolerant soundness `Flow.CodeU` admits); the length loads decide control and are followed on
their word. The one data branch (pc 1191: a zero row sum skips the normalization; both sides meet
at pc 1197 and write only data registers) is not a transition: the epilogue's segment over it is
a joined havoc segment.

The value table states each control register as the code's term over the launch, the
parameters, `w` and the fields. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- A state. -/
structure D where
  site : Site
  el : Nat := 0
  a0 : Value := .pred false
  l0 : BitVec 64 := 0
  l1 : BitVec 64 := 0
  cnt : BitVec 64 := 0
  bi : BitVec 64 := 0
  vs : BitVec 64 := 0
  pv : BitVec 64 := 0
  sl : BitVec 64 := 0
  ps : BitVec 64 := 0
  vt : Bool := false

/-! ### The code's terms -/

/-- The padded length `pad64 a` (pcs 171–175, 189–193). -/
abbrev pad (a : BitVec 64) : BitVec 64 :=
  andi (add32 (addi a 63) (shru (shrs (addi a 63) 31) 26)) (-64)
/-- `%r15`, the padded total, as the code computes it (pcs 189–197). -/
abbrev r15 (a b : BitVec 64) : BitVec 64 :=
  add32 (add32 (addi b 63) (max32 (pad a) (i32 64))) (sub32 (pad b) (addi b 63))
/-- `%r512`, the block count (pcs 236–239). -/
abbrev nblk (a b : BitVec 64) : BitVec 64 :=
  shrs (add32 (r15 a b) (shru (shrs (r15 a b) 31) 26)) 6

/-- `%r5`, `%r8`, `%r10`: the thread's index in its warpgroup, its lane, its head. -/
abbrev r5W (L : Launch) (g : Nat) : BitVec 64 := andi (tw L g) 127
abbrev r8W (L : Launch) (g : Nat) : BitVec 64 := andi (tw L g) 31
abbrev r10W (L : Launch) (g : Nat) : BitVec 64 := andi (tw L g) 63
/-- `%r13`, `%r14`: the thread's word of the row-exchange buffer and its partner's. -/
abbrev r13W (L : Launch) (g : Nat) : BitVec 64 := add32 (sbw L) (shl (r5W L g) 2)
abbrev r14W (L : Launch) (g : Nat) : BitVec 64 := add32 (sbw L) (xor32 (shl (r5W L g) 2) (i32 256))
/-- `%r16`: the thread's P-tile store base (pcs 211–221). -/
abbrev r16W (L : Launch) (g : Nat) (w : BitVec 64) : BitVec 64 :=
  add32 (sbw L) (or32 (andi (shl (add32 w (shru w 31)) 11) (-4096))
    (or32 (shl (r8W L g) 4) (andi (shl w 9) 512)))
/-- `%r507`: the partner warp's P-tile base (pcs 222–225), `%r17` the thread's own (234–235). -/
abbrev r507W (L : Launch) (g : Nat) (w : BitVec 64) : BitVec 64 :=
  add32 (add32 (sbw L) (xor32 (shl w 12) (i32 8192))) (shl (r8W L g) 4)
abbrev r17W (L : Launch) (g : Nat) (w : BitVec 64) : BitVec 64 :=
  add32 (add32 (sbw L) (shl w 12)) (shl (r8W L g) 4)
/-- `%r18`: the valid-mask word's offset of the warp pair (pcs 243–244). -/
abbrev r18W (w : BitVec 64) : BitVec 64 := sel (scmpi .gt .s w 1) (i32 4) (i32 0)
/-- `%r25`: the warp's staging tile (pcs 1343–1345). -/
abbrev r25W (L : Launch) (w : BitVec 64) : BitVec 64 := add32 (sbw L) (shl w 14)
/-- `%r19`, `%r20`: the two rings' slot words (pcs 259–261, 269–270). -/
abbrev r19W (L : Launch) (d : D) : BitVec 64 := add32 (sbw L) (shl d.vs 3)
abbrev r20W (L : Launch) (d : D) : BitVec 64 := add32 (sbw L) (shl d.sl 3)
/-- The low byte of a 16-bit parity word, as a 32-bit word (`cvt.u32.u16`, `and 255`). -/
abbrev parW (p : BitVec 64) : BitVec 64 := andi (zext16w (truncBits 16 p)) 255

/-- The LSE address's row term (`%rd579`, pc 1170) and head-block term (`%rd580`, pc 1172). -/
abbrev lseRow (P : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  mulWideR .s (pw (P.s_q * 64)) (r2W L g)
abbrev lseBlk (L : Launch) (g : Nat) : BitVec 64 :=
  mulWideR .s (pw 64) (BitVec.ofNat 64 (ctaidX L g))
/-- The LSE element index (`%rd583`, pcs 1173–1175). -/
abbrev lseIdx (P : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  add64 (add64 (lseRow P L g) (zext (r5W L g))) (lseBlk L g)
/-- **The LSE address** (`%rd585`, pcs 1167–1177). -/
abbrev lseAddr (P : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  add64 (r64 (pw8 P.lseBase)) (shl64 (lseIdx P L g) 2)

/-! ### The staging pointers (pcs 104–145) -/

/-- `%r472`: the thread's row word of the staging tile (pcs 104–111). -/
abbrev stRow (L : Launch) (g : Nat) : BitVec 64 :=
  or32 (andi (shl (tw L g) 6) 4032) (andi (shl (tw L g) 7) 8192)
/-- `%rd123`: the row's byte offset in the tile (pc 112). -/
abbrev stQuad (L : Launch) (g : Nat) : BitVec 64 := mulWide .u (stRow L g) 2
/-- The unswizzled byte of the thread's staging chunk `k` (`%rd125`, `%rd128`, ..., `%rd146`): the
shared base, the row's offset, the region's `65536` and the chunk's 16 bytes. -/
def stP (L : Launch) (g : Nat) (k : Nat) : Nat :=
  L.sharedBase + (stQuad L g).toNat + (65536 + 16 * k)
/-- The swizzle's mask of chunk `k` (`(address / 8) & 112`, pcs 115–116, ...). -/
def stM (L : Launch) (g : Nat) (k : Nat) : Nat := stP L g k / 8 &&& 112
/-- The swizzled byte of chunk `k`: the byte of the staging pointer `%rd3 + k`. -/
def stW (L : Launch) (g : Nat) (k : Nat) : Nat := stM L g k ^^^ stP L g k
/-- A generic pointer to byte `x` of the thread's CTA's shared memory. -/
abbrev shP (L : Launch) (g : Nat) (x : Nat) : Value :=
  .ptr 64 true (.shared (g / L.block) (g / L.block)) (BitVec.ofNat 64 x)

/-! ### The loop's advance (pcs 1123–1144) -/

/-- `(vs + 1) % 4` as the code computes it (pcs 1137–1142). -/
abbrev nvs (vs : BitVec 64) : BitVec 64 :=
  sub32 (addi vs 1) (andi (add32 (addi vs 1) (shru (shrs (addi vs 1) 31) 30)) (-4))
/-- The valid-mask ring's parity test (`%p116`, pc 1135): the parity's low byte against the
wrap of the slot (`%p115`, `vs = 3`). -/
abbrev pvc (vs pv : BitVec 64) : Bool :=
  PTX.compare .ne .b 16 (truncBits 16 (truncBits 16 pv &&& i16 255))
    (truncBits 16 (sel (scmpi .eq .b vs 3) (i16 1) (i16 0)))
/-- The valid-mask ring's next parity (pcs 1132–1136). -/
abbrev npv (vs pv : BitVec 64) : BitVec 64 := sel (pvc vs pv) (i16 1) (i16 0)
/-- The score ring's parity test (`%p114`, pc 1129). -/
abbrev psc (sl ps : BitVec 64) : Bool :=
  PTX.compare .ne .b 16 (truncBits 16 (truncBits 16 ps &&& i16 255))
    (truncBits 16 (truncBits 16 (truncBits 16 (r32 sl)) &&& i16 255))
/-- The score ring's next parity (pcs 1126–1130). -/
abbrev nps (sl ps : BitVec 64) : BitVec 64 := sel (psc sl ps) (i16 1) (i16 0)

/-- The loop's registers after a block: the counters advance, and the rings unless the block is
the last (`%r2426 = 0`, pc 1123). -/
def advance (d : D) : D :=
  let d1 : D := { d with cnt := addi d.cnt 1, bi := addi d.bi 1 }
  if scmpi .eq .b d.cnt 0 then d1
  else { d1 with sl := andi (not32 d.sl) 1, ps := nps d.sl d.ps, vs := nvs d.vs,
                 pv := npv d.vs d.pv }

/-! ### Transitions -/

section
variable (P : Params) (L : Launch) (g : Nat) (w : BitVec 64)

/-- The end of the warpgroup (pcs 1836–1837): warp 0 deallocates, the others return. -/
def finish (d : D) : D :=
  if scmpi .ne .b w 0 then { d with site := .exit } else { d with site := .dealloc }

/-- After the block loop's set-up (pcs 201–255): the epilogue when there is no block, else the
first block with the rings at zero. -/
def loopEntry (d : D) : D :=
  if scmpi .lt .s (r15 d.l0 d.l1) 64 then { d with site := .ebar0, sl := i32 0, ps := i16 0 }
  else { d with site := .bar0, cnt := sub32 (i32 1) (nblk d.l0 d.l1), bi := i32 1,
                vs := i32 0, pv := i16 0, sl := i32 0, ps := i16 0 }

/-- After the first length: the second length's load if its pointer is set, else the bulk wait. -/
def afterA (d : D) : D :=
  if eqz64 (pw8 (P.extraTopkLenBase.getD 0)) then { d with site := .bwait, l1 := pw P.extra_topk }
  else { d with site := .lenB }

/-- After the sink (pcs 158–165): the end for a CTA beyond the batch, else the length loads the
set pointers ask for. -/
def afterSink (d : D) : D :=
  if scmp .ge .s (r2W L g) (pw P.b) then finish w d
  else if eqz64 (pw8 (P.topkLenBase.getD 0)) then afterA P { d with l0 := pw P.topk }
  else { d with site := .lenA }

/-- After `setmaxnreg` (pcs 146–153): the sink's load when its pointer is set and the head is
below the heads. -/
def afterSmr (d : D) : D :=
  if eqz64 (pw8 (P.sinkBase.getD 0)) || scmp .ge .s (r10W L g) (pw 64) then afterSink P L g w d
  else { d with site := .sink }

/-- The next chunk of the output after chunk `k`. -/
def nextChunk (k : Fin 4) (d : D) : D :=
  { d with site := [.old 1, .old 2, .old 3, .commit].getD k.val .commit }

/-- After an output chunk's named barrier: warps 2 and 3 go on, warps 0 and 1 elect. -/
def afterObar (k : Fin 4) (d : D) : D :=
  if scmpi .gt .s w 1 then nextChunk k d else { d with site := .oel k }

/-- After the epilogue's row-sum read: the LSE store unless the head is beyond the heads. -/
def afterEld (d : D) : D :=
  if scmp .ge .s (r5W L g) (pw 64) then { d with site := .wsv } else { d with site := .lse }
end

/-- The next element of a vector access of `n` elements, or the site after it. -/
def elemNext (d : D) (n : Nat) (s : Site) : D :=
  if d.el + 1 < n then { d with el := d.el + 1 } else { d with site := s, el := 0 }

/-- A length load: a 32-bit word continues, another value stops the machine. -/
def ncWord (e : Event) (f : BitVec 64 → D) : Option (Option D) :=
  match e.kind with
  | .nc _ bs =>
    match rebuild 3 bs with
    | .ok (.bits 32 x) => some (some (f x))
    | .ok _ => some none
    | .error _ => none
  | _ => none

/-- A data read: any payload continues. -/
def dataRd (e : Event) (d : D) : Option (Option D) :=
  match e.kind with
  | .nc _ _ | .rd _ _ => some (some d)
  | _ => none

/-- A poll: on success the next site, else the poll again. -/
def poll (e : Event) (d : D) (s : Site) : Option (Option D) :=
  match e.kind with
  | .wait _ _ ok _ _ => some (some (if ok then { d with site := s } else d))
  | _ => none

/-- A Tensor Memory load: any words continue. -/
def tcLoad (e : Event) (d : D) (s : Site) : Option (Option D) :=
  match e.kind with
  | .tc (.ld ..) => some (some { d with site := s })
  | _ => none

/-- After the P stores of the block: the rescale arm unless the block is the first or the vote
is false (pcs 708–710). -/
def afterOst (d : D) : Site :=
  if scmpi .eq .b d.bi 1 || !d.vt then .fpx else .rsf

/-- **The successor after event `e`.** -/
def succ (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D) (e : Event) :
    Option (Option D) :=
  match d.site with
  | .smr => some (some (afterSmr P L g w d))
  | .sink => dataRd e (afterSink P L g w d)
  | .lenA => ncWord e fun x => afterA P { d with l0 := x }
  | .lenB => ncWord e fun x => { d with site := .bwait, l1 := x }
  | .bwait => some (some { d with site := .arrL })
  | .arrL => some (some (loopEntry d))
  | .bar0 => some (some { d with site := .wv })
  | .wv => poll e d .wq
  | .wq => poll e d .tcfa
  | .tcfa => some (some { d with site := .sld (scmpi .gt .s w 1) 0 })
  | .sld a 0 => tcLoad e d (.sld a 1)
  | .sld _ _ => tcLoad e d .sldw
  | .sldw => some (some { d with site := .tcfb })
  | .tcfb => some (some { d with site := .vm })
  | .vm => dataRd e { d with site := .pst 0 }
  | .pst k => some (some { d with site :=
      [.pst 1, .pst 2, .pst 3, .pst 4, .pst 5, .pst 6, .pst 7].getD k.val .bar1 })
  | .bar1 => some (some { d with site := .pld 0, el := 0 })
  | .pld k =>
    match e.kind with
    | .rd _ bs =>
      if d.el = 0 then
        some (some { d with el := 1, a0 := (rebuild 3 bs).toOption.getD (.bits 64 0) })
      else some (some { d with el := 0, a0 := .pred false, site :=
        [.pld 1, .pld 2, .pld 3, .pld 4, .pld 5, .pld 6, .pld 7].getD k.val .mst })
    | _ => none
  | .mst => some (some { d with site := .bar2 })
  | .bar2 => some (some { d with site := .arrV })
  | .arrV => some (some { d with site := .mld })
  | .mld => dataRd e { d with site := .vote }
  | .vote =>
    match e.kind with
    | .voteMode _ _ _ r => some (some { d with site := .ost 0, el := 0, vt := r })
    | _ => none
  | .ost k => some (some (elemNext d 4 ([.ost 1, .ost 2, .ost 3].getD k.val (afterOst d))))
  | .rsf => some (some { d with site := .rld 0 })
  | .rld k => tcLoad e d (.rldw k)
  | .rldw k => some (some { d with site := .rst k })
  | .rst k => some (some { d with site := .rstw k })
  | .rstw k => some (some { d with site := [.rld 1, .rld 2, .rld 3].getD k.val .rsfb })
  | .rsfb => some (some { d with site := .fpx })
  | .fpx => some (some { d with site := .arrS })
  | .arrS =>
    let d' := advance d
    if scmpi .ne .b d'.cnt 1 then some (some { d' with site := .bar0 })
    else some (some { d' with site := .ebar0 })
  | .ebar0 => some (some { d with site := .est })
  | .est => some (some { d with site := .ebar1 })
  | .ebar1 => some (some { d with site := .eld })
  | .eld => dataRd e (afterEld L g d)
  | .lse => some (some { d with site := .wsv })
  | .wsv => poll e d .efa
  | .efa => some (some { d with site := .old 0 })
  | .old k => tcLoad e d (.oldw k)
  | .oldw k => some (some { d with site := .ost2 k 0, el := 0 })
  | .ost2 k j => some (some (elemNext d 4
      ([.ost2 k 1, .ost2 k 2, .ost2 k 3, .ost2 k 4, .ost2 k 5, .ost2 k 6, .ost2 k 7].getD j.val
        (.ofpx k))))
  | .ofpx k => some (some { d with site := .obar k })
  | .obar k => some (some (afterObar w k d))
  | .oel k =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (if PTX.laneOf L g = ld then { d with site := .otma k } else nextChunk k d))
    | _ => none
  | .otma k => some (some (nextChunk k d))
  | .commit => some (some { d with site := .ebar })
  | .ebar => some (some (finish w d))
  | .dealloc => some (some { d with site := .exit })
  | .exit => none

/-- The number of elements of a site's access. -/
def elems : Site → Nat
  | .pld _ => 2
  | .ost _ | .ost2 _ _ => 4
  | _ => 1

/-! ### The control registers' values -/

section
variable (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D)

/-- The launch's and the startup's registers. -/
def valuesLaunch : List (Nat × Value) :=
  [(459, w32 (BitVec.ofNat 64 (ctaidX L g))), (460, w32 (r2W L g)), (461, w32 (tw L g)),
   (463, w32 (r5W L g)), (465, w32 w), (466, w32 (r8W L g)),
   (2990, .ptr 64 false (.param (param "1")) 0), (2991, .ptr 64 false (.param (param "0")) 0)]

/-- The registers that read the lengths or the vote: the words (`%r2423`, `%r2424`), the first
padded (`%r12`), the padded total (`%r15`), the vote (`%p1`) and its negation (`%p110`), the
no-block test (`%p74`). -/
def valuesLen : List (Nat × Value) :=
  [(2881, w32 d.l0), (2882, w32 d.l1), (470, w32 (pad d.l0)), (473, w32 (r15 d.l0 d.l1)),
   (1, .pred d.vt), (110, .pred (!d.vt)), (74, .pred (scmpi .lt .s (r15 d.l0 d.l1) 64))]

/-- The set-up's registers: parameter pointers and their tests, the exchange and P-tile
addresses, the named-barrier word, the TMA stores' sources and coordinates. -/
def valuesSetup : List (Nat × Value) :=
  [(469, w32 (shl w 1)), (2880, w32 (BitVec.ofNat 64 4286578688)),
   (940, w32 (sbw L)), (981, w32 (sbw L)), (938, w32 (addi (sbw L) 222768)),
   (471, w32 (r13W L g)), (472, w32 (r14W L g)),
   (474, w32 (r16W L g w)), (475, w32 (r17W L g w)), (476, w32 (r18W w)),
   (988, w32 (addi (r507W L g w) 204800)), (989, w32 (addi (r507W L g w) 205312)),
   (990, w32 (addi (r507W L g w) 205824)), (991, w32 (addi (r507W L g w) 206336)),
   (992, w32 (addi (r507W L g w) 206848)), (993, w32 (addi (r507W L g w) 207360)),
   (994, w32 (addi (r507W L g w) 207872)), (995, w32 (addi (r507W L g w) 208384)),
   (996, w32 (or32 (andi w 1) (i32 10))),
   (76, .pred (scmpi .gt .s w 1)), (121, .pred (scmpi .gt .s w 1)),
   (123, .pred (scmpi .gt .s w 1)), (125, .pred (scmpi .gt .s w 1)),
   (127, .pred (scmpi .gt .s w 1)),
   (3000, .bits 64 (pw8 (P.sinkBase.getD 0))), (69, .pred (eqz64 (pw8 (P.sinkBase.getD 0)))),
   (468, w32 (r10W L g)), (70, .pred (scmp .ge .s (r10W L g) (pw 64))),
   (71, .pred (scmp .ge .s (r2W L g) (pw P.b))),
   (3002, .bits 64 (pw8 (P.topkLenBase.getD 0))),
   (72, .pred (eqz64 (pw8 (P.topkLenBase.getD 0)))),
   (3003, .bits 64 (pw8 (P.extraTopkLenBase.getD 0))),
   (73, .pred (eqz64 (pw8 (P.extraTopkLenBase.getD 0)))),
   (3138, .bits 64 (add64 (pw8 (P.sinkBase.getD 0)) (mulWide .u (r10W L g) 4))),
   (3140, .bits 64 (add64 (pw8 (P.topkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (3142, .bits 64 (add64 (pw8 (P.extraTopkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (3001, .ptr 64 true (.param (param "1")) 0),
   (483, w32 (r25W L w)),
   (1913, w32 (addi (r25W L w) 65536)), (1914, w32 (shl w 7)),
   (2082, w32 (addi (r25W L w) 73728)), (2083, w32 (addi (shl (shl w 1) 6) 64)),
   (2251, w32 (addi (r25W L w) 98304)), (2252, w32 (addi (shl (shl w 1) 6) 256)),
   (2421, w32 (addi (r25W L w) 106496)), (2422, w32 (addi (shl (shl w 1) 6) 320)),
   (3832, .bits 64 (W (P.param1Base + 512))),
   (3566, .bits 64 (pw8 P.lseBase)), (3567, .bits 64 (r64 (pw8 P.lseBase))),
   (1734, w32 (pw (P.s_q * 64))), (1735, w32 (pw 64)), (3568, .bits 64 (lseRow P L g)),
   (3569, .bits 64 (lseBlk L g)), (3570, .bits 64 (zext (r5W L g))),
   (3571, .bits 64 (add64 (lseRow P L g) (zext (r5W L g)))), (3572, .bits 64 (lseIdx P L g)),
   (3573, .bits 64 (shl64 (lseIdx P L g) 2)),
   (3574, .bits 64 (lseAddr P L g)), (118, .pred (scmp .ge .s (r5W L g) (pw 64))),
   (75, .pred (scmpi .gt .s w 1)), (129, .pred (scmpi .ne .b w 0))]

/-- The constants moved into registers before an event: barrier ids and counts, the polls'
suspend bound, Tensor Memory columns, the elections' masks and flags, the TMA coordinates. -/
def valuesConst : List (Nat × Value) :=
  [(972, w32 (i32 9)), (973, w32 (i32 128)), (997, w32 (i32 64)), (998, w32 (i32 9)),
   (999, w32 (i32 128)), (1725, w32 (i32 9)), (1726, w32 (i32 128)), (1906, w32 (i32 9)),
   (1907, w32 (i32 128)), (2077, w32 (i32 9)), (2078, w32 (i32 128)), (2247, w32 (i32 9)),
   (2416, w32 (i32 9)), (2417, w32 (i32 128)), (2425, w32 (i32 12)), (2426, w32 (i32 384)),
   (2427, w32 (i32 0)), (2428, w32 (i32 512)),
   (976, w32 (i32 10000000)), (1737, w32 (i32 10000000)), (1112, w32 (i32 (-1))),
   (984, w32 (i32 400)), (985, w32 (i32 432)), (986, w32 (i32 400)), (987, w32 (i32 432)),
   (1263, w32 (i32 0)), (1392, w32 (i32 64)), (1521, w32 (i32 128)), (1650, w32 (i32 192)),
   (1809, w32 (i32 0)), (1980, w32 (i32 64)), (2150, w32 (i32 128)), (2319, w32 (i32 192)),
   (1911, w32 (i32 0)), (1912, w32 (i32 (-1))), (1915, w32 (i32 0)),
   (2080, w32 (i32 0)), (2081, w32 (i32 (-1))), (2084, w32 (i32 0)),
   (2249, w32 (i32 0)), (2250, w32 (i32 (-1))), (2253, w32 (i32 0)),
   (2419, w32 (i32 0)), (2420, w32 (i32 (-1))), (2423, w32 (i32 0))]

/-- The block loop's registers. -/
def valuesLoop : List (Nat × Value) :=
  [(2883, w32 d.bi), (2884, w32 d.cnt), (2952, w32 d.vs), (2953, w32 d.sl),
   (451, .bits 16 d.pv), (452, .bits 16 d.ps),
   (477, w32 (r19W L d)), (478, w32 (r20W L d)),
   (974, w32 (addi (r19W L d) 222840)), (975, w32 (parW d.pv)),
   (977, w32 (addi (r20W L d) 222904)), (978, w32 (parW d.ps)),
   (1001, w32 (add32 (r19W L d) (r18W w))), (1000, w32 (addi (r19W L d) 222872)),
   (1717, w32 (addi (r20W L d) 222920)),
   (2954, w32 (parW d.ps)), (1736, w32 (addi (r20W L d) 222936)),
   (113, .pred (scmpi .eq .b d.cnt 0)), (117, .pred (scmpi .ne .b d.cnt 1)),
   (1718, w32 (not32 d.sl)), (114, .pred (psc d.sl d.ps)), (115, .pred (scmpi .eq .b d.vs 3))]

/-- The staging pointers (`%rd3`–`%rd10`, ids 2992–2999) and their computation: the row words
(925–930), the base word and its generic pointer (3110, 3111), the row's offset and its pointer
(3112, 3113), and per chunk `k` its unswizzled pointer, eighth and mask (`3114 + 3 k`, `+ 1`,
`+ 2`). -/
def valuesStage : List (Nat × Value) :=
  [(2992, shP L g (stW L g 0)), (2993, shP L g (stW L g 1)), (2994, shP L g (stW L g 2)),
   (2995, shP L g (stW L g 3)), (2996, shP L g (stW L g 4)), (2997, shP L g (stW L g 5)),
   (2998, shP L g (stW L g 6)), (2999, shP L g (stW L g 7)),
   (925, w32 (shl (tw L g) 6)), (926, w32 (andi (shl (tw L g) 6) 4032)),
   (927, w32 (shl (tw L g) 7)), (928, w32 (andi (shl (tw L g) 7) 8192)), (929, w32 (sbw L)),
   (930, w32 (stRow L g)), (3110, .bits 64 (zext (sbw L))), (3111, shP L g L.sharedBase),
   (3112, .bits 64 (stQuad L g)), (3113, shP L g (L.sharedBase + (stQuad L g).toNat)),
   (3114, shP L g (stP L g 0)), (3115, .bits 64 (BitVec.ofNat 64 (stP L g 0 / 8))),
   (3116, .bits 64 (BitVec.ofNat 64 (stM L g 0))),
   (3117, shP L g (stP L g 1)), (3118, .bits 64 (BitVec.ofNat 64 (stP L g 1 / 8))),
   (3119, .bits 64 (BitVec.ofNat 64 (stM L g 1))),
   (3120, shP L g (stP L g 2)), (3121, .bits 64 (BitVec.ofNat 64 (stP L g 2 / 8))),
   (3122, .bits 64 (BitVec.ofNat 64 (stM L g 2))),
   (3123, shP L g (stP L g 3)), (3124, .bits 64 (BitVec.ofNat 64 (stP L g 3 / 8))),
   (3125, .bits 64 (BitVec.ofNat 64 (stM L g 3))),
   (3126, shP L g (stP L g 4)), (3127, .bits 64 (BitVec.ofNat 64 (stP L g 4 / 8))),
   (3128, .bits 64 (BitVec.ofNat 64 (stM L g 4))),
   (3129, shP L g (stP L g 5)), (3130, .bits 64 (BitVec.ofNat 64 (stP L g 5 / 8))),
   (3131, .bits 64 (BitVec.ofNat 64 (stM L g 5))),
   (3132, shP L g (stP L g 6)), (3133, .bits 64 (BitVec.ofNat 64 (stP L g 6 / 8))),
   (3134, .bits 64 (BitVec.ofNat 64 (stM L g 6))),
   (3135, shP L g (stP L g 7)), (3136, .bits 64 (BitVec.ofNat 64 (stP L g 7 / 8))),
   (3137, .bits 64 (BitVec.ofNat 64 (stM L g 7)))]

/-- **The value table.** -/
def values : List (Nat × Value) :=
  valuesLen d ++ valuesLoop L w d ++ valuesConst ++ valuesSetup P L g w ++ valuesLaunch L g w ++
    valuesStage L g

/-- The value of register `r` at state `d`. -/
def valueOf (r : Nat) : Value := ((values P L g w d).lookup r).getD (.pred false)

/-- The facts at state `d`: the control registers live at its pc. -/
abbrev facts : List (Nat × Value) := factsFrom (ctlLive d.site.pc) (valueOf P L g w d)
end

/-- The element sub-step and the accumulator of a vector access. -/
def D.acc (d : D) : List Value := if d.el = 0 then [] else
  match d.site with
  | .pld _ => [d.a0]
  | _ => []

/-- **Warpgroup 0 as a control machine** (for the warp word `w`). -/
@[reducible] def code (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := { site := .smr }
  pc := (·.site.pc)
  facts := facts P L g w
  sub := (·.el)
  acc := D.acc
  inv := fun d => d.el < elems d.site
  next := succ P L g w

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
