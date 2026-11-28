-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Sites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Arith
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Entry
public import Lemmas.Flow.Arith32Wide
public import Lemmas.Flow.CodeU
public import Lemmas.Flow.NcLoadU

@[expose] public section

/-! # Warpgroup 2 as a control machine

One machine for the whole role (pcs 2606–3610 and the `ret`), from its first event, the
`setmaxnreg` at pc 2606. A state carries what decides control flow and the shapes of events:

* the site, the element of the scale load (`el`) and the elements read so far (`ac`);
* the two length words (`l0`, `l1`: `%r2527`, `%r2528`), the parameters unless a length pointer
  is set, then the loaded word;
* the block loop's registers: the negative block counter `cnt` (`%r2529`, from `-blocks` to `0`),
  the ring's slot (`sb`, `%r2530 = 1`) and parity (`pb`, `%rs318 = 1`). Slot and parity are
  `0` or `1` by the code (`mov 0`, then `(~slot) & 1` and `selp 1, 0`), so they are Booleans:
  a step proof splits on them and every slot and parity word is a literal.

Everything else is havocked: the data registers (`Live.lean`) are not stated, so the scale
bytes, the raw words and the dequantized chunks are free (their values: `Dequant/Data`). The data
loads continue on any payload (bytes that do not rebuild fault in the concrete continuation, which
the UB-tolerant soundness `Flow.CodeU` admits); the length loads decide control and are followed on
their word.

The warp word `w` is a parameter, as for every warpgroup's fragment; this role does not read it.
The value table states each control register as the code's term over the launch, the
parameters and the fields. -/

/-! # The control registers of warpgroup 2

The control machine states facts for its control registers only: `ctlLive pc` is the generated
liveness (`Flow.live`) without the data registers. The data registers (`dataRanges`, ids) are the
closure, under the role's local instructions, of the destinations of its scale and raw loads from
shared memory: the scale bytes and their selection, the halfwords, the converted and multiplied
pairs and the packed chunks. Read from the PTX: no branch and no event address reads a data
register; the stores' payloads do. The chunk addresses (`%r2014` and the 31 `add.s32` of it in
the float runs) are control registers. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX

/-- The data registers of warpgroup 2 (ranges of register ids). -/
def dataRanges : List (Nat × Nat) :=
  [(191, 350), (353, 448), (2463, 2471), (2473, 2481), (2483, 2491), (2493, 2501), (2503, 2511),
   (2513, 2521), (2523, 2531), (2533, 2541), (2543, 2551), (2553, 2561), (2563, 2571),
   (2573, 2581), (2583, 2591), (2593, 2601), (2603, 2611), (2613, 2621), (2623, 2631),
   (2633, 2641), (2643, 2651), (2653, 2661), (2663, 2671), (2673, 2681), (2683, 2691),
   (2693, 2701), (2703, 2711), (2713, 2721), (2723, 2731), (2733, 2741), (2743, 2751),
   (2753, 2761), (2763, 2771), (2773, 2781), (2797, 2816), (2818, 2877), (3837, 4028),
   (4039, 4070)]

/-- A control register: not a data register. -/
def ctl (r : Nat) : Bool := !dataRanges.any fun (a, b) => Nat.ble a r && Nat.ble r b

/-- The control registers live at program counter `pc`. -/
noncomputable def ctlLive (pc : Nat) : List Nat :=
  (PTX.Kernels.FlashMlaSparseDecodeH64.Flow.live pc).filter ctl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- A state. -/
structure D where
  site : Site
  el : Nat := 0
  ac : List Value := []
  l0 : BitVec 64 := 0
  l1 : BitVec 64 := 0
  cnt : BitVec 64 := 0
  sb : Bool := false
  pb : Bool := false

/-! ### The code's terms -/

/-- The padded length `pad64 a` (pcs 2622–2626, 2631–2635). -/
abbrev pad (a : BitVec 64) : BitVec 64 :=
  andi (add32 (addi a 63) (shru (shrs (addi a 63) 31) 26)) (-64)
/-- `%r57`, the padded total (pcs 2631–2639). -/
abbrev r57 (a b : BitVec 64) : BitVec 64 :=
  add32 (add32 (addi b 63) (max32 (pad a) (i32 64))) (sub32 (pad b) (addi b 63))
/-- The block count (pcs 2650–2653). -/
abbrev nblk (a b : BitVec 64) : BitVec 64 :=
  shrs (add32 (r57 a b) (shru (shrs (r57 a b) 31) 26)) 6

/-- `%r5`, `%r54`, `%r55`: the thread's index in its warpgroup, its group of eight, its index in
the group. -/
abbrev r5W (L : Launch) (g : Nat) : BitVec 64 := andi (tw L g) 127
abbrev r54W (L : Launch) (g : Nat) : BitVec 64 := shru (r5W L g) 3
abbrev r55W (L : Launch) (g : Nat) : BitVec 64 := andi (tw L g) 7
/-- `%r58`: the thread's swizzled 16-byte column of the dequantized tile (pcs 2649–2662). -/
abbrev r58W (L : Launch) (g : Nat) : BitVec 64 :=
  or32 (or32 (andi (shl (r54W L g) 7) 896) (andi (shl (tw L g) 4) 1024))
    (shl (xor32 (andi (r54W L g) 7) (r55W L g)) 4)
/-- `%r59`, `%r60`: the raw word's offset in a row, the row's offset in the raw buffer. -/
abbrev r59W (L : Launch) (g : Nat) : BitVec 64 := shl (r55W L g) 3
abbrev r60W (L : Launch) (g : Nat) : BitVec 64 := mul32 (r54W L g) (i32 576)

/-- The slot and parity words. -/
@[reducible] def slW : Bool → BitVec 64
  | true => i32 1
  | false => i32 0
@[reducible] def parB : Bool → BitVec 64
  | true => i16 1
  | false => i16 0
/-- `%r2330`: the slot's barrier word base (pcs 2671–2673). -/
abbrev r2330W (L : Launch) (b : Bool) : BitVec 64 := add32 (sbw L) (shl (slW b) 3)
/-- `%p135`: the slot is `0`. -/
abbrev s0 (b : Bool) : Bool := scmpi .eq .b (slW b) 0
/-- `%r2338`: the row's scale and raw base in the slot's raw buffer (pcs 2688–2694). -/
abbrev r2338W (L : Launch) (g : Nat) (b : Bool) : BitVec 64 :=
  add32 (sel (s0 b) (addi (sbw L) 131072) (addi (sbw L) 167936)) (r60W L g)
/-- `%r2014`: the thread's first chunk address in the slot's dequantized buffer (2691–2693). -/
abbrev r2014W (L : Launch) (g : Nat) (b : Bool) : BitVec 64 :=
  add32 (r58W L g) (sel (s0 b) (sbw L) (addi (sbw L) 65536))

/-! ### Transitions -/

section
variable (P : Params) (L : Launch) (g : Nat)

/-- After the first length: the second length's load if its pointer is set, else the Q poll. -/
def afterA (d : D) : D :=
  if eqz64 (pw8 (P.extraTopkLenBase.getD 0)) then { d with site := .wq }
  else { d with site := .lenB }

/-- After `setmaxnreg` (pcs 2607–2617): the end for a CTA beyond the batch, else the length
loads the set pointers ask for; the lengths start as the parameters. -/
def afterSmr (d : D) : D :=
  let d1 : D := { d with l0 := pw P.topk, l1 := pw P.extra_topk }
  if scmp .ge .s (r2W L g) (pw P.b) then { d1 with site := .exit }
  else if eqz64 (pw8 (P.topkLenBase.getD 0)) then afterA P d1
  else { d1 with site := .lenA }
end

/-- After the Q poll (pcs 2647–2666): the closing barrier when there is no block, else the first
block with the ring at slot 0, parity 0. -/
def loopEntry (d : D) : D :=
  if scmpi .lt .s (r57 d.l0 d.l1) 64 then { d with site := .bar }
  else { d with site := .wraw, cnt := neg32 (nblk d.l0 d.l1), sb := false, pb := false }

/-- After the arrivals (pcs 3600–3607): the counter advances, the slot flips and the parity flips
after slot 1; the next block unless the counter reached `0`. -/
def advance (d : D) : D :=
  let d1 : D := { d with cnt := addi d.cnt 1, sb := !d.sb, pb := d.pb != d.sb }
  if scmpi .ne .b d1.cnt 0 then { d1 with site := .wraw } else { d1 with site := .bar }

/-- The next row's scale load after row `r`, or the fence. -/
def rowNext (r : Fin 4) : Site := [Site.scale 1, .scale 2, .scale 3].getD r.val .fpx
/-- The site after raw load `s` of row `r`. -/
def rawNext (r : Fin 4) (s : Fin 8) : Site :=
  [Site.raw r 1, .store r 0, .store r 1, .store r 2, .store r 3, .store r 4, .store r 5,
    .store r 6].getD s.val .fpx
/-- The site after store `s` of row `r`. -/
def storeNext (r : Fin 4) (s : Fin 8) : Site :=
  [Site.raw r 2, .raw r 3, .raw r 4, .raw r 5, .raw r 6, .raw r 7, .store r 7].getD s.val
    (rowNext r)

/-- The elements of a vector access read so far. -/
def D.acc (d : D) : List Value := if d.el = 0 then [] else d.ac

/-- An element of the scale load: the next element, after the last the row's first raw load. -/
def scaleNext (r : Fin 4) (d : D) (v : Value) : D :=
  if d.el + 1 < 4 then { d with el := d.el + 1, ac := d.acc ++ [v] }
  else { d with site := .raw r 0, el := 0, ac := [] }

/-- A data read: any payload continues. -/
def dataRd (e : Event) (d : D) : Option (Option D) :=
  match e.kind with
  | .rd _ _ => some (some d)
  | _ => none

/-- A poll: on success the next site, else the poll again. -/
def poll (e : Event) (d : D) (s : Site) : Option (Option D) :=
  match e.kind with
  | .wait _ _ ok _ _ => some (some (if ok then { d with site := s } else d))
  | _ => none

/-- **The successor after event `e`.** -/
def succ (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .smr => some (some (afterSmr P L g d))
  | .lenA =>
    match e.kind with
    | .nc _ bs => Code.ncNext (fun x => afterA P { d with l0 := x }) bs
    | _ => none
  | .lenB =>
    match e.kind with
    | .nc _ bs => Code.ncNext (fun x => { d with site := .wq, l1 := x }) bs
    | _ => none
  | .wq =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then loopEntry d else d))
    | _ => none
  | .wraw => poll e d .wsv
  | .wsv => poll e d (.scale 0)
  | .scale r =>
    match e.kind with
    | .rd _ bs => some (some (scaleNext r d ((rebuild 3 bs).toOption.getD (.pred false))))
    | _ => none
  | .raw r s => dataRd e { d with site := rawNext r s }
  | .store r s => some (some { d with site := storeNext r s })
  | .fpx => some (some { d with site := .arrD })
  | .arrD => some (some { d with site := .arrF })
  | .arrF => some (some (advance d))
  | .bar => some (some { d with site := .exit })
  | .exit => none

/-- The number of elements of a site's access. -/
def elems : Site → Nat
  | .scale _ => 4
  | _ => 1

/-! ### The control registers' values -/

section
variable (P : Params) (L : Launch) (g : Nat) (d : D)

/-- The launch's registers and the set-up's: the thread's words, the parameter pointers and
their tests, the length words, the Q barrier's word and the loop's per-thread offsets. -/
def valuesSetup : List (Nat × Value) :=
  [(460, w32 (r2W L g)), (461, w32 (tw L g)), (463, w32 (r5W L g)),
   (2991, .ptr 64 false (.param (param "0")) 0),
   (512, w32 (r54W L g)), (513, w32 (r55W L g)),
   (130, .pred (scmp .ge .s (r2W L g) (pw P.b))),
   (3017, .bits 64 (pw8 (P.topkLenBase.getD 0))),
   (131, .pred (eqz64 (pw8 (P.topkLenBase.getD 0)))),
   (3018, .bits 64 (pw8 (P.extraTopkLenBase.getD 0))),
   (132, .pred (eqz64 (pw8 (P.extraTopkLenBase.getD 0)))),
   (3833, .bits 64 (add64 (pw8 (P.topkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (3835, .bits 64 (add64 (pw8 (P.extraTopkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (2985, w32 d.l0), (2986, w32 d.l1), (514, w32 (pad d.l0)), (515, w32 (r57 d.l0 d.l1)),
   (133, .pred (scmpi .lt .s (r57 d.l0 d.l1) 64)),
   (2434, w32 (addi (sbw L) 222784)), (2435, w32 (i32 0)), (2436, w32 (i32 10000000)),
   (516, w32 (r58W L g)), (517, w32 (r59W L g)), (518, w32 (r60W L g)),
   (134, .pred (scmpi .gt .u (r55W L g) 3)),
   (2878, w32 (i32 12)), (2879, w32 (i32 384))]

/-- The first chunk offsets of the 31 chunks after the first, by register (`%r2024`, …). -/
def chunkOffs : List (Nat × Int) :=
  [(2482, 8192), (2492, 16384), (2502, 24576), (2512, 32768), (2522, 40960), (2532, 49152),
   (2542, 57344), (2552, 2048), (2562, 10240), (2572, 18432), (2582, 26624), (2592, 34816),
   (2602, 43008), (2612, 51200), (2622, 59392), (2632, 4096), (2642, 12288), (2652, 20480),
   (2662, 28672), (2672, 36864), (2682, 45056), (2692, 53248), (2702, 61440), (2712, 6144),
   (2722, 14336), (2732, 22528), (2742, 30720), (2752, 38912), (2762, 47104), (2772, 55296),
   (2782, 63488)]

/-- The block loop's registers: counter, slot and parity, the polls' words, the slot's bases and
the chunk addresses, the arrivals' words and the back-edge's test. -/
def valuesLoop : List (Nat × Value) :=
  [(2987, w32 d.cnt), (2988, w32 (slW d.sb)), (457, .bits 16 (parB d.pb)),
   (351, .bits 16 (truncBits 16 (parB d.pb) &&& i16 255)),
   (2787, w32 (sbw L)), (2788, w32 (r2330W L d.sb)), (2789, w32 (not32 (slW d.sb))),
   (2458, w32 (addi (r2330W L d.sb) 222808)),
   (2459, w32 (andi (zext16w (truncBits 16 (parB d.pb))) 255)), (2460, w32 (i32 10000000)),
   (2461, w32 (addi (r2330W L d.sb) 222936)),
   (2462, w32 (andi (zext16w (xor16 (parB d.pb))) 255)),
   (135, .pred (s0 d.sb)),
   (2791, w32 (addi (sbw L) 167936)), (2792, w32 (addi (sbw L) 131072)),
   (2794, w32 (addi (sbw L) 65536)),
   (2793, w32 (sel (s0 d.sb) (addi (sbw L) 131072) (addi (sbw L) 167936))),
   (2796, w32 (r2338W L g d.sb)), (2817, w32 (add32 (r2338W L g d.sb) (r59W L g))),
   (2472, w32 (r2014W L g d.sb)),
   (2783, w32 (addi (r2330W L d.sb) 222792)), (2784, w32 (addi (r2330W L d.sb) 222824)),
   (137, .pred (scmpi .ne .b d.cnt 0))] ++
  chunkOffs.map fun (r, c) => (r, w32 (addi (r2014W L g d.sb) c))

/-- **The value table.** -/
def values : List (Nat × Value) := valuesLoop L g d ++ valuesSetup P L g d

/-- The value of register `r` at state `d`. -/
def valueOf (r : Nat) : Value := ((values P L g d).lookup r).getD (.pred false)

/-- The facts at state `d`: the control registers live at its pc. -/
abbrev facts : List (Nat × Value) := factsFrom (ctlLive d.site.pc) (valueOf P L g d)
end

/-- **Warpgroup 2 as a control machine** (for the warp word `_w`, not read). -/
@[reducible] def code (P : Params) (L : Launch) (g : Nat) (_w : BitVec 64) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := { site := .smr }
  pc := (·.site.pc)
  facts := facts P L g
  sub := (·.el)
  acc := D.acc
  inv := fun d => d.el < elems d.site
  next := succ P L g

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
