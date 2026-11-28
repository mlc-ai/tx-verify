-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
public import Kernels.InklingRelDecode.Proof.Prologue.Control.Live
public import Kernels.InklingRelDecode.Proof.Prologue.CopyAddress
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Prologue
public import Kernels.InklingRelDecode.Proof.Lib.WideBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Proof PTX.Flow Arith32

noncomputable section

def u32 (n : Nat) := b32 (n%2^32)
def u64 (n : Nat) := b64 (n%2^64)
def u16 (n : Nat) := Value.bits 16 (BitVec.ofNat 64 n)

/-- The common query-store address register after pc 520. Keep the same
32-bit operations as the PTX code so the following proof works on any launch. -/
def queryBase (L : Launch) (t : Nat) : BitVec 64 :=
  add32 (W (L.sharedBase%2^32)) (xor32 (andi (shl (W t) 4) 2032) (andi (shl (W t) 1) 112))

/-- The election result and the guards computed from it. -/
def voteReg (r : Nat) : Bool :=
  (26 ≤ r && r ≤ 37) || (41 ≤ r && r ≤ 52) ||
  (54 ≤ r && r ≤ 80 && r != 59 && r != 63 && r != 72)

/-- Query row group `gp` of lane `tid`: its row, the token of the row, the row sum of the
sixteen-bit chain (row plus doubled token, the row of the last group kept below 64) and the
head remainder. -/
def qRow (tid gp : Nat) := tid / 8 % 16 + 16 * gp
def qTok (tid gp : Nat) := qRow tid gp * 10923 / 65536
def qSum (tid gp : Nat) := tid / 8 % 16 + (if gp = 3 then 48 else 0) + 2 * qTok tid gp

/-- The signed product of the row stride and the token of group `gp`. -/
def qProd (Q : Params) (first : Value) (tid gp : Nat) : Nat :=
  Lib.sx Q.strideQ * Lib.sx ((Lib.word first).toNat + qTok tid gp)

/-- The row origin of query group `gp`: the base plus the doubled product. -/
def queryOrigin (Q : Params) (first : Value) (tid gp : Nat) : Nat :=
  (Q.qBase + 2 * qProd Q first tid gp) % 2 ^ 64

/-- The head offset of group `gp` in elements: the head index plus the remainder, times 128. -/
def qHoff (y tid gp : Nat) : Nat := (y * 6 + qSum tid gp % 8) % 2 ^ 32 * 128 % 2 ^ 32

/-- The Q-tile row pointer of query group `gp`. -/
def queryPointer (Q : Params) (first : Value) (tid y gp : Nat) : Nat :=
  (queryOrigin Q first tid gp + 2 * qHoff y tid gp) % 2 ^ 64

/-- The block-table row of request `req`: the base plus four times the signed row offset. -/
def btRow (Q : Params) (req : Nat) : Nat := Lib.sx (Q.strideBt * req) * 4 + Q.btBase

/-- The signed shift of a word by six: the block-table index of a preload half. -/
def blkIx (n : Nat) : Nat := (shrs (W (n % 2 ^ 32)) 6).toNat

/-- The shifted offsets of the three preloads (`1912`, `712`, `734`). -/
def blkOff (Q : Params) (split : Nat) : Nat → Nat
  | 0 => split * 128
  | 1 => (Q.splits + split) * 128
  | _ => Q.splits * 256 + split * 128

/-- The address register of block-table load `b`, half `h` (`2071 + 2 b + h`). -/
def blockPtr (Q : Params) (req split b h : Nat) : Nat :=
  Lib.sx (blkIx (blkOff Q split b)) * 4 + btRow Q req + 4 * h

/-- The byte offset of element `e` of a query lane's sixteen: two halves of eight 16-bit words,
128 bytes apart. -/
def qOff (e : Nat) : Nat := 2 * (e % 8) + 128 * (e / 8)

/-- The query load address `2077 + 16 gp + e`: the row pointer of group `gp`, the lane column
`8 (tid % 8)` in elements, and the offset of element `e`. -/
def qLane (Q : Params) (first : Value) (tid y gp e : Nat) : Nat :=
  queryPointer Q first tid y gp + 16 * (tid % 8) + qOff e

/-- The registers of the query pointer chain at pcs 84 to 128, grouped by name range. -/
def queryReg (r : Nat) : Bool :=
  (190 ≤ r && r ≤ 197) || (645 ≤ r && r ≤ 664) || (1951 ≤ r && r ≤ 1954) ||
  (2059 ≤ r && r ≤ 2070) ||
  (691 ≤ r && r ≤ 692) || (711 ≤ r && r ≤ 713) || (733 ≤ r && r ≤ 735) || r == 1955 ||
  (2071 ≤ r && r ≤ 2076) || (2077 ≤ r && r ≤ 2140) || r == 2205

/-- The values of the registers of `queryReg`: tokens, rows, remainders, head offsets, products,
origins and pointers of the four row groups of the lane. -/
def queryValue (Q : Params) (first : Value) (tid y split req r : Nat) : Value :=
  if r ≤ 197 then
    if (r - 190) % 2 = 0 then u16 (2 * qTok tid ((196 - r) / 2)) else u16 (qSum tid ((197 - r) / 2))
  else if r ≤ 648 then b32 (((Lib.word first).toNat + qTok tid (r - 645)) % 2 ^ 32)
  else if r ≤ 656 then
    if (r - 649) % 2 = 0 then u32 (qSum tid ((r - 649) / 2)) else u32 (qSum tid ((r - 650) / 2) % 8)
  else if r ≤ 660 then u32 (y * 6 + qSum tid (r - 657) % 8)
  else if r ≤ 664 then u32 (qHoff y tid (r - 661))
  else if r ≤ 691 then u32 (Q.strideBt * req)
  else if r ≤ 692 then .bits 32 (shrs (W (blkOff Q split 0 % 2 ^ 32)) 6)
  else if r ≤ 711 then u32 (Q.splits + split)
  else if r ≤ 712 then u32 ((Q.splits + split) * 128)
  else if r ≤ 713 then .bits 32 (shrs (W (blkOff Q split 1 % 2 ^ 32)) 6)
  else if r ≤ 733 then u32 (Q.splits * 256)
  else if r ≤ 734 then u32 (Q.splits * 256 + split * 128)
  else if r ≤ 735 then .bits 32 (shrs (W (blkOff Q split 2 % 2 ^ 32)) 6)
  else if r ≤ 1954 then u64 (queryPointer Q first tid y (r - 1951))
  else if r ≤ 1955 then u64 (btRow Q req)
  else if r ≤ 2062 then u64 (qProd Q first tid (2062 - r))
  else if r ≤ 2070 then
    if (r - 2063) % 2 = 0 then u64 (2 * qProd Q first tid ((r - 2063) / 2))
    else u64 (queryOrigin Q first tid ((r - 2064) / 2))
  else if r ≤ 2076 then u64 (blockPtr Q req split ((r - 2071) / 2) ((r - 2071) % 2))
  else if r ≤ 2140 then u64 (qLane Q first tid y ((r - 2077) / 16) ((r - 2077) % 16))
  else u64 (16 * (tid % 8))

set_option linter.deprecated false in
/-- The lane address registers `2077 + 16 gp + e`. -/
theorem queryValue_lane {Q first tid y split req r} (lo : 2077 ≤ r) (hi : r ≤ 2140) :
    queryValue Q first tid y split req r =
      u64 (qLane Q first tid y ((r - 2077) / 16) ((r - 2077) % 16)) := by
  unfold queryValue
  repeat rw [if_neg (by omega)]
  rw [if_pos (by omega)]

def registerValue (Q : Params) (L : Launch) (g : Nat) (w : Value) (first last seq : Value)
    (won : Bool) (r : Nat) : Value :=
  let d : D := {first,last,seq}
  let tid := g%L.block
  let coords := L.ctaidOf (g/L.block)
  let split := coords.get .x
  let req := (coords.get .z)%2^32
  let len := subValue d.last d.first
  let prior := subValue d.seq len
  let pastWord := Lib.word prior
  let seq127 := addi (Lib.word d.seq) 127
  let biased := add32 seq127 (shru (shrs seq127 31) 25)
  let num := iters Q.splits split (div128 seq127)
  let old := iters Q.splits split (div128 pastWord)
  let shift := add32 (W Q.splits) (not32 (W split))
  let n := preload Q.splits split d
  let laneRow := tid/8%16
  let token := fun group => (laneRow+16*group)*10923/65536
  match r with
  | 3 => .pred (decide (tid<32))
  | 38 => .pred (decide (laneRow+48<60))
  | 39 => .pred (scmp .gt .s (qlen d) (W (token 3)))
  | 40 => .pred (decide (tid<32))
  | 53 => .pred (decide (n≠0)) | 59 => .pred (decide (tid%128<64))
  | 63 => .pred (decide (n=1)) | 72 => .pred (decide (n<3))
  | 81 | 82 | 83 | 84 => .pred (queryOn tid (r-81) d)
  | 177 => .pred (decide (tid%128=0))
  | 182 | 183 | 184 | 185 => u16 (laneRow+16*(r-182))
  | 186 | 187 | 188 | 189 => u16 (token (189-r))
  | 462 => b32 tid | 463 => w | 464 => b32 (tid/32)
  | 478 => u32 split | 479 => u32 (coords.get .y) | 480 => b32 req
  | 481 => len | 482 => prior
  | 483 => .bits 32 (shru (positive (addi pastWord (-1023))) 7)
  | 484 => .bits 32 (div128 pastWord) | 485 => .bits 32 (andi biased (-128))
  | 486 => .bits 32 num | 487 => .bits 32 (positive num)
  | 488 => b32 (tid%128) | 489 => b32 (tid%8*8)
  | 490 => u32 ((coords.get .y)*6) | 491 => Lib.addBase w 256
  | 492 => b32 n | 493 => b32 (min 3 n)
  | 526 => u32 Q.strideQ | 527 => u32 Q.strideRel | 528 => u32 Q.strideBt
  | 532 => u32 Q.splits | 533 => u32 Q.nTok
  | 610 => d.first | 611 => d.last | 612 => d.seq
  | 625 => .bits 32 (addi pastWord (-1023)) | 626 => .bits 32 (positive (addi pastWord (-1023)))
  | 627 => .bits 32 (shrs pastWord 31) | 628 => .bits 32 (shru (shrs pastWord 31) 25)
  | 629 => .bits 32 (add32 pastWord (shru (shrs pastWord 31) 25))
  | 630 => .bits 32 seq127 | 631 => .bits 32 (shrs seq127 31)
  | 632 => .bits 32 (shru (shrs seq127 31) 25) | 633 => .bits 32 biased
  | 634 => .bits 32 (shrs biased 7) | 635 => .bits 32 (not32 (W split))
  | 636 => .bits 32 shift | 637 => .bits 32 (add32 shift (div128 seq127))
  | 638 => b32 laneRow | 639 => b32 (laneRow+48)
  | 641 | 642 | 643 | 644 => b32 (token (644-r))
  | 666 => u32 L.sharedBase
  | 678 => .bits 32 (add32 shift (div128 pastWord)) | 679 => .bits 32 old
  | 680 => .bits 32 (positive old)
  | 746 => .bits 32 (addi (queryBase L tid) 196608)
  | 751 => .bits 32 (addi (queryBase L tid) 204800)
  | 756 => .bits 32 (addi (queryBase L tid) 198656)
  | 761 => .bits 32 (addi (queryBase L tid) 206848)
  | 766 => .bits 32 (addi (queryBase L tid) 200704)
  | 771 => .bits 32 (addi (queryBase L tid) 208896)
  | 776 => .bits 32 (addi (queryBase L tid) 202752)
  | 781 => .bits 32 (addi (queryBase L tid) 210944)
  | 791 => .bits 32 (queryBase L tid)
  | 792 => u32 (L.sharedBase+212992) | 1912 => u32 (split*128)
  | 1949 => .ptr 64 true (.param (param "1")) 0
  | 2018 => b64 Q.qBase | 2019 => b64 Q.relBase | 2020 => b64 Q.btBase
  | 2021 => b64 Q.seqBase | 2022 => b64 Q.cuBase
  | 2023 => b64 Q.oBase | 2024 => b64 Q.lseBase
  | 2055 => u64 (Q.cuBase+4*req) | 2056 => u64 (Q.cuBase+4*req+4)
  | 2057 => u64 (Q.seqBase+4*req) | 2058 => b64 (4*req)
  | _ => if queryReg r then queryValue Q first tid (coords.get .y) split req r
    else if h : 613 ≤ r ∧ r < 625 then
      u32 (L.sharedBase+MbarRow.initOffset ⟨r-613,by omega⟩)
    else if r = 199 then u16 0
    else if 26 ≤ r ∧ r ≤ 37 then .pred (decide (tid<32) && won)
    else if (54 ≤ r ∧ r ≤ 57) ∨ (64 ≤ r ∧ r ≤ 67) ∨ (73 ≤ r ∧ r ≤ 76) then
      .pred (decide (tid%128<64) && won)
    else .pred won

def copyValue (L : Launch) (broadcast : Value) : Nat → Value
  | 693 | 714 | 736 => broadcast
  | 695 | 716 | 738 => .bits 32 (andi (Lib.word broadcast) 1)
  | 696 | 717 | 739 => .bits 32 (shl (andi (Lib.word broadcast) 1) 14)
  | 682 | 718 | 740 => .bits 32 (copyBase L broadcast)
  | 685 => .bits 32 (addi (copyBase L broadcast) 98304)
  | 688 => .bits 32 (addi (copyBase L broadcast) 8192)
  | 690 => .bits 32 (addi (copyBase L broadcast) 106496)
  | 702 => .bits 32 (addi (copyBase L broadcast) 32768)
  | 705 => .bits 32 (addi (copyBase L broadcast) 131072)
  | 708 => .bits 32 (addi (copyBase L broadcast) 40960)
  | 710 => .bits 32 (addi (copyBase L broadcast) 139264)
  | 724 => .bits 32 (addi (copyBase L broadcast) 65536)
  | 727 => .bits 32 (addi (copyBase L broadcast) 163840)
  | 730 => .bits 32 (addi (copyBase L broadcast) 73728)
  | 732 => .bits 32 (addi (copyBase L broadcast) 172032)
  | _ => b32 0

def valueOf (Q : Params) (L : Launch) (g : Nat) (w : Value) (d : D) (r : Nat) : Value :=
  if copyReg r then copyValue L d.broadcast r else
    registerValue Q L g w d.first d.last d.seq (voteReg r && d.elected) r

theorem valueOf_plain {Q L g w d r} (plain : copyReg r=false) :
    valueOf Q L g w d r=registerValue Q L g w d.first d.last d.seq (voteReg r && d.elected) r := by
  simp [valueOf,plain]

/-- The registers of the query pointer chain take `queryValue`. -/
theorem valueOf_query {Q L g w d r} (plain : copyReg r = false) (h : queryReg r = true) :
    valueOf Q L g w d r =
      queryValue Q d.first (g % L.block) ((L.ctaidOf (g / L.block)).get .y)
        ((L.ctaidOf (g / L.block)).get .x) ((L.ctaidOf (g / L.block)).get .z % 2 ^ 32) r := by
  rw [valueOf_plain plain]
  unfold registerValue
  split <;> first | (exfalso; simp_all [queryReg]; done) | simp [h]

def facts (Q : Params) (L : Launch) (g : Nat) (w : Value) (d : D) (pc : Nat) :=
  factsFrom (ctlLive pc) (valueOf Q L g w d)

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
