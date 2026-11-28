-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Sites
public import Kernels.InklingRelDecode.Proof.Softmax.Control.Live
public import Kernels.InklingRelDecode.Proof.Lib.RawArith
public import Lemmas.Flow.CodeU
public import Kernels.InklingRelDecode.Proof.Lib.RescaleWord
public import Kernels.InklingRelDecode.Proof.Lib.WideBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Control inputs from the prologue. The shared base word is retained with its Value tag. -/
structure Entry where
  base : Value
  split : Nat
  qlen : Nat
  /-- The value of register 21 of the prologue: the words past the request's first token. -/
  prior : Value
  nbias : Nat
  biasOffset : Nat
  blocks : Nat
  limit : Nat
  head : Nat
  firstWord : Value
  stride : Nat
  splits : Nat
  tokens : Nat
  rel : Nat
  outBase : Nat
  lseBase : Nat

def Entry.firstToken (e : Entry) := (Lib.word e.firstWord).toNat
/-- The words past the request's first token. -/
def Entry.past (e : Entry) : Nat := (Lib.word e.prior).toNat

/-- The data registers the control machine tracks beyond the control-live ones: the warp
broadcast, and the two words of the last shuffle: the scratch word read at pc 2252 with the
word its xor-2 neighbour sent, or the operand and result of a butterfly shuffle at pc 2242
to 2248. -/
structure Carry where
  base : Value := b32 0
  word : Value := b32 0
  peer : Value := b32 0

structure D where
  site : Site := .setMaxReg
  i : Nat := 0
  held : Carry := {}

def row (t : Nat) := t % 16 + t / 32 % 4 * 16
def token (t : Nat) := row t * 43 / 256
def headInGroup (t : Nat) := row t - token t * 6
/-- The signed length comparison at pc 585 treats every high-bit request length as negative. -/
def tokenFits (e : Entry) (t : Nat) := decide (token t < e.qlen ∧ e.qlen < 2^31)
def validRow (e : Entry) (t : Nat) := decide (row t < 60) && tokenFits e t
def preEnabled (e : Entry) (t : Nat) :=
  validRow e t && decide (0 < e.blocks ∧ e.blocks < 2^31 ∧ e.nbias ≤ e.split)
def nextEnabled (e : Entry) (t i : Nat) :=
  validRow e t && decide (i + 1 < e.blocks ∧ e.blocks < 2^31 ∧
    e.nbias ≤ e.split + i * e.splits + e.splits)

def loopSite (e : Entry) (t i : Nat) : Site :=
  if i = e.limit then .epilogue else if nextEnabled e t i then .nxt 0 else .waitS

/-- The last reduction shuffle publishes both inputs of the following min and
comparison. Read their predicate with the instruction semantics, including the
kernel's ideal-min rule. A fault leaves the concrete thread dead during the crossing. -/
def skipRescale (L : Launch) (g : Nat) (sent recv : Value) : Bool := Id.run do
  let t : TState := {pc := 2256, regs := fun r =>
    if r = 1544 then some sent else if r = 1545 then some recv else none}
  let some mi := kernel.code[2256]? | return false
  let some cmp := kernel.code[2257]? | return false
  let .ok u := execLocalA Assumptions.all L g t mi.op | return false
  let .ok s := execLocalA Assumptions.all L g u cmp.op | return false
  return decide (s.regs 170 = some (.pred true))

def advance (e : Entry) (t : Nat) (d : D) : D :=
  {d with i := d.i+1, site := loopSite e t (d.i+1)}

def next (e : Entry) (L : Launch) (g : Nat) (d : D) (ev : Event) : Option (Option D) :=
  let t := g % L.block
  let go := fun s => some (some {d with site := s})
  let poll := fun s => match ev.kind with
    | .wait _ _ ok _ _ => go (if ok then s else d.site)
    | _ => none
  let fold := fun s => match ev.kind with
    | .shfl _ sent _ _ recv _ => some (some {d with site := s, held := {d.held with
        word := sent, peer := recv}})
    | _ => none
  match d.site with
  | .setMaxReg => go .bar0
  | .bar0 => go (if preEnabled e t then .pre 0 else loopSite e t d.i)
  | .pre j => go (if h : j.val+1 < 64 then .pre ⟨_,h⟩ else loopSite e t d.i)
  | .nxt j => go (if h : j.val+1 < 64 then .nxt ⟨_,h⟩ else .waitS)
  | .waitS => poll .shfl4
  | .shfl4 => match ev.kind with
    | .shfl _ _ _ _ recv _ => some (some {d with site := .ldS, held := {d.held with base := recv}})
    | _ => none
  | .ldS => go .waitLd
  | .waitLd => go .shfl5
  | .shfl5 => go .shfl6
  | .shfl6 => go (if d.i = 0 then .bar20 else .waitO)
  | .waitO => poll .bar22
  | .bar22 => go .shfl7
  | .shfl7 => fold .shfl8
  | .shfl8 => fold .shfl9
  | .shfl9 => fold .shfl10
  | .shfl10 => fold .store10
  | .store10 => go .bar23
  | .bar23 => go .ldL
  | .ldL => match ev.kind with
    | .rd _ bs =>
      some (some {d with site := .shfl11, held := {d.held with word := Lib.loadWord bs}})
    | _ => none
  | .shfl11 => match ev.kind with
    | .shfl _ _ _ _ recv _ =>
      some (some {d with site := .shfl12, held := {d.held with peer := recv}})
    | _ => none
  | .shfl12 => match ev.kind with
    | .shfl _ sent _ _ recv _ => go (if skipRescale L g sent recv then .bar20 else .ldO)
    | _ => none
  | .ldO => go .waitLdO
  | .waitLdO => go .bar24
  | .bar24 => go .stO
  | .stO => go .waitStO
  | .waitStO => go .bar20
  | .bar20 => go .tmemSt
  | .tmemSt => go .tmemWait
  | .tmemWait => go .bar21
  | .bar21 => if t % 128 = 0 then go .arrive else some (some (advance e t d))
  | .arrive => some (some (advance e t d))
  | .epilogue => some none

def u32 (n : Nat) := b32 (n % 2^32)
def u64 (n : Nat) := b64 (n % 2^64)
def u16 (n : Nat) := Value.bits 16 (BitVec.ofNat 64 n)
export Lib (sx)

/-- The relative bias base after the five wide arithmetic instructions. -/
def biasBase (e : Entry) (t : Nat) :=
  (sx (e.firstToken + token t) * sx e.stride * 2 + e.rel +
    ((e.head + headInGroup t) * 1280 % 2^32) * 2 +
    sx (1280 + 2^32 - e.biasOffset) * 2 + t / 16 % 2 * 128) % 2^64

/-- If a tagged pointer survives the integer add, its address space survives too. -/
def basePlus (v : Value) (a : Nat) : Value :=
  match v with
  | .ptr _ gen target off => .ptr 32 gen target (BitVec.ofInt 64 ((off.toNat : Int) + a))
  | _ => u32 ((Lib.word v).toNat + a)

def scalarValue (e : Entry) (L : Launch) (g i r : Nat) : Value :=
  let t := g % L.block
  let n := e.split + i * e.splits
  let sb := L.sharedBase
  let rowPtr := biasBase e t
  let wide := sx (e.firstToken + token t) * sx e.stride
  let heads := (e.head + headInGroup t) * 1280 % 2^32
  match r with
  | 3 => .pred (decide (t < 32))
  | 85 => .pred (preEnabled e t)
  | 86 => .pred (decide (row t < 60)) | 87 => .pred (tokenFits e t)
  | 88 => .pred (decide (e.nbias ≤ e.split))
  | 89 => .pred (validRow e t && decide (e.nbias ≤ e.split))
  | 90 => .pred (decide (0 < e.blocks ∧ e.blocks < 2^31))
  | 91 => .pred (decide (i = e.limit)) | 92 => .pred (nextEnabled e t i)
  | 93 => .pred (decide (e.nbias ≤ n + e.splits))
  | 94 => .pred (decide (i+1 < e.blocks ∧ e.blocks < 2^31))
  | 95 => .pred (decide (i+1 < e.blocks ∧ e.blocks < 2^31 ∧ e.nbias ≤ n+e.splits))
  | 169 => .pred (decide (i = 0)) | 171 | 172 => .pred true
  | 173 => .pred (decide (e.blocks = 0 ∨ 2^31 ≤ e.blocks))
  | 175 => .pred (validRow e t) | 177 => .pred (decide (t % 128 = 0))
  | 327 => u16 (row t) | 328 => u16 (row t * 43) | 329 => u16 (token t)
  | 330 => u16 (token t * 6) | 331 => u16 (headInGroup t)
  | 462 => b32 t | 463 => e.base | 464 => b32 (t/32)
  | 478 => b32 e.split | 481 => b32 e.qlen | 483 => b32 e.nbias
  | 485 => b32 e.biasOffset | 486 => b32 e.blocks | 487 => b32 e.limit | 490 => b32 e.head
  | 491 => basePlus e.base 256 | 496 => b32 (token t) | 497 => u32 (e.head + headInGroup t)
  | 500 => u32 (sb + t%4*4) | 501 => u32 (e.splits*128) | 502 => u32 (n+e.splits)
  | 503 => u32 ((e.splits+n)*128) | 504 => b32 (i%2) | 505 => u32 (sb+i%2*8)
  | 527 => b32 e.stride | 532 => b32 e.splits | 533 => b32 e.tokens
  | 610 => e.firstWord | 623 => u32 (sb+213312) | 624 => u32 (sb+213328)
  | 666 => u32 sb | 792 => u32 (sb+212992) | 793 => b32 (t%16)
  | 794 => b32 (t/32%4*32) | 795 => b32 (t/32%4*16) | 796 => b32 (row t)
  | 797 => b32 (t*4) | 798 => b32 (t/16%2*64)
  | 801 | 802 => b32 (headInGroup t) | 803 => u32 (e.firstToken+token t)
  | 806 => b32 heads | 807 => u32 (1280+2^32-e.biasOffset)
  | 808 => b32 (t/32%4*4) | 809 => b32 (t%4*4)
  | 874 => u32 (sb+i%2*8+213280) | 875 => b32 (i/2%2) | 940 => b32 i
  | 941 => b32 (i%2*8) | 942 => b32 (i%2*128)
  | 943 => basePlus e.base (i%2*128)
  | 1532 => b32 ((i+1)%2) | 1533 => u32 (sb+212992+t/32%4*4)
  | 1709 => u32 (sb+i%2*8+213296) | 1760 => b32 0
  | 1912 => u32 (n*128) | 1913 => u32 n
  | 1956 => b64 (t/16%2*64) | 1957 => b64 rowPtr | 1958 => u64 (sx e.blocks)
  | 1959 => b64 e.limit | 1993 => b64 (i+1) | 2019 => b64 e.rel
  | 2023 => b64 e.outBase | 2024 => b64 e.lseBase
  | 2206 => u64 wide | 2207 => u64 (wide*2) | 2208 => u64 (wide*2+e.rel)
  | 2209 => u64 (wide*2+e.rel+heads*2)
  | 2210 => u64 (wide*2+e.rel+heads*2+sx (1280+2^32-e.biasOffset)*2)
  | 2446 => b64 i
  | r => if 2141 ≤ r ∧ r ≤ 2204 then u64 (sx (n*128)*2+rowPtr+2*(r-2141))
    else if 2211 ≤ r ∧ r ≤ 2274 then u64 (sx ((e.splits+n)*128)*2+rowPtr+2*(r-2211))
    else b32 0

/-- Exactly five register values depend on the last warp broadcast. -/
def valueOf (e : Entry) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  let b := (Lib.word d.held.base).toNat % 4 * 2^21
  if r = 506 then b32 b
  else if r = 944 then d.held.base
  else if r = 945 then u32 ((Lib.word d.held.base).toNat*2^21)
  else if r = 1542 then d.held.word
  else if r = 1543 then d.held.peer
  else if r = 1544 then Lib.minWord d.held.word d.held.peer
  else if r = 1534 then Lib.minWord d.held.word d.held.peer
  else if r = 1536 then Lib.minWord d.held.word d.held.peer
  else if r = 1538 then Lib.minWord d.held.word d.held.peer
  else if r = 1540 then Lib.minWord d.held.word d.held.peer
  else if r = 1611 then basePlus (basePlus e.base 256) b
  else if r = 1676 then basePlus (basePlus e.base (d.i%2*128)) b
  else scalarValue e L g d.i r


def facts (e : Entry) (L : Launch) (g : Nat) (d : D) (pc : Nat) :=
  factsFrom (ctlLive pc) (valueOf e L g d)

/-- Bounds used to interpret the signed block and token comparisons. The recorded
allocation word can have any contents. -/
structure Entry.Ok (e : Entry) : Prop where
  blockWord : e.blocks < 2^32
  limitEq : e.limit = if e.blocks < 2^31 then e.blocks else 0
  firstBits : e.firstWord.regBits.isSome
  query : e.qlen < 2^32
  bias : e.nbias < 2^31
  offsetWord : e.biasOffset < 2^32
  keyRange : e.split + (e.limit + 1) * e.splits < 2^31
  addrRange : e.tokens * e.split + 11 < 2^31

structure Inv (e : Entry) (t : Nat) (d : D) : Prop where
  entry : e.Ok
  thread : t < 256
  bound : d.i ≤ e.limit
  init : d.site = .setMaxReg ∨ d.site = .bar0 → d.i = 0
  pre : ∀ j, d.site = .pre j → d.i = 0 ∧ preEnabled e t
  nxt : ∀ j, d.site = .nxt j → nextEnabled e t d.i
  lead : d.site = .arrive → t % 128 = 0
  loop : d.site ≠ .epilogue → d.site ≠ .setMaxReg → d.site ≠ .bar0 →
    (∀ j, d.site ≠ .pre j) → d.i < e.limit

@[reducible] def code (e : Entry) (L : Launch) (g : Nat) : Code kernel Assumptions.all L g where
  D := D
  init := {}
  pc := fun d => d.site.pc
  facts := fun d => facts e L g d d.site.pc
  inv := Inv e (g % L.block)
  next := next e L g

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
