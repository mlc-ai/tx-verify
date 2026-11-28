-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Sites
public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Live
public import Kernels.InklingRelDecode.Proof.Lib.AddBase
public import Kernels.InklingRelDecode.Proof.Lib.RawArith
public import Kernels.InklingRelDecode.Proof.Lib.WideBits
public import Kernels.InklingRelDecode.Proof.Iface.Objects
public import Lemmas.Flow.CodeU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof Arith32

/-- The numbers the store addresses are built from, with what the handoff proves of them: the
first token is read as integer bits and the token index fits a signed word. -/
structure Addr where
  split : Nat
  head : Nat
  tokens : Nat
  firstWord : Value
  outBase : Nat
  lseBase : Nat
  good : firstWord.regBits.isSome ∧ tokens * split + 11 < 2^31

structure Entry where
  base : Value
  skip : Bool
  valid : Bool
  addr : Addr

abbrev Entry.split (e : Entry) := e.addr.split
abbrev Entry.head (e : Entry) := e.addr.head
abbrev Entry.tokens (e : Entry) := e.addr.tokens
abbrev Entry.firstWord (e : Entry) := e.addr.firstWord
abbrev Entry.outBase (e : Entry) := e.addr.outBase
abbrev Entry.lseBase (e : Entry) := e.addr.lseBase

noncomputable def Entry.firstToken (e : Entry) := (Lib.word e.firstWord).toNat

def row (t : Nat) := t % 16 + t / 32 % 4 * 16
def token (t : Nat) := row t * 43 / 256
def headInGroup (t : Nat) := row t - token t * 6
def u32 (n : Nat) := b32 (n % 2^32)
def u64 (n : Nat) := b64 (n % 2^64)
export Lib (sx)

/-- The tile index of a thread: `(first + tokens * split + token) * 12 + head`, as a word. -/
noncomputable def Entry.tile (e : Entry) (t : Nat) :=
  ((e.firstToken + (e.tokens * e.split + token t)) * 12 + (e.head + headInGroup t)) % 2^32

/-- The address of the first word of the output row, and of the thread's column. -/
noncomputable def Entry.rowAddr (e : Entry) (t : Nat) := e.outBase + sx (e.tile t * 128 % 2^32) * 4

structure D where
  site : Site := .wait
  received : Value := b32 0

def lead (t : Nat) := scmpi .eq .b (andi (W t) 16) 0

def firstStore (v lead : Bool) : Site := if v then (if lead then .lse else .store 0) else .join

def storeAt (n : Nat) : Site := if h : n<64 then .store ⟨n,h⟩ else .join

def next (e : Entry) (L : Launch) (g : Nat) (d : D) (ev : Event) : Option (Option D) :=
  let t := g%L.block
  let go := fun s => some (some {d with site := s})
  match d.site with
  | .wait => match ev.kind with
    | .wait _ _ ok _ _ => if ok then go (if e.skip then firstStore e.valid (lead t) else .shfl)
      else some (some d)
    | _ => none
  | .shfl => match ev.kind with
    | .shfl _ _ _ _ x _ => some (some ⟨.load,x⟩)
    | _ => none
  | .load => go .waitLd
  | .waitLd => go (firstStore e.valid (lead t))
  | .lse => go (.store 0)
  | .store j => go (storeAt (j.val+1))
  | .join => go .setMax | .setMax => go .roleWord | .roleWord => go .sync1 | .sync1 => go .sync0
  | .sync0 => go (if t<32 then .dealloc else .exit)
  | .dealloc => go .exit | .exit => none

noncomputable def scalarValue (e : Entry) (L : Launch) (g : Nat) (r : Nat) : Value :=
  let t := g%L.block
  match r with
  | 3 => .pred (decide (t<32)) | 173 => .pred e.skip | 175 => .pred e.valid
  | 478 => b32 e.split | 496 => b32 (token t) | 497 => u32 (e.head + headInGroup t)
  | 533 => b32 e.tokens | 610 => e.firstWord | 1956 => b64 (t/16%2*64)
  | 2023 => b64 e.outBase | 2024 => b64 e.lseBase
  | 1896 => u32 (e.tokens * e.split + token t)
  | 1897 => u32 (e.firstToken + (e.tokens * e.split + token t))
  | 1898 => b32 (e.tile t) | 1900 => u32 (e.tile t * 128)
  | 2379 => u64 (e.lseBase + sx (e.tile t) * 4) | 2444 => u64 (e.rowAddr t)
  | 2445 => u64 (t/16%2*64*4)
  | 174 => .pred (lead t && e.valid) | 176 => .pred (lead t)
  | 462 => b32 t | 463 => e.base | 464 => b32 (t/32)
  | 491 => Lib.addBase e.base 256 | 624 => b32 ((L.sharedBase+Iface.oFinal)%2^32)
  | 1760 => b32 0 | 1899 => .bits 32 (andi (W t) 16)
  | _ => if 2380 ≤ r ∧ r ≤ 2443 then u64 (e.rowAddr t + t/16%2*256 + 4*(r-2380)) else b32 0

noncomputable def valueOf (e : Entry) (L : Launch) (g : Nat) (v : Value) (r : Nat) : Value :=
  let b := (Lib.word v).toNat
  if r = 1827 then Lib.addBase (Lib.addBase e.base 256) (b%4*2^21)
  else if r = 1828 then v
  else if r = 1829 then b32 (b*2^21%2^32)
  else if r = 1830 then b32 (b%4*2^21)
  else scalarValue e L g r

noncomputable def facts (e : Entry) (L : Launch) (g : Nat) (v : Value) (pc : Nat) :=
  factsFrom (ctlLive pc) (valueOf e L g v)

def Inv (e : Entry) (t : Nat) (d : D) : Prop := match d.site with
  | .lse => e.valid=true ∧ lead t=true
  | .store _ => e.valid=true
  | .dealloc => t<32
  | _ => True

@[reducible] noncomputable def code (e : Entry) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g where
  D := D
  init := {}
  pc d := d.site.pc
  facts d := facts e L g d.received d.site.pc
  inv := Inv e (g%L.block)
  next := next e L g

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
