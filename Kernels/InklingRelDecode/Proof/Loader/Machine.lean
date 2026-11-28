-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Flow.Sites
public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Arith32
public import Lemmas.Flow.RegBits
public import Lemmas.Flow.Scalars

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Each election controls a pair of copies. Two pairs serve each page. -/
inductive Site where
  | dec | first | second | beginBar | poll | readyBar | arrive
  | page (upper : Bool)
  | warpBar (pair : Fin 4)
  | elect (pair : Fin 4)
  | copy (pair : Fin 4) (second : Bool)
  | endBar | inc | dispatch
  deriving DecidableEq

def Site.pc : Site → Nat
  | .dec => 2344 | .first | .second => 2345 | .beginBar => 2346
  | .poll => 2374 | .readyBar => 2377 | .arrive => 2378
  | .page false => 2382 | .page true => 2399
  | .warpBar p => [2387, 2392, 2401, 2407][p.val]!
  | .elect p => [2388, 2393, 2403, 2409][p.val]!
  | .copy p s => [2389, 2394, 2404, 2410][p.val]! + (if s then 2 else 0)
  | .endBar => 2419 | .inc => 2420 | .dispatch => 2337

structure D where
  site : Site := .dec
  counter : Value := b32 0
  limit : Value := b32 0
  page0 : Value := b32 0
  page1 : Value := b32 0

def bits (v : Value) : BitVec 64 := truncBits 32 (v.regBits.getD 0)

def finishPair (d : D) (p : Fin 4) : D :=
  match p.val with
  | 0 => {d with site := .warpBar 1}
  | 1 => {d with site := .page true}
  | 2 => {d with site := .warpBar 3}
  | _ =>
    let i := truncBits 32 (bits d.counter + 1)
    {d with counter := .bits 32 i, site := if i = bits d.limit then .endBar else .poll}

def readResult (e : Event) (f : Value → D) : Option (Option D) := do
  let .rd _ bs := e.kind | none
  let v ← (rebuild 3 bs).toOption
  pure (some (f v))

/-- The two counter words and both page words are retained verbatim. If a local
instruction cannot consume a word, StepAtU admits the resulting terminal fault at
the crossing to the predicted site. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  let go := fun s => some (some {d with site := s})
  match d.site with
  | .dec => go .first
  | .first => readResult e fun v => {d with counter := v, site := .second}
  | .second => readResult e fun v => {d with limit := v, site := .beginBar}
  | .beginBar => go (if toSigned 32 (bits d.limit) ≤ toSigned 32 (bits d.counter)
      then .endBar else .poll)
  | .poll => match e.kind with
    | .wait _ _ ok _ _ => go (if ok then .readyBar else .poll)
    | _ => none
  | .readyBar => go (if laneOf L g = 0 then .arrive else .page false)
  | .arrive => go (.page false)
  | .page false => readResult e fun v => {d with page0 := v, site := .warpBar 0}
  | .page true => readResult e fun v => {d with page1 := v, site := .warpBar 2}
  | .warpBar p => go (.elect p)
  | .elect p => match e.kind with
    | .elect _ _ lead =>
      if laneOf L g = lead then go (.copy p false) else some (some (finishPair d p))
    | _ => none
  | .copy p false => go (.copy p true)
  | .copy p true => some (some (finishPair d p))
  | .endBar => go .inc
  | .inc => go .dispatch
  | .dispatch => some none

open Arith32

/-- The quotient of the signed counter by three as computed at 2365–2367. -/
def quotient (i : BitVec 64) : BitVec 64 :=
  let hi := r32 (BitVec.ofInt 64 (toSigned 32 (r32 i) * 1431655766 / 2 ^ 32))
  add32 hi (shru hi 31)

def wide (a c : BitVec 64) : BitVec 64 :=
  intBits 64 (intOf .s 32 (r32 a) * 4 + intOf .s 64 (truncBits 64 c))

/-- Registers live across event boundaries. The loop-carried address registers use the
counter modulo 32 bits. The recorded allocation word at register 463 is carried unchanged. -/
def loopValue (L : Launch) (g : Nat) (w : Value) (inheritReg : Nat → Value) (d : D) :
    Nat → Value :=
  let paramW := fun r => bits (inheritReg r)
  let coord := fun axis => r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get axis))
  let i := bits d.counter
  let q := quotient i
  let base := r32 (BitVec.ofNat 64 L.sharedBase)
  let bar := add32 base (mad32 q (i32 (-24)) (shl i 3))
  let tile := add32 base (mad32 q (i32 (-98304)) (shl i 15))
  let row := mul32 (paramW 530) (coord .y)
  let col := mul32 (paramW 531) (coord .y)
  let slab := shl (mad32 (paramW 532) i (coord .x)) 7
  let bt := ((inheritReg 2020).regBits.getD 0)
  let btReq := wide (mul32 (paramW 528) (coord .z)) bt
  let addr := wide (shrs slab 6) btReq
  let values : List (Nat × Value) :=
    [(463, w),
     (1905, d.counter),
     (467, d.limit),
     (20, .pred (decide (laneOf L g = 0))),
     (21, .pred true),
     (22, .pred true),
     (23, .pred true),
     (24, .pred true),
     (1904, .bits 32 (shl i 3)),
     (1903, .bits 32 (shl i 15)),
     (1902, .bits 32 slab),
     (1950, .bits 64 btReq),
     (470, .bits 32 row),
     (583, .bits 32 col),
     (586, .bits 32 (addi col 64)),
     (588, .bits 32 (addi col 128)),
     (590, .bits 32 (addi col 192)),
     (599, .bits 32 q),
     (602, .bits 32 base),
     (603, .bits 32 bar),
     (578, .bits 32 (addi bar 213248)),
     (580, .bits 32 (addi bar 213216)),
     (579, .bits 32 (andi (not32 q) 1)),
     (582, .bits 32 tile),
     (585, .bits 32 (addi tile 16384)),
     (587, .bits 32 (addi tile 98304)),
     (589, .bits 32 (addi tile 114688)),
     (592, .bits 32 (addi tile 8192)),
     (594, .bits 32 (addi tile 24576)),
     (595, .bits 32 (addi tile 106496)),
     (596, .bits 32 (addi tile 122880)),
     (584, .bits 32 (mad32 (bits d.page0) (paramW 529) row)),
     (593, .bits 32 (mad32 (bits d.page1) (paramW 529) row)),
     (2053, .bits 64 addr),
     (2054, .bits 64 (truncBits 64 (truncBits 64 addr + 4)))]
  fun r => (values.lookup r).getD (inheritReg r)

def inherited (w : Value) (regs : Nat → Value) (r : Nat) : Value :=
  if r = 463 then w else regs r

def valueOf (L : Launch) (g : Nat) (w : Value) (regs : Nat → Value) (d : D) : Nat → Value :=
  match d.site with
  | .dec | .first | .second | .dispatch | .inc | .endBar => inherited w regs
  | .beginBar => fun r =>
    if r = 1905 then d.counter else if r = 467 then d.limit else inherited w regs r
  | _ => loopValue L g w regs d

@[reducible] def code (L : Launch) (g : Nat) (w : Value) (inheritReg : Nat → Value) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := {}
  pc := (·.site.pc)
  facts := fun d => factsFrom (Flow.live d.site.pc) (valueOf L g w inheritReg d)
  sub := fun d => if d.site = .second then 1 else 0
  acc := fun d => if d.site = .second then [d.counter] else []
  inv := fun d => d.site = .arrive → laneOf L g = 0
  next := next L g

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
