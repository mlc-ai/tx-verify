-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Sites
public import Kernels.InklingRelDecode.Proof.Lib.RawArith

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

/-- Only the request words enter a control decision. The six block-table payloads
and the 64 query payloads affect copy coordinates and stored data. -/
structure D where
  site : Site := .sMax
  first : Value := b32 0
  last : Value := b32 0
  seq : Value := b32 0
  elected : Bool := false
  broadcast : Value := b32 0

noncomputable section

/-- The tag on the left operand of sub.s32 survives a successful pointer subtraction. -/
def subValue (a b : Value) : Value :=
  match a with
  | .ptr _ gen sp off =>
    .ptr 32 gen sp (BitVec.ofInt 64 ((off.toNat : Int)-toSigned 32 (Lib.word b)))
  | _ => .bits 32 (sub32 (Lib.word a) (Lib.word b))

def qlen (d : D) := Lib.word (subValue d.last d.first)
def past (d : D) := Lib.word (subValue d.seq (subValue d.last d.first))

/-- Signed division by 128 rounds toward zero. The instruction sequence biases a
negative numerator before the arithmetic shift. -/
def div128 (x : BitVec 64) := shrs (add32 x (shru (shrs x 31) 25)) 7

def iters (splits split : Nat) (blocks : BitVec 64) :=
  let denom := BitVec.ofNat 64 splits
  let num := add32 (add32 denom (not32 (BitVec.ofNat 64 split))) blocks
  intBits 32 ((intOf .s 32 (r32 num)).tdiv (intOf .s 32 (r32 denom)))

def positive (x : BitVec 64) := if scmpi .gt .s x 0 then r32 x else 0

def preload (splits split : Nat) (d : D) :=
  let all := positive (iters splits split (div128 (addi (Lib.word d.seq) 127)))
  let old := positive (iters splits split (div128 (past d)))
  (min32 old all).toNat

/-- Each 16-load group serves one of four rows separated by 16. -/
def queryOn (tid group : Nat) (d : D) : Bool :=
  let row := tid/8%16 + 16*group
  decide (row < 60) && scmp .gt .s (qlen d) (BitVec.ofNat 64 (row*10923/65536))

def querySite (tid : Nat) (d : D) (group : Nat) : Site :=
  if group ≤ 0 && queryOn tid 0 d then .ldq 0
  else if group ≤ 1 && queryOn tid 1 d then .ldq 16
  else if group ≤ 2 && queryOn tid 2 d then .ldq 32
  else if group ≤ 3 && queryOn tid 3 d then .ldq 48
  else .stq 0 0

def afterInit (i : Fin 12) : Site := if h : i.val+1 < 12 then .el ⟨_,h⟩ else .fnc0

def afterCopy (d : D) (tid n : Nat) (b : Fin 3) : Fin 4 → Site
  | 0 => .pb b 2
  | 1 => .lb b 1
  | 2 => .pb b 4
  | 3 => if h : b.val+1 < 3 then
      if (if b.val=0 then n≠1 else ¬n<3) then .pb ⟨_,h⟩ 0 else querySite tid d 0
    else querySite tid d 0

def afterQuery (d : D) (tid : Nat) (j : Fin 64) : Site :=
  if h : j.val+1 < 64 then
    if (j.val+1)%16=0 then querySite tid d ((j.val+1)/16) else .ldq ⟨_,h⟩
  else .stq 0 0

def afterStore (i : Fin 8) (j : Fin 4) : Site :=
  if h : j.val+1 < 4 then .stq i ⟨_,h⟩
  else if h : i.val+1 < 8 then .stq ⟨_,h⟩ 0 else .fnc1

/-- The control successor retains a rebuilt request value with its original tag.
An invalid byte list makes the concrete load continuation fault. -/
def next (Q : Params) (L : Launch) (g : Nat) (d : D) (ev : Event) : Option (Option D) :=
  let tid := g % L.block
  let n := preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d
  let go := fun s => some (some {d with site := s})
  let elect := fun (choose : Bool → Site) => match ev.kind with
    | .elect _ _ leader =>
      let won := laneOf L g == leader
      some (some {d with site := choose won, elected := won})
    | _ => none
  match d.site with
  | .sMax => go (.ld 0)
  | .ld i => match ev.kind with
    | .rd _ bs =>
      let v := (rebuild 3 bs).toOption.getD (b32 0)
      match i with
      | 0 => some (some {d with first := v, site := .ld 1})
      | 1 => some (some {d with last := v, site := .ld 2})
      | 2 => some (some {d with seq := v, site := .el 0})
    | _ => none
  | .el i => elect fun won => if tid < 32 && won then .init i else afterInit i
  | .init i => go (afterInit i)
  | .fnc0 => go .bar2
  | .bar2 => go (if n = 0 then querySite tid d 0 else .pb 0 0)
  | .pb b 0 => go (if tid%128=0 then .arr b else .lb b 0)
  | .pb b 1 => go (.psh b)
  | .pb b 2 => go (.pel b 1)
  | .pb b 3 => go (.pel b 2)
  | .pb b 4 => go (.pel b 3)
  | .arr b => go (.lb b 0)
  | .lb b 0 => go (.pb b 1)
  | .lb b 1 => go (.pb b 3)
  | .psh b =>
    let payload := match ev.kind with | .shfl _ _ _ _ recv _ => recv | _ => d.broadcast
    some (some {d with site := .pel b 0, broadcast := payload})
  | .pel b j => elect fun won => if tid%128 < 64 && won then .ptc b j else afterCopy d tid n b j
  | .ptc b j => go (afterCopy d tid n b j)
  | .ldq j => go (afterQuery d tid j)
  | .stq i j => go (afterStore i j)
  | .fnc1 => go .st8
  | .st8 => go (.st9 0)
  | .st9 0 => go (.st9 1)
  | .st9 1 => go .bar18
  | .bar18 => go .exit
  | .exit => some none

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
