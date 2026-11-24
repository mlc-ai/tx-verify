-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Data.NormMachine
import Kernels.FlashKdaFwd.Audit.NormSums

/-! Symbolic register evaluation of the normalization in two compiled CUDA binaries. The
covered instruction forms are specific to this slice. Inputs are the two loaded shared arrays;
each fused multiply-add and each standalone addition remains a separate expression node. -/
namespace FlashKda.Binary

inductive Expr where
  | unknown (register : String) | zero | epsilon | thread | address | timesEight
  | otherLane | quarterThread | rowOffset
  | input (key : Bool) (element : Nat)
  | word (low high : Expr) | lo (v : Expr) | hi (v : Expr)
  | fma (a b c : Expr) | add (a b : Expr) | shuffle (distance : Nat) (source : Expr)
  | root (x : Expr)
  deriving Repr, DecidableEq

open Expr

def low : Expr → Expr | word a _ => a | .zero => .zero | x => lo x
def high : Expr → Expr | word _ b => b | .zero => .zero | x => hi x

abbrev Registers := List (String × Expr)
def readOperand (rs : Registers) (r : String) : Expr :=
  if r = "RZ" then .zero
  else if r = "9.9999999747524270788e-07" then epsilon
  else (rs.lookup r).getD (unknown r)

def loadWords (rs : Registers) (key : Bool) (regs : List String) : Registers :=
  (regs.zipIdx.map fun (r,i) => (r, word (input key (2*i)) (input key (2*i+1)))) ++ rs

/-- Follow the first thread of a row at the conditional branch. The shuffle nodes represent
values from their peer lanes and are built before the branch. Unrecognized forms are rejected. -/
def instruction (rs : Registers) (tokens : List String) : Option Registers := do
  let val := readOperand rs
  let put := fun (d : String) (v : Expr) => some ((d,v)::rs)
  match tokens with
  | ["S2R",d,"SR_TID.X"] => put d thread
  | ["LEA",d,a,"UR4","0x4"] =>
    guard (val a = thread)
    put d address
  | ["LDS.128","R4","[R16]"] =>
    guard (val "R16" = address)
    return loadWords rs false ["R4","R5","R6","R7"]
  | ["LDS.128","R8","[R16+0x1000]"] =>
    guard (val "R16" = address)
    return loadWords rs true ["R8","R9","R10","R11"]
  | ["PRMT",d,a,"0x7632",b] => put d (word (high (val a)) (high (val b)))
  | ["IMAD.U32",d,a,"0x10000","RZ"] | ["SHF.L.U32",d,a,"0x10","RZ"] =>
    put d (word .zero (low (val a)))
  | ["FFMA.FTZ",d,a,b,c] => put d (fma (val a) (val b) (val c))
  | ["SHFL.BFLY","PT",d,a,b,"0x1f"] =>
    let delta ← [("0x8",8),("0x4",4),("0x2",2),("0x1",1)].lookup b
    put d (shuffle delta (val a))
  | ["FADD.FTZ",d,a,b] => put d (add (val a) (val b))
  | ["IMAD.SHL.U32",d,a,"0x8","RZ"] =>
    guard (val a = thread)
    put d timesEight
  | ["LOP3.LUT",d,"RZ",a,"0x78","RZ","0xc0","!PT"] =>
    guard (val a = timesEight)
    put d otherLane
  | ["@P0","BRA","0xf00"] =>
    guard (val "P0" = otherLane)
    return rs
  | ["SHF.R.U32.HI",d,"RZ","0x2",a] =>
    guard (val a = thread)
    put d quarterThread
  | ["LOP3.LUT",d,a,"0x3c","RZ","0xc0","!PT"] =>
    guard (val a = quarterThread)
    put d rowOffset
  | ["MUFU.RSQ",d,a] => put d (root (val a))
  | ["STS",dest,a] =>
    guard (val "R5" = rowOffset)
    put dest (val a)
  | _ => none

def result : Option (Expr × Expr) := do
  let rs ← instructions.foldlM instruction []
  return (← rs.lookup "[R5+UR4+0x4000]", ← rs.lookup "[R5+UR4+0x4080]")

def expected (key : Bool) : Expr :=
  let accum := (List.range 8).foldl (fun acc i =>
    let x := word .zero (input key i)
    fma x x acc) .zero
  let total := [8,4,2,1].foldl (fun a d => add a (shuffle d a)) accum
  root (add total epsilon)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The binary data paths preserve the two PTX reduction trees through the shared result stores. -/
theorem binary_routes : result = some (expected false, expected true) := by decide +kernel

end FlashKda.Binary
