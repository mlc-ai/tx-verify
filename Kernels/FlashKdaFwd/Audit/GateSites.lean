-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.PackedNormalize

/-! Register dependencies for the eight decay/restore pairs in both preparation entries. -/
namespace FlashKda.GateSites
open PTX

/-- Registers in the order read or written by the two sides of the product. -/
structure Pair where
  gate : Nat
  query : Nat
  key : Nat
  scale : Nat
  down : Nat
  queryProd : Nat
  queryScaled : Nat
  queryBf : Nat
  negGate : Nat
  up : Nat
  keyProd : Nat
  keyBf : Nat
  deriving Repr, DecidableEq

def floatOp (op : FOp) (mode : FMode) (dst : Nat) (src : List Nat) : Instr :=
  ⟨none,.float {op,mode,ty := ⟨.f32,1⟩,ftz := true,dsts := [some dst],srcs := src.map Opnd.reg}⟩

def narrow (dst src : Nat) : Instr :=
  ⟨none,.cvt {dst := .float .bf16,src := .float .f32,rnd := some .rn,d := dst,srcs := [.reg src]}⟩

def route (r : Pair) : List Instr := [
  floatOp .ex2 .approx r.down [r.gate],
  floatOp .mul .ieee r.queryProd [r.query,r.down],
  floatOp .mul .ieee r.queryScaled [r.scale,r.queryProd],
  narrow r.queryBf r.queryScaled,
  floatOp .neg .ieee r.negGate [r.gate],
  floatOp .ex2 .approx r.up [r.negGate],
  floatOp .mul .ieee r.keyProd [r.up,r.key],
  narrow r.keyBf r.keyProd]

def pcs (packed : Bool) : List (Nat × Nat) :=
  if packed then [(569,589),(581,595),(609,629),(621,635),(651,671),(663,677),(691,711),(703,717)]
  else [(513,533),(525,539),(553,573),(565,579),(595,615),(607,621),(635,655),(647,661)]

def sites (packed : Bool) : Option (List (List Instr)) := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[if packed then 1 else 9]!).toOption
  (pcs packed).mapM fun (pos,neg) => do
    let decodeAt := fun i => (Decode.code p.env i ((p.instrs.drop i).take 4)).toOption
    return (← decodeAt pos) ++ (← decodeAt neg)

def fixedPairs : List Pair := [
  ⟨483,585,588,1247,482,589,484,122,491,490,492,126⟩,
  ⟨487,592,595,1247,486,596,488,124,495,494,496,128⟩,
  ⟨499,599,602,1247,498,603,500,130,507,506,508,134⟩,
  ⟨503,606,609,1247,502,610,504,132,511,510,512,136⟩,
  ⟨515,615,618,1247,514,619,516,138,523,522,524,142⟩,
  ⟨519,622,625,1247,518,626,520,140,527,526,528,144⟩,
  ⟨531,629,632,1247,530,633,532,146,539,538,540,150⟩,
  ⟨535,636,639,1247,534,640,536,148,543,542,544,152⟩]

/-- The packed entry has three additional 16-bit registers below the narrow results
and fourteen additional registers below all the binary32 operands in these regions. -/
def shifted (r : Pair) : Pair :=
  ⟨r.gate+14,r.query+14,r.key+14,r.scale+14,r.down+14,r.queryProd+14,r.queryScaled+14,
   r.queryBf+3,r.negGate+14,r.up+14,r.keyProd+14,r.keyBf+3⟩

set_option maxRecDepth 80000 in
set_option maxHeartbeats 24000000 in
/-- The exponents have opposite signs and the narrowing conversions occur after the
displayed multiplications at every one of the eight paired positions in either kernel. -/
theorem decoded (packed : Bool) : sites packed =
    some ((if packed then fixedPairs.map shifted else fixedPairs).map route) := by
  cases packed <;> rfl

end FlashKda.GateSites
