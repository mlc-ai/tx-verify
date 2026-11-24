-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.FullDecode
import Core.Sync.Shuffle

/-! Register and thread routing of the fixed-length preparation kernel's two square sums. -/
namespace FlashKda.Normalize
open PTX

/-- Load eight adjacent bfloat16 coordinates as four words, then unpack the word pairs. -/
def loadCoordinates (off : Int) (word half : Nat) : List Instr :=
  [⟨none, .mem {
    kind := .load, elem := .int .b 32, vec := 4, sem := .weak,
    space := some (.shared .cta), addr := ⟨.reg 294 32, off⟩,
    dsts := (List.range 4).map (fun i => some (word+i)) }⟩] ++
  (List.range 4).reverse.map fun i =>
    ⟨none, .move ⟨.unpack, .int .b 32, [some (half+4*i), some (half+4*i+2)], [.reg (word+i)]⟩⟩

def widen (dst src : Nat) : Instr :=
  ⟨none, .cvt { dst := .float .f32, src := .float .bf16, d := dst, srcs := [.reg src] }⟩

def sumSquare (dst src : Nat) (previous : Opnd) : Instr :=
  ⟨none, .float {
    op := .fma, ty := ⟨.f32, 1⟩, rnd := some .rn, ftz := true,
    dsts := [some dst], srcs := [.reg src, .reg src, previous] }⟩

/-- Each lane accumulates separate query and key squares over its eight local coordinates. -/
def laneSquares : List Instr :=
  loadCoordinates 0 295 90 ++ [widen 271 90] ++ loadCoordinates 4096 299 91 ++
  [widen 272 91, sumSquare 303 271 (.f32imm 0), sumSquare 304 272 (.f32imm 0)] ++
  (List.range 7).flatMap fun i =>
    [widen (273+2*i) (92+2*i), widen (274+2*i) (93+2*i),
     sumSquare (305+2*i) (273+2*i) (.reg (303+2*i)),
     sumSquare (306+2*i) (274+2*i) (.reg (304+2*i))]

def exchangeAndAdd (delta input temp predicate result : Nat) : List Instr :=
  [⟨none, .warp {
    kind := .shfl .bfly, ty := some (.int .b 32),
    dsts := [some temp, some predicate], srcs := [.reg input, .imm delta, .imm 31],
    mask := some (.imm (-1)) }⟩,
   ⟨none, .float {
    op := .add, ty := ⟨.f32, 1⟩, ftz := true,
    dsts := [some result], srcs := [.reg input, .reg temp] }⟩]

/-- The last round writes the two sums to the registers that feed normalization. -/
def warpSquares : List Instr :=
  exchangeAndAdd 8 317 319 3 320 ++ exchangeAndAdd 8 318 321 4 322 ++
  exchangeAndAdd 4 320 323 5 324 ++ exchangeAndAdd 4 322 325 6 326 ++
  exchangeAndAdd 2 324 327 7 328 ++ exchangeAndAdd 2 326 329 8 330 ++
  exchangeAndAdd 1 328 331 9 208 ++ exchangeAndAdd 1 330 332 10 209

def squareWindow : Option (List Instr) := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[9]!).toOption
  (Decode.code p.env 80 ((p.instrs.drop 80).take 58)).toOption

set_option maxRecDepth 50000 in
set_option maxHeartbeats 6000000 in
theorem production_reduction : squareWindow = some (laneSquares ++ warpSquares) := by rfl

/-- Follow both operands of the four additions backwards to their contributing lanes. -/
def contributingLanes : List Nat → Nat → List Nat
  | [], lane => [lane]
  | distance :: rest, lane => contributingLanes rest lane ++
      contributingLanes rest (shflSource .bfly lane distance 31).1

def coordinates (lane : Nat) : List Nat :=
  (contributingLanes [1,2,4,8] lane).flatMap fun source =>
    List.range' (8 * (source % 16)) 8

set_option maxRecDepth 50000 in
set_option maxHeartbeats 6000000 in
theorem row_coverage : ∀ lane : Fin 32,
    ((contributingLanes [1,2,4,8] lane.val).all (fun src => src / 16 == lane.val / 16)) = true ∧
    (coordinates lane.val).Perm (List.range 128) := by decide +kernel

/-- Every input coordinate contributes once, for each of the two independent rows. -/
theorem coordinate_permutation (lane : Fin 32) : (coordinates lane.val).Perm (List.range 128) :=
  (row_coverage lane).2

end FlashKda.Normalize
