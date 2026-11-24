-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine

@[expose] public section

/-! # Words of the code that the roles running the scheduler share

The arithmetic the output warp does not use, the chosen request's coordinates, the launch's used-K
length of a request and the output warp's sites a scheduler step reaches. Nothing here reads a
role's machine. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (tilesOf prefixOf addrU addrS Scan laneW ctaW paramW
  batchOf skipFirst reqOf skipLoop tlOf prefixD headsW lanePreds partials loopRegs chosen loopOf)

noncomputable section

/-! ### Arithmetic of the code that the output warp does not use -/

abbrev ori (x : BitVec 64) (n : Int) : BitVec 64 := r32 x ||| i32 n
abbrev xori (x : BitVec 64) (n : Int) : BitVec 64 := r32 x ^^^ i32 n
abbrev neg32 (x : BitVec 64) : BitVec 64 := truncBits 32 (0 - r32 x)

/-- The blocks of 128 rows that `x` rows need (rounded up), as the code computes them. -/
def ceil128 (x : BitVec 64) : BitVec 64 :=
  let s := add32 x (shru (shrs x 31) 25)
  add32 (shrs s 7) (sel (scmpi .gt .s x (-1) && scmp .ne .b x (andi s (-128))) (i32 1) (i32 0))

/-- The shared-memory base. -/
abbrev sbW (L : Launch) : BitVec 64 := BitVec.ofNat 64 L.sharedBase
/-- A 32-bit word of the shared base plus `n`. -/
abbrev sbi (L : Launch) (n : Int) : Value := .bits 32 (addi (sbW L) n)
abbrev w32 (x : BitVec 64) : Value := .bits 32 x

/-- The 64-bit index of the chosen request (`mul.wide.s32 … 4`). -/
abbrev wideS (i : BitVec 64) : Value :=
  .bits 64 (truncBits (2 * 32) (BitVec.ofInt 64 (toSigned 32 (r32 i) * toSigned 32 (i32 4))))

/-- The chosen request's coordinates as the MMA warp computes them: the row offset `%r6142`
and the operands of its two divisions. -/
structure Coords where
  row : BitVec 64
  n1 : BitVec 64
  d1 : BitVec 64
  n2 : BitVec 64
  d2 : BitVec 64

def coords (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : Coords :=
  let heads := headsW p
  let k := paramW 800
  let r126 := sub32 c.cur (mul32 c.tot heads)
  let r1445 := sub32 (ctaW L g) (add32 r126 c.pv)
  let r1446 := shl c.nt 8
  let r1454 := sel (scmp .gt .s (shrs r1446 3) k) (sel (scmp .gt .s (shrs r1446 4) k)
    (sel (scmp .gt .s (shrs r1446 5) k) (sel (scmp .gt .s (shrs r1446 6) k) (i32 1) (i32 2))
      (i32 4)) (i32 8)) (i32 16)
  let r1455 := min32 r1454 heads
  let r1456 := mul32 r1455 c.nt
  let r1461 := fdiv r1445 r1456
  let r1463 := sub32 r1445 (mul32 r1461 r1456)
  let r1464 := mul32 r1461 r1455
  let r1467 := sel (scmp .gt .s (add32 r1464 r1455) heads) (sub32 heads r1464) r1455
  let r1468 := sdiv r1463 r1467
  let r1471 := sel (scmp .eq .b r1463 (mul32 r1467 r1468) || scmpi .gt .s (xor32 r1467 r1463) (-1))
    (i32 (-1)) (i32 0)
  ⟨addi (shl (add32 (sub32 c.nt r1468) r1471) 8) 256, r1445, r1456, r1463, r1467⟩

/-- The launch's used-K length of request `i`. -/
def ukv (p : Params) (i : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (p.kLength (Epilogue.r32 i).toNat)

/-- The output warp's sites that an MMA scheduler step reaches. -/
def backE : Epilogue.Site → Bool
  | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ | .q0 | .q1 | .exit _ =>
    true
  | .ready st => st = 0
  | _ => false

/-- The second pass's output-warp sites. -/
def lateE : Epilogue.Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .exit l => l
  | _ => false

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
