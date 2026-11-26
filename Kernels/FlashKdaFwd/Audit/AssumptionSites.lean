-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Assumptions
public import Kernels.FlashKdaFwd.Spec

@[expose] public section

/-!
# Site audit of the FlashKDA assumptions

Two assumptions of the kernel select instructions: `inputReadOnly` by a list of instruction
indices, `sharedBits` by instruction form. This file checks, by evaluating scans of the decoded
program, that they select what their statements say and nothing else.

* `inputReadSites` are exactly the `ld.global` instructions of the program, 21 plain weak loads
  of one 64-bit word. Every other load names shared memory or the parameters, or is one of the
  138 generic (space-less) `ld.b32`; where those read is a matter of the pointer they are given
  (the proof shows it is a generic pointer into shared memory).
* The forms `sharedBits` reads, `shr.u64 x, p, 3` and `xor.b64 q, y, p` of two registers, occur
  only in the 266 address computations `shr.u64 x, p, 3; and.b64 y, x, 16; xor.b64 q, y, p`
  (`swizzleSites`: 10 in the conversion of the initial state, 128 before the loads and 128
  before the stores of the per-thread carry), each directly followed by the generic 32-bit load
  or store through `q`. So the two single-instruction rules of `sharedBits` only ever act
  together, as the swizzle of one address, as its statement describes.
-/

namespace PTX.Kernels.FlashKdaFwd.Assumptions
open PTX

/-- **`inputReadSites` are exactly the `ld.global` instructions of the program**, and each is a
plain (not `.nc`) weak load of one 64-bit word. -/
theorem inputRead_sites :
    (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .mem a => a.kind == .load && a.space == some .global
      | _ => false)).map (·.2) = inputReadSites ∧
    (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .mem a => a.kind == .load && a.space == some .global && !a.nc && a.sem == .weak &&
          a.vec == 1 && a.elem == .int .b 64 && a.ext == .same
      | _ => false)).map (·.2) = inputReadSites ∧
    inputReadSites.length = 21 := by
  refine ⟨?_, ?_, rfl⟩ <;> decide +kernel

/-- Whether a load names shared memory or the parameters. -/
def sharedOrParam : Option StateSpace → Bool
  | some (.shared _) => true
  | some .param => true
  | _ => false

/-- The other loads: 138 generic `ld.b32` (no state space in the instruction), and loads that
name shared memory or the parameters. No load is `.nc`. -/
theorem other_loads :
    (kernel.code.zipIdx.filter (fun p => match p.1.op with
      | .mem a => a.kind == .load && a.space == none
      | _ => false)).length = 138 ∧
    kernel.code.zipIdx.all (fun p => match p.1.op with
      | .mem a => a.kind != .load || inputReadSites.contains p.2 || !a.nc &&
          (a.space == none || sharedOrParam a.space)
      | _ => true) = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- The instruction indices of the `shr.u64 x, p, 3` that start an address swizzle. -/
def swizzleSites : List Nat :=
  [423, 440, 470, 487, 510, 527, 550, 567, 590, 607] ++
    (List.range 128).map (762 + 5 * ·) ++ (List.range 128).map (3129 + 5 * ·)

/-- Whether `op` is a generic 32-bit load or store whose address is the register `q`. -/
def genericAccess (q : Nat) : Op → Bool
  | .mem a => a.space == none && a.elem == .int .b 32 && a.addr == ⟨.reg q 64, 0⟩
  | _ => false

/-- The destination, source and mask of `and.b64 y, x, 16`. -/
def swizzleMask : Op → Option (Nat × Nat)
  | .int ⟨.and, .int .b 64, false, [some y], [.reg x, .imm 16]⟩ => some (y, x)
  | _ => none

/-- Whether four consecutive instructions are `shr.u64 x, p, 3; and.b64 y, x, 16;
xor.b64 q, y, p` and a generic 32-bit load or store whose address is the register `q`. -/
def swizzleAt (a b c d : Instr) : Bool :=
  match swizzleShift a.op, swizzleMask b.op, swizzleXor c.op with
  | some (x, p), some (y, x'), some (q, y', p') =>
    x == x' && y == y' && p == p' && genericAccess q d.op
  | _, _, _ => false

/-- The indices, from `pc` on, at which `swizzleAt` holds of the next four instructions. -/
def swizzlePcs : List Instr → Nat → List Nat
  | a :: b :: c :: d :: rest, pc =>
    (bif swizzleAt a b c d then [pc] else []) ++ swizzlePcs (b :: c :: d :: rest) (pc + 1)
  | _, _ => []

/-- The shifts `sharedBits` reads are exactly at `swizzleSites`. -/
theorem swizzle_shift_sites :
    (kernel.code.zipIdx.filter (fun p => (swizzleShift p.1.op).isSome)).map (·.2) =
      swizzleSites := by
  decide +kernel

/-- The exclusive-ors `sharedBits` reads are exactly two instructions after `swizzleSites`. -/
theorem swizzle_xor_sites :
    (kernel.code.zipIdx.filter (fun p => (swizzleXor p.1.op).isSome)).map (·.2) =
      swizzleSites.map (· + 2) := by
  decide +kernel

/-- **The forms `sharedBits` reads occur only in the 266 address swizzles**: the whole triple,
followed by the generic access through its result, stands at exactly the sites of the shifts. -/
theorem swizzle_triples : swizzlePcs kernel.code 0 = swizzleSites := by
  decide +kernel

theorem swizzleSites_length : swizzleSites.length = 266 := by
  decide +kernel

end PTX.Kernels.FlashKdaFwd.Assumptions
