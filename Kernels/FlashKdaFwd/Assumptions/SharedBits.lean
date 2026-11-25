-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local

@[expose] public section

/-!
# Reading a generic shared pointer as bits

The kernel addresses its FP32 state buffer through `cvta.shared.u64`, which produces a generic
pointer to shared memory, and computes the 32-byte-swizzled address of an element with
`shr.u64 x, p, 3`, `and.b64 y, x, 16` and `xor.b64 q, y, p` on that pointer's 64-bit
representation (CuTe's `Swizzle<1,4,3>`; 266 such triples, one per generic load or store of the
buffer). Core has no rule for an integer read of a pointer (`readBits` declines `.ptr`). The
rule below reads the pointer of the two instructions that take it as its shared-window byte
address, as FlashMLA's `sharedBits` does for the 128-byte swizzle: the 64-bit generic address
of a shared byte and its shared-window address have the same low eight bits (the generic base of
the shared window is 256-byte aligned), and the swizzle reads and changes only bits 4 and 7.
The final `xor` keeps the pointer's shared-space tag for the generic access that uses it.

The rule is selected by instruction form and operand shape, not by position: a `shr.u64` by the
constant 3 whose source register holds a generic shared pointer, and an `xor.b64` of a register
holding the bits 0 or 16 with a register holding a generic shared pointer.
-/

namespace PTX.Kernels.FlashKdaFwd.Assumptions
open PTX

noncomputable section

/-- The destination and source of `shr.u64 d, r, 3`. -/
def swizzleShift : Op → Option (Nat × Nat)
  | .int ⟨.shr, .int .u 64, false, [some d], [.reg r, .imm 3]⟩ => some (d, r)
  | _ => none

/-- The destination, mask register and pointer register of `xor.b64 d, m, r`. -/
def swizzleXor : Op → Option (Nat × Nat × Nat)
  | .int ⟨.xor, .int .b 64, false, [some d], [.reg m, .reg r]⟩ => some (d, m, r)
  | _ => none

/-- The swizzle of a generic shared pointer on its shared-window address. -/
def sharedBitsRule (t : TState) (op : Op) : Option (Exec TState) :=
  match swizzleShift op with
  | some (d, r) =>
    match t.regs r with
    | some (.ptr 64 true (.shared _ _) off) =>
      some (pure (next (setReg t d (.bits 64 (off >>> 3)))))
    | _ => none
  | none =>
    match swizzleXor op with
    | some (d, m, r) =>
      match t.regs m, t.regs r with
      | some (.bits 64 bits), some (.ptr 64 true (.shared owner cta) off) =>
        if bits = 0 ∨ bits = 16 then
          some (pure (next (setReg t d (.ptr 64 true (.shared owner cta) (off ^^^ bits)))))
        else none
      | _, _ => none
    | none => none

/-- Read generic shared pointer bits in the 32-byte swizzle of the FP32 state buffer. -/
def sharedBits : Assumption where
  name := "flash-kda-shared-pointer-bits"
  statement := "In the address computation shr.u64 x, p, 3; and.b64 y, x, 16; xor.b64 q, y, p \
    of a generic shared pointer p (the result of cvta.shared.u64 plus an offset), the shift \
    reads the pointer's 64-bit representation as its shared-window byte address (EXT-CVTA), and \
    the xor with the mask 0 or 16 gives the pointer to the byte whose shared-window address has \
    bit 4 flipped accordingly, keeping the shared-space tag for the generic load or store that \
    uses it. The low eight bits of a generic shared address are those of its shared-window \
    address."
  localRule _ _ t op := sharedBitsRule t op

end
end PTX.Kernels.FlashKdaFwd.Assumptions
