-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Assumptions.DeadPack
public import Kernels.FlashMlaSparseDecodeH64.Assumptions.PeerScores

@[expose] public section

/-!
# Reading a generic shared pointer as bits

The softmax warpgroup addresses the shared workspace through `cvta.shared.u64`, which produces a
generic pointer to shared memory, and then computes the SW128-swizzled addresses with
`shr.b64`/`and.b64`/`xor.b64` on that pointer's 64-bit representation. Core has no rule for an
integer read of a pointer (`readBits` declines `.ptr`), so the eight `shr.u64` sites that read
the pointer are read as the pointer's shared-window byte address: the 64-bit generic address of
shared memory is that byte address. The swizzle's final xor keeps the pointer's shared-space tag
for the generic stores that use it.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
open PTX

noncomputable section

/-- The eight `shr.u64` sites that read a generic shared pointer as bits (PTX 115–145). -/
def sharedBitsSites : List Nat :=
  [115, 117, 119, 121, 123, 125, 127, 129, 131, 133, 135, 137, 139, 141, 143, 145]

/-- The final xor for each of the eight generic staging addresses. -/
def sharedSwizzleXorSites : List Nat := [117, 121, 125, 129, 133, 137, 141, 145]

/-- An operand whose register holds a generic shared pointer becomes the pointer's byte address;
every other operand is unchanged. -/
def sharedPtrBits (t : TState) (o : Opnd) : Opnd :=
  match o with
  | .reg r =>
    match readReg t r with
    | .ok (.ptr 64 true (.shared _ _) off) => .imm (Int.ofNat off.toNat)
    | _ => o
  | _ => o

/-- Preserve the input pointer's shared-space tag on the swizzled output bits. -/
def keepSwizzleTag (t : TState) (i : IntInstr) (u : TState) : TState :=
  match i.op, i.ty, i.dsts, i.srcs with
  | .xor, .int .b 64, [some dst], [.reg _, .reg src] =>
    match t.regs src, u.regs dst with
    | some (.ptr 64 true (.shared owner cta) _), some (.bits 64 bits) =>
      setReg u dst (.ptr 64 true (.shared owner cta) bits)
    | _, _ => u
  | _, _, _, _ => u

/-- Read generic shared pointer bits and handle the audited packed copies. -/
def sharedBits : Assumption where
  name := "flashmla-h64-shared-pointer-bits"
  statement := "At the eight shr.u64 and eight xor.b64 sites of the SW128 swizzle that read the \
    generic shared pointer produced by cvta.shared.u64 (PTX 115, 117, ..., 145), the pointer's \
    64-bit representation is read as its shared-window byte address (EXT-CVTA). The eight final \
    xors preserve the shared-space tag on the computed address used by the generic output \
    staging stores. At the two audited mov pack sites (208 and 712), zero represents the \
    unwritten high half, which the immediate unpack discards. The packed temporary is dead \
    thereafter, as checked against the frozen program. At the 64 audited integer instructions \
    packing QK scores for exchange with the peer warp, preserve the ideal score payloads in \
    their 32-bit lanes. These widening, shift and merge instructions only move the lanes."
  localRule L g t op :=
    if sharedBitsSites.contains t.pc then
      match op with
      | .int i =>
        let result := execInt L g t { i with srcs := i.srcs.map (sharedPtrBits t) }
        if sharedSwizzleXorSites.contains t.pc then some (result.map (keepSwizzleTag t i))
        else some result
      | _ => none
    else (deadPackRule L g t op).orElse (fun _ => peerPackRule t op)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
