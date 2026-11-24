-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Data.Params

@[expose] public section

/-!
# `ld.param` audit of the frozen FlashMLA sparse decode head64 program

`Data/Params.lean` fixes the field offsets of `SparseAttnDecodeParams`, the read table
`param0Reads`, and the full list `paramAccesses_eq` of the program's parameter-space accesses,
and proves that set to be exactly the table (`param0Reads_complete`, `param0Reads_sound`). This
file adds the object-level facts of the audit: the decoded metadata declares the two by-value
objects of 304 and 1024 bytes, pc 0 loads `param_0`'s address into register 2991 and pc 1 loads
`param_1`'s address into register 2990, and the reads happen at the sites listed below. With
`param1_notRead` (no access uses `param_1`'s register), the 44 reads of `paramAccesses_eq` are
reads of `param_0`.

The check is static. A clobbered `param_0` register would not silently read another object:
`ld.param` through a register requires the parameter-space address of a launch parameter object
(THREAD-MOVE, `paramObjectOf`), so the program would be undefined instead of reading elsewhere.
A correctness proof must show register 2991 is unchanged at each read site.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Audit

open PTX

/-- The two by-value parameter objects the PTX declares: `param_0`
(`SparseAttnDecodeParams`, 304 bytes, 8-byte aligned) and `param_1` (the `TmaParams`
tensor-map object, 1024 bytes, 128-byte aligned). -/
theorem paramObjects_eq :
    (Decoded.metadata.paramObjects.map fun o => (o.bytes, o.alignment)) =
      [(param0Bytes, 8), (param1Bytes, 128)] := by
  decide +kernel

/-- pc 0 is `mov.b64 %rd2, param_0`: it loads the address of the `SparseAttnDecodeParams`
object into register 2991, the base of every parameter-space access. -/
theorem param0Address :
    (Decoded.kernel.code[0]?).bind moveOf = some
      { kind := .scalar, ty := .int .b 64, dsts := [some param0AddrReg],
        srcs := [.paramSym param0Name] } := by
  decide +kernel

/-- pc 1 is `mov.b64 %rd1, param_1`: it loads the address of the tensor-map object into
register 2990, which no `ld.param` uses. -/
theorem param1Address :
    (Decoded.kernel.code[1]?).bind moveOf = some
      { kind := .scalar, ty := .int .b 64, dsts := [some param1AddrReg],
        srcs := [.paramSym param1Name] } := by
  decide +kernel

/-- The audit statement: every parameter-space access of the program is a load through
`param_0`'s address register, and its `(offset, width)` pair is a row of `param0Reads`.
`param0Reads_sound` (Data) gives the other direction, so the read set is exactly the table. -/
theorem param0_audit :
    (paramAccesses Decoded.kernel.code).all (fun a =>
        (a.kind == .load && a.base == .reg param0AddrReg 64) &&
          (param0Reads.map fun r => (r.1, r.2.1)).contains (a.off.toNat, a.width)) = true := by
  rw [paramAccesses_eq]
  decide

/-- The program positions of the 44 parameter-space reads, in program order. -/
theorem param0Sites :
    (paramAccesses Decoded.kernel.code).map (fun a => a.pc) =
      [146, 147, 151, 158, 163, 170, 176, 183, 1159, 1167, 1169, 1171, 1858, 1861, 1862,
      1863, 1864, 2170, 2173, 2174, 2175, 2176, 2332, 2335, 2336, 2337, 2338, 2339, 2340,
      2341, 2342, 2343, 2345, 2346, 2349, 2355, 2587, 2590, 2591, 2609, 2612, 2613, 2614,
      2615] := by
  rw [paramAccesses_eq]
  decide

end PTX.Kernels.FlashMlaSparseDecodeH64.Audit
