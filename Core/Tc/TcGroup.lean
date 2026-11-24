-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Instr

@[expose] public section

namespace PTX

/-! ## PROG-TC-CTA-GROUP — one tcgen05 CTA-group qualifier per kernel
Statement: A kernel is correct only if its code does not contain both instructions qualified
  `.cta_group::1` and instructions qualified `.cta_group::2`, counting predicated and unreachable
  instructions. Loads, stores, waits and fences name no group.

Defs: Op.tcGroup, Kernel.tcGroupUniform, Kernel.TcGroupUniform

Source:
- §9.7.18.10.10.1 (all tcgen05 instructions within a kernel specify the same cta_group)

Direction: equal

Applies: All represented source instructions with an explicit tcgen05 .cta_group qualifier

Premises: Inspect the whole source kernel, including predicated and unreachable instructions.
  Unqualified ld/wait/fence instructions contribute no group.

Effect: Static component of Correct.safe.
-/

/-- The CTA-group size that a tcgen05 instruction names; loads, stores, waits and fences name
none. -/
def Op.tcGroup : Op → Option Nat
  | .tcAlloc group .. | .tcDealloc group .. | .tcRelinquish group
  | .tcCommit group .. => some group.size
  | .tcMma m => some m.group.size
  | .tcCp group .. | .tcShift group .. => some group.size
  | _ => none

/-- No qualified operations, or operations of just one group, are accepted. -/
def Kernel.tcGroupUniform (K : Kernel) : Bool :=
  !(K.code.any fun ins => ins.op.tcGroup == some 1) ||
    !(K.code.any fun ins => ins.op.tcGroup == some 2)

/-- The code of the kernel does not contain both `.cta_group::1` and `.cta_group::2`
instructions. -/
def Kernel.TcGroupUniform (K : Kernel) : Prop := K.tcGroupUniform = true

end PTX
