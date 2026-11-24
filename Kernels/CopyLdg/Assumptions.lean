-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Spec
public import Core.Assumption.NcReadOnly

@[expose] public section

/-!
# The assumptions of `copy_ldg`

The theorems of `Theorem.lean` assume exactly `ncInput`, and nothing else.
-/

namespace PTX.Kernels.CopyLdg.Assumptions
open PTX

/-- The kernel's one `ld.global.nc.f32`, at pc 12 (§9.7.10.9), reads the launch content of the
input `A`, which the kernel never writes. -/
noncomputable def ncInput : Assumption :=
  Assumption.ncReadOnly "copy-ldg-nc-input" [12]
    "copy_ldg reads its input with one ld.global.nc.f32, for which PTX states only \"Load \
    register variable d from the location specified by the source address operand a in the \
    global state space, and optionally cache in non-coherent read-only cache.\" and to which \
    the memory model does not apply; the kernel writes only B, disjoint from A."

/-- The site of `ncInput` is the kernel's `ld.global.nc`. -/
theorem ncInput_site : kernel.code[12]? = some
    ⟨none, .mem
      { kind := .load, space := some .global, sem := .weak, nc := true, elem := .float .f32,
        addr := { base := .reg 12 64 }, dsts := [some 8] }⟩ := rfl

end PTX.Kernels.CopyLdg.Assumptions
