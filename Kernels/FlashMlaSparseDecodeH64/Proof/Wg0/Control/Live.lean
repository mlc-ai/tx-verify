-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch

@[expose] public section

/-! # The control registers of warpgroup 0

The control machine states facts for its control registers only: `ctlLive pc` is the generated
liveness (`Flow.live`) without the data registers. The data registers (`dataRanges`, ids) are the
closure, under the role's local instructions, of the destinations of its score loads from Tensor
Memory, its reads from shared memory and its sink load, and of the floating-point constants it
moves into registers, together with the scale word and the two registers no instruction
writes. The eight generic staging pointers and their computation (pcs 104–145: `cvta.shared` and
the SW128 swizzle on the pointer) are control registers: the staging stores' addresses are
stated.
Read from the PTX: no branch reads a data register but the row-sum test at pc 1191 (its two sides
meet at pc 1197 and write only data registers), and no event other than a store's payload or the
vote's predicate reads one. The data plane (their values) is the `Data` machine's. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX

/-- The data registers of warpgroup 0 (ranges of register ids). -/
def dataRanges : List (Nat × Nat) :=
  [(77, 109), (119, 120), (138, 138), (155, 185), (467, 467), (479, 482), (932, 932), (950, 950),
   (1002, 1111), (1114, 1262), (1264, 1391), (1393, 1520), (1522, 1649), (1651, 1716),
   (1727, 1728), (1730, 1733), (1741, 1808), (1810, 1905), (1916, 1979), (1981, 2076),
   (2086, 2149), (2151, 2246), (2255, 2318), (2320, 2415), (2880, 2880), (2885, 2951),
   (2955, 2956), (3145, 3243), (3245, 3565), (3575, 3831),
   (4031, 4038)]

/-- The sink word `%r2422` (id 2880): `-inf` from the start-up (pc 101) until the sink's load at
pc 156 can overwrite it (pc 157). Up to there the control machine states it, so the data machine
starts its chain with it; later it is a data register (the loop carries it). -/
def sinkReg : Nat := 2880
def sinkPc : Nat := 156

/-- A control register: not a data register. -/
def ctl (r : Nat) : Bool := !dataRanges.any fun (a, b) => Nat.ble a r && Nat.ble r b

/-- The control registers live at program counter `pc`. -/
noncomputable def ctlLive (pc : Nat) : List Nat :=
  (PTX.Kernels.FlashMlaSparseDecodeH64.Flow.live pc).filter fun r =>
    ctl r || (r == sinkReg && Nat.blt pc sinkPc)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
