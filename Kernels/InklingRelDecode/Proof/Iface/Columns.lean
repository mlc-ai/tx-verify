-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

def InS (tm b col : Nat) : Prop := tm + 128 * b ≤ col ∧ col < tm + 128 * b + 128

/-- The probabilities of buffer `b`: the first half of its score buffer. -/
def InP (tm b col : Nat) : Prop := tm + 128 * b ≤ col ∧ col < tm + 128 * b + 64

/-- The output accumulator's columns. -/
def InO (tm col : Nat) : Prop := tm + 256 ≤ col ∧ col < tm + 384

def allocCols : Nat := 512

end PTX.Kernels.InklingRelDecode.Proof.Iface
