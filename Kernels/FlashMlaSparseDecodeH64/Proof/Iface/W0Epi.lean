-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Lemmas.Flow.OutFloatItems
public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # Warpgroup 0's epilogue: the words a block read and the factor they give

The vocabulary of the epilogue value export (`Wg0/Export/EpiIface.lean`): the peer's row-sum word
(the last read at pc 1157, `w0EpiPe`), the accumulator words (`w0EpiO`) and the sink word the
trace left (`w0SkWord`) are in `Iface/W0Value.lean`; here are the numbers they give: the weight
of the sink `w0Sk2`, the factor of the output `w0Fac`, the maximum the epilogue uses `w0EMax`,
the LSE word `w0LseV`, and the two as the carried statistics of a trace give them (`w0EpiF`,
`w0EpiLse`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The maximum the epilogue uses: `-inf` for a row without a kept column, else the carried one. -/
def w0EMax (r : EReal) (m : ℝ) : EReal := if r = ⊥ then ⊥ else (m : EReal)

/-- The weight of the sink: `2 ^ (sk - m)`, zero for no sink. -/
def w0Sk2 (sk : EReal) (m : ℝ) : ℝ := if sk = ⊥ then 0 else (2 : ℝ) ^ (sk.toReal - m)

/-- **The factor of the output** for the sum `s`, the sink word `sk` and the maximum `m`: zero for
a zero sum, else `1 / (s + 2 ^ (sk - m))`. -/
def w0Fac (s : ℝ) (sk : EReal) (m : ℝ) : ℝ := if s = 0 then 0 else 1 / (s + w0Sk2 sk m)

/-- The value the LSE word holds: `+inf` for no kept column or a zero sum. -/
def w0LseV (s : ℝ) (M : EReal) : Value :=
  if s = 0 ∨ M = ⊥ then .bits 32 (BitVec.ofNat 64 2139095040)
  else .float .f32 (M.toReal * lseLog2Factor + Real.log s / Real.log 2 * lseLog2Factor)

/-- **The epilogue's factor**: `w0Fac (w0ESum r l + p) sk m` from the statistics `m`, `l`, the true
maximum `r` the finished blocks of the trace `tr` carry, the peer's word `p` and the sink `sk`. -/
def w0EpiF (sc : ℝ) (tr : List Event) (p : ℝ) (sk : EReal) : ℝ :=
  w0Fac (w0ESum (w0MxCarry sc (w0Fin tr).1) (w0Carry sc (w0Fin tr).1).2 + p) sk
    (w0Carry sc (w0Fin tr).1).1

/-- **The epilogue's LSE word** (`w0LseV`): `+inf` for a zero sum or no kept column, else
`(M + log2 s) ln 2` with the sum `s = l + p` and the maximum `M` the true maximum selects. -/
def w0EpiLse (sc : ℝ) (tr : List Event) (p : ℝ) : Value :=
  w0LseV (w0ESum (w0MxCarry sc (w0Fin tr).1) (w0Carry sc (w0Fin tr).1).2 + p)
    (w0EMax (w0MxCarry sc (w0Fin tr).1) (w0Carry sc (w0Fin tr).1).1)

/-- **A valid trace of lane `g`** (valid rows): the words of its blocks are valid at the end of
every prefix (`W0Valid`, scale `P.scale`). -/
def W0Trace (P : Params) (X : Execution) (g : Nat) : Prop := W0Valid P.scale (X.tr g)

namespace Wg0

/-- The four output chunks' first pcs of their eight staging stores. -/
def ost2Base (c : Fin 4) : Nat := [1331, 1491, 1649, 1806].getD c.val 0

end Wg0

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
