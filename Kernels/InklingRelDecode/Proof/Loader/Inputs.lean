-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section

/-- The integer and address operands passed by dispatch. The remaining live registers,
including the tensor-map pointer, are preserved verbatim. -/
def inputs (Q : Params) (L : Launch) (g : Nat) (rest : Nat → Value) (r : Nat) : Value :=
  let table : List (Nat × Value) :=
    [(462, b32 (g % L.block)), (466, .bits 32 (shl (BitVec.ofNat 64 (Q.splits % 2 ^ 32)) 7)),
     (528, b32 (Q.strideBt % 2 ^ 32)), (529, b32 (Q.pageRows % 2 ^ 32)),
     (530, b32 (Q.headRows % 2 ^ 32)), (531, b32 (Q.headCols % 2 ^ 32)),
     (532, b32 (Q.splits % 2 ^ 32)), (2020, b64 Q.btBase)]
  (table.lookup r).getD (rest r)

/-- Temporaries used only before the first poll. -/
def entryValue (Q : Params) (L : Launch) (g : Nat) (w : Value) (rest : Nat → Value)
    (i n a b : Value) (r : Nat) : Value :=
  let x := r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .x))
  let short : List (Nat × Value) :=
    [(468, .bits 32 x), (469, .bits 32 (andi (BitVec.ofNat 64 (g % L.block)) 31)),
     (577, .bits 32 (mad32 (r32 (BitVec.ofNat 64 (Q.splits % 2 ^ 32))) (bits i) x))]
  (short.lookup r).getD (loopValue L g w (inputs Q L g rest) ⟨.poll,i,n,a,b⟩ r)

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
