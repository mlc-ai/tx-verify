-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Proof.Lib.RawArith

@[expose] public section

/-! # The static form of the `tcgen05` collectives

Lane `g` made, as its `n`-th shuffle, the broadcast at `pc` that received `w` (`ShflAt`). Of the
collective `tcgen05` events, what the lanes of a warp must agree on (`tcStatic`) is a function of
the position, the round `i` of the Softmax loop and the word `w` the warp's broadcast delivered
(`opStatic`): the Tensor Memory address of a load or store is the object's base plus the round's
buffer offset plus the word's low two bits scaled by `2^21`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

noncomputable section

/-- Lane `g` made, as its `n`-th shuffle, the index shuffle of lane zero at `pc` that received
`w`. -/
def ShflAt (X : Execution) (g pc n : Nat) (w : Value) : Prop :=
  ∃ j a ok, X.get (g,j) = some ⟨pc,.shfl .idx a 0 31 w ok⟩ ∧
    ((X.tr g).take j).countP Execution.isShfl = n

/-- The positions whose address depends on a broadcast. -/
def addrPcs : List Nat := [1265,2260,2328,1009,2607]

/-- The broadcast that decides the address of the collective at `pc`. -/
def bcastPc (pc : Nat) : Nat := if pc = 2607 then 2603 else 1261

/-- The offset the broadcast word adds to a Tensor Memory address. -/
def bcastOffset (w : Value) : Nat := (word w).toNat % 4 * 2^21

/-- The collective `tcgen05` event of a CTA's thread at `pc`, in round `i`, with the broadcast
word `w`, as the lanes of a warp must agree on it. -/
def opStatic (L : Launch) (cta pc i : Nat) (w : Value) : TcKind :=
  if pc = 1265 then .ld (i%2*128 + bcastOffset w) [] (.s16x32bx2 64)
  else if pc = 2260 then .ld (256 + bcastOffset w) [] (.s16x32bx2 64)
  else if pc = 2328 then .st (256 + bcastOffset w) [] (.s16x32bx2 64)
  else if pc = 1009 then .st (i%2*128 + bcastOffset w) [] (.s16x32bx2 32)
  else if pc = 2607 then .ld (256 + bcastOffset w) [] (.s16x32bx2 64)
  else if pc = 1298 ∨ pc = 2261 ∨ pc = 2608 then .waitLd
  else if pc = 2329 ∨ pc = 1010 then .waitSt
  else if pc = 11 then .resource .one (some ⟨.shared, cta, L.sharedBase⟩) (.alloc 512)
  else if pc = 15 then .resource .one none .relinquish
  else .resource .one none (.dealloc 0 512)

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
