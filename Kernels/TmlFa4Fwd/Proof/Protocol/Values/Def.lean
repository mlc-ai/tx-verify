-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Facts
public import Kernels.TmlFa4Fwd.Spec
public import Assumption.IdealReal
public import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # What the values of the MMAs' results need

A completed MMA's ideal arithmetic gives a number at each of its cells when the elements of its
operands are numbers and its old values are (`CompletedValues`). The facts of other layers that this
needs:

* `SmemElements`: the elements in shared memory are BF16 numbers (the Q, K and V copies).
* `SoftStores`: a softmax lane stores pairs of BF16 numbers, once the Tensor Memory loads of its CTA
  that precede the store returned single-precision numbers (the softmax data machine).
* `CorrStores`: a correction lane stores single-precision numbers, once those loads did (the
  correction's data machine and the statistics hand-off). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm

noncomputable section

/-- Each value is a single-precision number. -/
def F32s (vals : List Value) : Prop := ∀ v ∈ vals, ∃ x : ℝ, v = .float .f32 x

/-- The bytes of a word are those of two BF16 numbers. -/
def Bf16Pair (v : Value) (x y : ℝ) : Prop :=
  v.bytes = 4 ∧ ∀ z < 2, v.byteAt z = (Value.float .bf16 x).byteAt z ∧
    v.byteAt (2 + z) = (Value.float .bf16 y).byteAt z

/-- **The Tensor Memory loads of a lane's CTA that precede an event** in the `tcgen05` orders
returned single-precision numbers. -/
def LoadsBefore (L : Launch) (X : Execution) (e : EvId) : Prop :=
  ∀ (f : EvId) (a : Nat) (vals : List Value), X.TLd f a vals .s32x32b →
    f.1 / L.block = e.1 / L.block → Relation.TransGen (TcStep L X) f e → F32s vals

/-- **The shared operand elements are BF16 numbers.** -/
def SmemElements (X : Execution) : Prop :=
  ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {row k : Nat}, X.MmaIssue i d s acc mask →
    X.async.mmaDone i = true → X.async.mmaOperands i = some ops → row < 128 → k < 16 →
      (∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok y) ∧
      (s.aTmem = none →
        ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x)

/-- **A softmax lane stores pairs of BF16 numbers**, once the loads before did. -/
def SoftStores (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a : Nat} {vals : List Value}, h < L.threads → Prologue.warpIndex L h < 8 →
    X.TSt (h, i) a vals .s32x32b → LoadsBefore L X (h, i) → ∀ v ∈ vals, ∃ x y, Bf16Pair v x y

/-- **A correction lane stores single-precision numbers**, once the loads before did. -/
def CorrStores (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a : Nat} {vals : List Value}, h < L.threads → 8 ≤ Prologue.warpIndex L h →
    Prologue.warpIndex L h < 12 → X.TSt (h, i) a vals .s32x32b → LoadsBefore L X (h, i) → F32s vals

/-- **The facts of the other layers for the values of the MMAs.** -/
structure ElementFacts (L : Launch) (X : Execution) : Prop where
  smem : SmemElements X
  soft : SoftStores L X
  corr : CorrStores L X

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
