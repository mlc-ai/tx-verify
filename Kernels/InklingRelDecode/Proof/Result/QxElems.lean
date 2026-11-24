-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QxQTile

@[expose] public section

/-!
# What is left of `Qx.ElemPrem`

`ElemRest` lists the fields of `Qx.ElemPrem` that have no proof; `elemPrem_of` builds
`Qx.ElemPrem` from it, with the A elements of the QK MMAs from `qk_a_real` (every row, every
consistent execution).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qx
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts threadCode)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The fields of `ElemPrem` without a proof**: the A elements of the PV MMAs (`pvA`), the B
elements of every MMA (`b`) and the base accumulators of the PV MMAs (`oBase`), as in
`ElemPrem`. -/
structure ElemRest (Q : Params) (L : Launch) (X : Execution) : Prop where
  pvA : ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
    {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands} {r kk : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv j →
    X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops → r < 64 → kk < 16 →
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r kk = .ok x
  b : ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
    {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands} {n kk : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    St Q L X g k = some (some (.w (.mma d P))) →
    (d.site = .qk j ∨ d.site = .pv j) →
    X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops → n < 128 → kk < 16 →
    ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b n kk = .ok y
  oBase : ∀ {g k : Nat} {d : Mma.D} {P : Loader.Pro}, g < L.threads →
    (∃ e, X.get (g, k) = some e) →
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv 0 → 2 ≤ d.i →
    X.async.mmaDone (g, k) = true → ResultBelow L X g k → ∀ {r n : Nat}, r < 64 → n < 128 →
    ∃ src, ReadSource L X .acc src (g, k) (oCell (g / L.block) d.tm r n) ∧
      ((∃ (k' : Nat) (d' : Mma.D) (P' : Loader.Pro), k' < k ∧ src = (g, k') ∧
          St Q L X g k' = some (some (.w (.mma d' P'))) ∧
          (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
          d'.site = .pv 7 ∧ d'.i + 1 = d.i ∧ d'.tm = d.tm) ∨
        ∃ old x, StoreValue L X src (oCell (g / L.block) d.tm r n) old ∧
          valFloat .f32 old = .ok x)

/-- **`ElemPrem`** from `ElemRest` and the A elements of the QK MMAs (`qk_a_real`). -/
theorem elemPrem_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : Interface.RoleReads L X) (hE : Interface.Bar1Exits L X) (R : ElemRest Q L X) :
    ElemPrem Q L X where
  qkA := fun hg he hσ hs _ hops hr hk => qk_a_real hpre hX hf hT hR hE hg he hσ hs hops hr hk
  pvA := R.pvA
  b := R.b
  oBase := R.oBase

end
end PTX.Kernels.InklingRelDecode.Proof.Qx
