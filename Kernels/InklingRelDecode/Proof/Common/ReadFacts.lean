-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof

/-- The actual dispatch read, at each of the two publications. -/
def RoleBytes (L : Launch) (X : Execution) : Prop :=
  ∀ {g k a bs}, X.get (g,k)=some ⟨2340,.rd a bs⟩ →
    bs=[(b32 (if ((X.tr g).take k).countP (Execution.isBarId 1)=1 then
      16777730 else 50529027)).toBytes[g%L.block/32-4]?]

/-- Each observed worker count load reads the published word at its byte address. -/
def CountBytes (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k p a bs}, X.get (g,k)=some ⟨p,.rd a bs⟩ → (p=2345 ∨ p=2423) →
    ∃ j : Fin 2, (p=2423 → j=1) ∧ a.loc=⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ ∧
      bs=(b32 (if j=0 then Iface.preloadCount Q L (g/L.block)
        else Lib.blocksOf Q L (g/L.block))).toBytes.map some

end PTX.Kernels.InklingRelDecode.Proof
