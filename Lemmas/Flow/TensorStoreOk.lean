-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TmplOkSync
public import Lemmas.Flow.TensorStoreOrigin

@[expose] public section

/-! # A tensor store that is not undefined behaviour

A proof tool, the store counterpart of `cpTensor_off_ok`: a tile-mode tensor store (no
reduction) whose cache policy, map, source and coordinates evaluate, with a 128-aligned source
and nonnegative 32-bit coordinates, is not undefined behaviour (`cpTensorStore_ok`). -/

namespace PTX.Flow
open PTX

/-- **A tile tensor store whose operands evaluate is not undefined behaviour.** -/
theorem cpTensorStore_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int} {pol : Option Opnd} {a outer : Nat}
    {desc : TensorDescriptor.Descriptor outer} {sl : Loc} {vs : List (BitVec 64)}
    (hp : cachePolicyRead L g t pol = .ok ())
    (hm : tensorMap L g t map cs .tile = .ok (a, ⟨outer, desc⟩))
    (hs : sharedEffAddr L g t false src off = .ok sl) (h128 : sl.addr % 128 = 0)
    (hvs : cs.mapM (readBits L g t 32) = .ok vs)
    (hor : ∀ i : Nat, 0 ≤ (BitVec.ofNat 32 (vs.getD i 0).toNat).toInt)
    (hbox : TensorDescriptor.BoxAligned desc
      (fun axis : Fin (outer + 1) => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt))
    (f : Fault) :
    eventTmpl A L g t (.cpTensorStore map cs src off pol .tile none) ≠ .ub f := by
  have hor' : ∀ axis : Fin (outer + 1),
      0 ≤ (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt := fun axis => hor axis.val
  simp only [eventTmpl, tensorStoreTmpl, tensorStoreSpec, hp, hm, hs, hvs, bind, Except.bind,
    pure, Except.pure, Option.all, h128, hor', TensorMode.transfer, requireBoxAligned, hbox]
  simp [ofExec]

end PTX.Flow
