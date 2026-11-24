-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow

/-- The tensor-only part of the rescale body cannot advance a ballot or
named-barrier count, including when different lanes start at distinct offsets. -/
theorem rescaleBodyCountUnchanged {trace : List Event} {index n : Nat} {test : Event → Bool}
    (disj : ∀ e, isTcColl e = true → test e = false)
    (tensor : (trace.take (index+n)).countP isTcColl = (trace.take index).countP isTcColl+n) :
    (trace.take (index+n)).countP test = (trace.take index).countP test := by
  let body := (trace.drop index).take n
  have split : trace.take (index+n) = trace.take index ++ body := List.take_add ..
  rw [split,List.countP_append] at tensor ⊢
  have total := List.countP_le_length (p := fun e => isTcColl e || test e) (l := body)
  rw [countP_or_disj (fun e _ ⟨h,h'⟩ => Bool.noConfusion ((disj e h).symm.trans h'))] at total
  have bounded : body.length ≤ n := List.length_take_le _ _
  omega

end PTX.Kernels.TmlFa4Fwd.Correction
