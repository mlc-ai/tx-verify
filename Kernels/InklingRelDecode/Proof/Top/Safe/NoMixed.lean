-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.NoRace
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- No mixed-size conflict: pairs of different footprints pass the guard of
`Safe.ordered`. -/
theorem Safe.noMixed (hp : Pre Q L m)
    {X : Execution} (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (words : RoleBytes L X)
    (hu : ¬ HasUb X) (gr : Iface.GlobalReads Q X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ¬ Mixed L X := by
  rintro ⟨e,f,a,b,l,con,diff,ca,cb,left,right⟩
  have ne : ¬ SameValueWrites X e f a b := fun ⟨_,_,eq,_⟩ => diff eq
  exact (Safe.ordered hp hX hf rows init words (.of_noUb hu) gr nub con ca cb ne
    fun ⟨eq,_⟩ => diff eq).elim left right

end PTX.Kernels.InklingRelDecode.Proof.Top
