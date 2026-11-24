-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncOrigins
public import Lemmas.MBarrier.MBarrierHistory

@[expose] public section

/-! One operation has one position in its object's history: the operation identities of a
checked history are distinct (`MBarrier.CheckedLog`, through `AsyncCopy.ObjectsOk`). -/
namespace PTX
open AsyncCopy
noncomputable section

/-- A single operation occupies only one position of its object's history. -/
theorem Consistent.object_index_eq {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    {m : Loc} {i j : Nat} {ri rj : MBarrier.Record Ref}
    (hi : (X.objects m)[i]? = some ri) (hj : (X.objects m)[j]? = some rj)
    (he : ri.id = rj.id) : i = j := by
  have hnd := (hX.tma.2.2.1 m).1.1
  have hi' : ((X.objects m).map MBarrier.Record.id)[i]? = some rj.id := by simp [hi, he]
  have hj' : ((X.objects m).map MBarrier.Record.id)[j]? = some rj.id := by simp [hj]
  obtain ⟨_, hi2⟩ := List.getElem?_eq_some_iff.mp hi'
  obtain ⟨_, hj2⟩ := List.getElem?_eq_some_iff.mp hj'
  exact (List.Nodup.getElem_inj_iff hnd).mp (hi2.trans hj2.symm)

end
end PTX
