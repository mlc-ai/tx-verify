-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarReach
import Lemmas.Protocol.GatedFaults

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.MbarRing MbarRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {c : Nat}

/-- **No record of a scalar object faults**: the gate of each arrival or notification is a
reuse path (`goals_all`). -/
theorem fault_free (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hc : c<L.grid) (o : Object) :
    ∀ r ∈ X.objects (o.loc L c), r.fault=none := by
  have all := goals_all hp hX hf rows init words c hc
  have reach (n' : AsyncCopy.Ref × Bool) (hn' : n' ∈ Reach.nodes L X) := all n' hn'
  cases o with
  | prob s =>
    have gate : Unit.Gated L kernel Assumptions.all X ((Object.prob s).loc L c) 1
        (fun _ => c*L.block) 0 := by
      apply Unit.gated_of_paths
      intro a i pc sc he hpos
      exact ⟨KV.leader L X c 7,prob_path hp hX hf rows init words hc he (by omega)
        (fun n' hn' _ => all n' hn')⟩
    exact (probability hX rows init (c := c) s).fault_free hX @gate
  | score s =>
    refine (notification hp hX hf rows init (c := c) (.inl ⟨s,rfl⟩)).fault_free hX
      (Notify.gated_of_paths (K := kernel) (A := Assumptions.all)
        fun {i pc sp rank} he hm ht hrec hpos => ?_)
    obtain ⟨r,hr,hid⟩ := hrec
    obtain ⟨_,_,_,_,mem⟩ := Reach.notify_rec hX hr hid
    exact ⟨c*L.block,score_path hp hX hf rows init words hc (ToArrival.zero hX) he hm mem (by omega)
      (fun n' hn' _ => all n' hn')⟩
  | done =>
    refine (notification hp hX hf rows init (c := c) (.inr rfl)).fault_free hX
      (Notify.gated_of_paths (K := kernel) (A := Assumptions.all)
        fun {i pc sp rank} he hm ht hrec hpos => ?_)
    obtain ⟨r,hr,hid⟩ := hrec
    obtain ⟨_,_,_,_,mem⟩ := Reach.notify_rec hX hr hid
    exact ⟨c*L.block,done_path hp hX hf rows init words hc (ToArrival.zero hX) he hm mem (by omega)
      (fun n' hn' _ => all n' hn')⟩

/-- The recurrent scalar rows of the initialization table are the scalar objects. -/
theorem slot_object (j : Fin 12) (low : 6≤j.val) (high : j.val<11) :
    ∃ o : Object, MbarRow.initOffset j=o.offset := by
  obtain ⟨j,hj⟩ := j
  interval_cases j
  · exact ⟨.score 0,rfl⟩
  · exact ⟨.prob 0,rfl⟩
  · exact ⟨.score 1,rfl⟩
  · exact ⟨.prob 1,rfl⟩
  · exact ⟨.done,rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
