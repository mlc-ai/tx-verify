-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Obj
public import Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.Export.FinalProducer
import Kernels.InklingRelDecode.Proof.Protocol.Warp.Leader
import Kernels.InklingRelDecode.Proof.Epilogue.Export.Time
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Lemmas.Protocol.NotifyBlocker
import Lemmas.Protocol.UnitReachBlocker

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.OFinal
open PTX PTX.Flow PTX.Sched PTX.MbarRing

def Waiting (L : Launch) (m : Mem0) (X : Execution) (c g : Nat) :=
  ∃ sc, NextEv L kernel Assumptions.all m X g ⟨2565,.wait (obj L c) 0 false true sc⟩

private theorem short {Q L m X c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hu : NoUbOutside L X) (hc : c<L.grid)
    (zero : (X.tr (KV.leader L X c 7)).countP (commitsTo (obj L c))=0) :
    threadTime (schedule Q L) X (KV.leader L X c 7)<Lib.Slots.finalWait ∧
      ∀ k pc, X.get (KV.leader L X c 7,k)≠some ⟨pc,.exit⟩ := by
  obtain ⟨hg,cta,warp⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  apply Export.final_short hp hX hf (fun h => Shared.role_bytes hp hX h) hg warp
    (Warp.leader_wins hp hX hc (by decide)) _ hu
  intro i sp he
  obtain ⟨off,rfl,site⟩ := Mma.Export.commit hp hX hf warp he
  rcases site with ⟨bad,_⟩|⟨bad,_⟩|⟨bad,_⟩|⟨_,rfl⟩ <;> try contradiction
  apply List.countP_eq_zero.mp zero _ (List.mem_of_getElem? he)
  simp [commitsTo,obj,cta]

/-- Only one final notification is ever due. Its producer is early or has already issued
it; an exited producer has issued it. This includes the warp's pre-election prefix. -/
theorem lag {Q L m X c} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (hu : NoUbOutside L X) (hc : c<L.grid) :
    ∃ τ, LagN (schedule Q L) X (obj L c) 0 (·=KV.leader L X c 7) (Waiting L m X c)
      τ 1 (commitsTo (obj L c)) := by
  let y := KV.leader L X c 7
  let late := max Lib.Slots.finalWait (threadTime (schedule Q L) X y)+1
  have zero {g} (wait : Waiting L m X c g) : okPolls (obj L c) (X.tr g)=0 := by
    obtain ⟨sc,Y,hY,pref,he⟩ := wait
    have n := wait_first hp hY (followed Y hY) (rows Y hY) he
    rwa [pref] at n
  refine ⟨fun n => if n=0 then Lib.Slots.finalWait else late,?_,?_,?_,?_,?_⟩
  · intro a b le
    dsimp only [late]
    split_ifs <;> omega
  · intro g w
    obtain ⟨sc,hn⟩ := w
    rw [zero ⟨sc,hn⟩,Epilogue.Export.final_wait_time hp (followed X hX) hn]
    exact Nat.le_refl _
  · rintro _ rfl _
    simp only [Nat.add_zero]
    split
    · rename_i no
      exact (short hp hX (followed X hX) hu hc no).1
    · exact Nat.lt_succ_of_le (Nat.le_max_right ..)
  · rintro _ k pc rfl exit
    by_contra! lt
    exact (short hp hX (followed X hX) hu hc (by omega)).2 k pc exit
  · intro g w
    rw [zero w]
    decide

end PTX.Kernels.InklingRelDecode.Proof.Protocol.OFinal
