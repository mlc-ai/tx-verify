-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarHistory
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarCommits
import Kernels.InklingRelDecode.Proof.Lib.IssueCount

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.MbarRing MbarRow

/-- An arrival on a probability slot is the lane's publication, on the slot of its ordinal. -/
theorem arrival_event {Q L X c s g j e} (rows : MbarRows Q L X) (hg : g<L.threads)
    (get : X.get (g,j)=some e) (hit : arrivesOn ((Object.prob s).loc L c) e) :
    ∃ tx n rel sc, e=⟨1013,.arrive ((Object.prob s).loc L c) tx n rel sc⟩ ∧
      s.val=((X.tr g).take j).countP (fun a => a.pc==1013)%2 := by
  obtain ⟨p,k⟩ := e
  cases k <;> simp [arrivesOn,sourceArrive] at hit
  rename_i l tx n rel sc
  subst l
  obtain ⟨_,use⟩ := uses rows hg get rfl
  cases use with
  | init kd => cases kd
  | probWait _ _ kd => obtain ⟨_,kd⟩ := kd; cases kd
  | probArrive pc _ _ => exact ⟨_,_,_,_,congrArg (Event.mk · _) pc,rfl⟩

/-- An arrival on a probability slot is on the slot of its ordinal among the lane's
publications, and the earlier arrivals on the slot are at most half of that ordinal. -/
theorem arrival_ordinal {Q L X c s g k pc tx n rel sc} (rows : MbarRows Q L X)
    (hg : g<L.threads)
    (get : X.get (g,k)=some ⟨pc,.arrive ((Object.prob s).loc L c) tx n rel sc⟩) :
    pc=1013 ∧ s.val=((X.tr g).take k).countP (fun a => a.pc==1013)%2 ∧
      arrivals ((Object.prob s).loc L c) ((X.tr g).take k)≤
        ((X.tr g).take k).countP (fun a => a.pc==1013)/2 := by
  obtain ⟨_,_,_,_,tag,slot⟩ := arrival_event (c := c) (s := s) rows hg get
    (by simp [arrivesOn,sourceArrive])
  refine ⟨congrArg Event.pc tag,slot,?_⟩
  set p : Event → Bool := fun e => e.pc==1013 with hpd
  apply Lib.count_le_tags (fun j => (((X.tr g).take k).take j).countP p/2)
  · intro j e atJ use
    obtain ⟨ji,atJ'⟩ := take_event atJ
    obtain ⟨_,_,_,_,tag,pos⟩ := arrival_event rows hg atJ' use
    replace pos : s.val=((X.tr g).take j).countP p%2 := pos
    have step := countP_take_succ (p := p) atJ' (by simp [tag,hpd])
    have le := countP_take_mono p (X.tr g) (show j+1 ≤ k from ji)
    rw [List.take_take,Nat.min_eq_left ji.le]
    change _≤((X.tr g).take k).countP p at le
    omega
  · intro j j' e f he ue hf uf eq
    obtain ⟨ji,he'⟩ := take_event he
    obtain ⟨ji',hf'⟩ := take_event hf
    obtain ⟨_,_,_,_,tag,pos⟩ := arrival_event rows hg he' ue
    obtain ⟨_,_,_,_,tag',pos'⟩ := arrival_event rows hg hf' uf
    replace pos : s.val=((X.tr g).take j).countP p%2 := pos
    replace pos' : s.val=((X.tr g).take j').countP p%2 := pos'
    rw [List.take_take,List.take_take,Nat.min_eq_left ji.le,Nat.min_eq_left ji'.le] at eq
    exact nthEv_unique (p := p) he' (by simp [tag,hpd]) hf' (by simp [tag',p]) (by omega)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
