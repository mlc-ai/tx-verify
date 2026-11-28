-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Mbar

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow MbarRow PTX.MbarRow

inductive Object where
  | score (s : Fin 2) | prob (s : Fin 2) | done
  deriving DecidableEq

def Object.offset : Object → Nat
  | .score s => Iface.sReady s | .prob s => Iface.pReady s | .done => Iface.oDone

def Object.loc (o : Object) (L : Launch) (c : Nat) : Loc :=
  ⟨.shared,c,L.sharedBase+o.offset⟩

private theorem same {L c g o z} (eq : Object.loc o L c=MbarRow.loc L g z.offset) :
    o=z ∧ g/L.block=c := by
  obtain ⟨_,cta,off⟩ := Loc.mk.inj eq
  have h := Nat.add_left_cancel off
  refine ⟨?_,cta.symm⟩
  cases o <;> cases z <;> simp only [Object.offset,Iface.sReady,Iface.pReady,Iface.oDone] at h
  all_goals first | rfl | (congr 1; apply Fin.ext; omega) | omega

private theorem outside {L c g o n} (out : n<213280 ∨ 213312<n)
    (eq : Object.loc o L c=MbarRow.loc L g n) : False := by
  have off := Nat.add_left_cancel (Loc.mk.inj eq).2.2
  cases o <;> simp only [Object.offset,Iface.sReady,Iface.pReady,Iface.oDone] at off <;> omega

/-- Each scalar object has one producer instruction and one polling instruction.
The score and probability slots alternate on successive blocks. -/
inductive Use (L : Launch) (X : Execution) (g k : Nat) (e : Event) (c : Nat) :
    Object → Prop where
  | init {o} (kind : e.kind=.mbInit (o.loc L c) 1) : Use L X g k e c o
  | scoreWait (pc : e.pc=1257) (dataLane : g%L.block/32<4)
      (kind : Wait e ((Object.score (slot2 (roundAt X g k 1257))).loc L c)
        (roundAt X g k 1257/2%2)) : Use L X g k e c (.score (slot2 (roundAt X g k 1257)))
  | scoreCommit (pc : e.pc=2499) (warp : g%L.block/32=7)
      (kind : Commit e ((Object.score (slot2 (roundAt X g k 2462-1))).loc L c)) :
      Use L X g k e c (.score (slot2 (roundAt X g k 2462-1)))
  | probWait (pc : e.pc=2510) (warp : g%L.block/32=7)
      (kind : Wait e ((Object.prob (slot2 (roundAt X g k 2510))).loc L c)
        (roundAt X g k 2510/2%2)) : Use L X g k e c (.prob (slot2 (roundAt X g k 2510)))
  | probArrive (pc : e.pc=1013) (lead : g%L.block=0)
      (kind : Arrive e ((Object.prob (slot2 (((X.tr g).take k).countP (·.pc==1013)))).loc L c) 0) :
      Use L X g k e c (.prob (slot2 (((X.tr g).take k).countP (·.pc==1013))))
  | doneWait (pc : e.pc=2239) (dataLane : g%L.block/32<4)
      (kind : Wait e (Object.done.loc L c) (roundAt X g k 2239%2)) : Use L X g k e c .done
  | doneCommit (pc : e.pc=2548) (warp : g%L.block/32=7)
      (kind : Commit e (Object.done.loc L c)) : Use L X g k e c .done

theorem uses {Q L X g k e c o} (rows : MbarRows Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some e) (hm : Frame.MbarOf e (Object.loc o L c)) :
    g/L.block=c ∧ Use L X g k e c o := by
  cases mbar_use rows hg he hm with
  | startup _ h | dispatch _ h => cases h
  | prologue _ h =>
    cases h with
    | init _ _ addr kd _ _ _ _ _ => exact ⟨(Loc.mk.inj addr).2.1.symm,.init kd⟩
    | preloadArrive _ _ addr _ | preloadCopy _ _ addr _ =>
      exact (outside (.inl (by unfold Iface.kvReady; omega)) addr).elim
  | epilogue _ h =>
    cases h with | finalWait _ addr _ => exact (outside (.inr (by decide)) addr).elim
  | loader _ h =>
    cases h with
    | emptyWait _ addr _ => exact (outside (.inl (by unfold Iface.kvEmpty; omega)) addr).elim
    | readyArrive _ _ addr _ | readyCopy _ _ addr _ =>
      exact (outside (.inl (by unfold Iface.kvReady; omega)) addr).elim
  | softmax hw h =>
    cases h with
    | pArrive pc lead addr kd =>
      obtain ⟨rfl,cta⟩ := same (z := .prob _) addr
      exact ⟨cta,.probArrive pc lead kd⟩
    | sWait pc addr kd =>
      obtain ⟨rfl,cta⟩ := same (z := .score _) addr
      exact ⟨cta,.scoreWait pc hw.1 kd⟩
    | oWait pc addr kd =>
      obtain ⟨rfl,cta⟩ := same (z := .done) addr
      exact ⟨cta,.doneWait pc hw.1 kd⟩
  | mma hw h =>
    cases h with
    | readyWait _ addr _ => exact (outside (.inl (by unfold Iface.kvReady; omega)) addr).elim
    | emptyCommit _ addr _ => exact (outside (.inl (by unfold Iface.kvEmpty; omega)) addr).elim
    | finalCommit _ addr _ => exact (outside (.inr (by decide)) addr).elim
    | pWait pc addr kd =>
      obtain ⟨rfl,cta⟩ := same (z := .prob _) addr
      exact ⟨cta,.probWait pc hw.1 kd⟩
    | sCommit pc addr kd =>
      obtain ⟨rfl,cta⟩ := same (z := .score _) addr
      exact ⟨cta,.scoreCommit pc hw.1 kd⟩
    | doneCommit pc addr kd =>
      obtain ⟨rfl,cta⟩ := same (z := .done) addr
      exact ⟨cta,.doneCommit pc hw.1 kd⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
