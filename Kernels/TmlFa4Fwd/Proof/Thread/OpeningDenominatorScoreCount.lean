-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorNotice
import all Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorNotice
import all Kernels.TmlFa4Fwd.Proof.Thread.FirstProbabilityScoreCount
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxStages
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow Prologue Thread.Scores

/-- The first denominator starts the recurring score cursor after precisely
one successful score poll of its physical stage object. -/
theorem OpeningDenominatorCursor.scoreCountOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {g batch blocks cap past : Nat} (hg : g < l.threads)
    (stage : Fin 2) (hRole : warpIndex l g/4 = stage.val) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ g/l.block) (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (c : OpeningDenominatorCursor p l X g blocks cap past) :
    okPolls (scoreReadyObject l (g/l.block) stage) ((X.tr g).take c.cursor.pos) = 1 := by
  let obj := scoreReadyObject l (g/l.block) stage
  let k := c.cursor.pos
  let e := Event.mk 3425 (.wait obj 0 true true .cta)
  obtain ⟨j,first⟩ :=
    Progress.openingSoftmaxAcquireOfAllStages hp hMax frame hg stage hRole hb lo hi
  have he : X.get (g,j) = some e := first.decoded
  have ht := c.cursor.checkpoint.1
  have hj : j < k := by
    by_contra! h
    have mem : e ∈ (X.tr g).drop k := by
      apply List.mem_of_getElem? (i := j-k)
      rwa [List.getElem?_drop,Nat.add_sub_of_le h]
    obtain ⟨_,walk⟩ := Mma.walkFromRun (c.cursor.remaining.after_local_nonempty
      c.cursor.localSteps (fun h => by change (X.tr g).drop k = [] at h; simp [h] at mem))
    have fail := Thread.eventTailEventsOfSegmentFloor openingDenominatorFloor
      openingDenominatorSegmentFloor walk ht.ge e mem
    exact (by decide : ¬ 5006 ≤ 3425) fail
  have low : 0 < okPolls obj ((X.tr g).take k) := by
    apply List.countP_pos_iff.mpr
    exact ⟨e,List.mem_of_getElem? ((List.getElem?_take_of_lt hj).trans he),
      by simp [okPoll,sourceWaitSuccess,e]⟩
  have hw : warpIndex l g < 8 := by have := stage.isLt; omega
  rw [← scoreCount hp hMax.1 stage hw rfl hRole]
  have path : TraceReach kernel Assumptions.all l g {} ((X.tr g).take k) c.cursor.ready := by
    simpa only [List.append_nil] using c.cursor.recorded.returning_reach.append
      (TraceReach.of_local c.cursor.localSteps)
  have opening {idx : Nat} {ev : Event} (hIdx : idx < k) (hEv : X.get (g,idx) = some ev)
      (marked : phaseAcquired true ev = true) :
      ∃ loc phase acq scope, ev = ⟨3425,.wait loc phase true acq scope⟩ := by
    have bound := beforeOpeningDenominatorEvent path ht
      (List.mem_of_getElem? ((List.getElem?_take_of_lt hIdx).trans hEv))
    rw [scoreReadyMarkKind] at marked
    obtain ⟨site,kind⟩ := ev
    change site < 5007 at bound
    cases kind <;> try cases marked
    rename_i loc phase ok acq scope
    cases ok <;> try cases marked
    change ([3425,5109,6676] : List Nat).contains site = true at marked
    simp only [List.contains_iff_mem,List.mem_cons,List.not_mem_nil,or_false] at marked
    have eq : site = 3425 := by omega
    exact ⟨_,_,_,_,by subst site; rfl⟩
  have eqCount := scoreCount (j := k) hp hMax.1 stage hw rfl hRole
  change ((X.tr g).take k).countP (phaseAcquired true) = 1
  rw [← eqCount] at low
  refine Nat.le_antisymm ?_ low
  by_contra! many
  obtain ⟨i,hi,ei,hei,mi,ri⟩ := exists_nth (phaseAcquired true) (X.tr g) (n := 0)
    (Nat.zero_lt_of_lt many)
  obtain ⟨j,hj,ej,hej,mj,rj⟩ := exists_nth (phaseAcquired true) (X.tr g) many
  have lt : i < j := by
    by_contra! rev
    have := countP_take_mono (phaseAcquired true) (X.tr g) rev
    omega
  obtain ⟨_,_,_,_,rfl⟩ := opening hi hei mi
  obtain ⟨_,_,_,_,rfl⟩ := opening hj hej mj
  exact (by decide : ¬ 3428 ≤ 3425) (afterFirstScoreSuccess hMax.1 hei hej lt)

end PTX.Kernels.TmlFa4Fwd.Softmax
