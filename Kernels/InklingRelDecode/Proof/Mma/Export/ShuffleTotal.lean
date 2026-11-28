-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerDeadline
import Kernels.InklingRelDecode.Proof.Common.WorkerBalance
import Kernels.InklingRelDecode.Proof.Mma.InvNext
import Lemmas.Step.ExitLast

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Sched PTX.Frame

private theorem toward_dispatch {L g d e dn} (step : next L g d e=some (some dn))
    (ret : dn.site=.dispatch) : d.site=.setMaxRegInc := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> try rfl
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals try contradiction
  all_goals try (rename_i bs _; cases h : (rebuild 3 bs).toOption <;> simp [h] at step)
  all_goals cases step
  all_goals simp only [afterQk,iterNext,issueNext,startSite] at ret
  all_goals repeat' split at ret
  all_goals contradiction

/-- Even a lane that loses every election executes both broadcasts for each block
before returning to dispatch. The startup broadcast contributes ordinal zero. -/
public theorem exited_shuffles {Q L m X g k pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (words : RoleBytes L X) (hu : NoUbLane X g) (warp : g%L.block/32=7)
    (exit : X.get (g,k)=some ⟨pc,.exit⟩) :
    1+2*Lib.blocksOf Q L (g/L.block)≤((X.tr g).take k).countP Execution.isShfl := by
  by_contra! short
  have hg := lt_of_get hX exit
  let cap := Lib.Slots.finish+285
  have no : threadTime (schedule Q L) X g≤cap ∧ ∀ u p, X.get (g,u)≠some ⟨p,.exit⟩ := by
    apply worker_deadline hp hX words hu hg (.inr warp) (by decide : 284<Lib.Slots.finish+285)
      (fun _ => False) Inv (by omega) (fun _ => rfl) (fun _ => False.elim)
      (fun d good => Nat.le_trans (time_bounds good).2 (by omega))
    · intros; contradiction
    · intro _ _ _ d _ _ _ _ _ good
      have := (time_bounds good).2
      dsimp [cap]; omega
    · intros; contradiction
    · intro w x call d n u e dn get hs nu good go
      refine ⟨inv_next good go,?_⟩
      intro back
      obtain ⟨_,ref,countQ,countP,-⟩ := (reached_table hf hg (noUbBefore_of_get hX get) hs).2
      have lim := ref_count ref (by rw [toward_dispatch go back]; rfl)
      have bal := mma_balance hp hX hf hg warp (noUbBefore_of_get hX get) hs
      obtain ⟨s,i,v⟩ := d
      obtain rfl : s=.setMaxRegInc := toward_dispatch go back
      change low v=Lib.blocksOf Q L (g/L.block) at lim
      change n (.poll 2462)=runCount (low v) at countQ
      change n (.poll 2510)=runCount (low v) at countP
      change n .shfl+0=1+n (.poll 2462)+n (.poll 2510) at bal
      have valid : Lib.blocksOf Q L (g/L.block)≤2147483646 := Lib.iter_admitted hp hg
      simp only [lim,runCount,valid,ite_true] at countQ countP
      have moves : u≤k := by
        have len := (List.getElem?_eq_some_iff.mp get).1
        have done := Execution.exit_last hX hg exit
        change u<(X.tr g).length at len
        omega
      have mono := countP_take_mono Execution.isShfl (X.tr g) moves
      have obs : n .shfl=((X.tr g).take u).countP Execution.isShfl := fcount hs _
      omega
  exact no.2 k pc exit

/-- **A lane of the MMA warp that exited polled `kv_ready` once per block**: a lane that loses
every election still polls (the poll count is the lane's, not the leader's). -/
public theorem exited_polls {Q L m X g k pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (warp : g%L.block/32=7)
    (exit : X.get (g,k)=some ⟨pc,.exit⟩) :
    Lib.blocksOf Q L (g/L.block)≤pollRound 2462 ((X.tr g).take k) := by
  by_contra! short
  have hg := lt_of_get hX exit
  let cap := Lib.Slots.finish+285
  have no : threadTime (schedule Q L) X g≤cap ∧ ∀ u p, X.get (g,u)≠some ⟨p,.exit⟩ := by
    apply worker_deadline hp hX words (hu.worker (by omega)) hg (.inr warp)
      (by decide : 284<Lib.Slots.finish+285)
      (fun _ => False) Inv (by omega) (fun _ => rfl) (fun _ => False.elim)
      (fun d good => Nat.le_trans (time_bounds good).2 (by omega))
    · intros; contradiction
    · intro _ _ _ d _ _ _ _ _ good
      have := (time_bounds good).2
      dsimp [cap]; omega
    · intros; contradiction
    · intro w x call d n u e dn get hs nu good go
      refine ⟨inv_next good go,?_⟩
      intro back
      obtain ⟨_,ref,countQ,_⟩ := (reached_table hf hg (noUbBefore_of_get hX get) hs).2
      have lim := ref_count ref (by rw [toward_dispatch go back]; rfl)
      obtain ⟨s,i,v⟩ := d
      obtain rfl : s=.setMaxRegInc := toward_dispatch go back
      change low v=Lib.blocksOf Q L (g/L.block) at lim
      change n (.poll 2462)=runCount (low v) at countQ
      have valid : Lib.blocksOf Q L (g/L.block)≤2147483646 := Lib.iter_admitted hp hg
      simp only [lim,runCount,valid,ite_true] at countQ
      have moves : u≤k := by
        have len := (List.getElem?_eq_some_iff.mp get).1
        have done := Execution.exit_last hX hg exit
        change u<(X.tr g).length at len
        omega
      have mono : pollRound 2462 ((X.tr g).take u)≤pollRound 2462 ((X.tr g).take k) :=
        countP_take_mono (okPollAt 2462) (X.tr g) moves
      have obs : n (.poll 2462)=pollRound 2462 ((X.tr g).take u) := fcount hs _
      omega
  exact no.2 k pc exit

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
