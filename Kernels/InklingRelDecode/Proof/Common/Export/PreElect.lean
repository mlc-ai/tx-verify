-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Kernels.InklingRelDecode.Proof.Lib.Slots
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Order.ElectOrdinal
import Kernels.InklingRelDecode.Proof.Common.PreElect
import all Kernels.InklingRelDecode.Proof.Common.Time
import all Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Flow.NotBulk

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Sched

private theorem before {Q L m X g k st} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hg : g<L.threads) (warp : g%L.block/32=6)
    (work : Iface.preloadCount Q L (g/L.block)<Lib.blocksOf Q L (g/L.block))
    (noVote : (X.tr g).countP isElectEv=0) (clean : NoUbBefore X g k) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some st)) :
    (schedule Q L).time g st ≤ Lib.Slots.frame (Iface.preloadCount Q L (g/L.block))+5 ∧
      (thread Q L g).pc st ≠ 2855 := by
  have clear : st.2 .elect=0 := by
    rw [fcount hs]
    exact Nat.le_zero.mp (noVote ▸ (List.take_sublist k (X.tr g)).countP_le (p := isElectEv))
  obtain ⟨s,n⟩ := st
  rcases s with s|⟨r,d⟩
  · obtain ⟨s,t,x,w⟩ := s
    change startupClock _ ≤ _ ∧ s.pc≠2855
    cases s
    case' enter r => cases r
    all_goals constructor
    all_goals first | decide | (simp only [startupClock,Lib.Slots.frame]; omega)
  · rcases r with (r|r)
    · cases r with
      | prologue =>
        have low := data_warp hp hX hk hs
        omega
      | dispatch w x =>
        rcases d with s|⟨i,s⟩
        · have early := loader_before_vote hp hX hf words warp work hk hs clean clear
          obtain ⟨s,r⟩ := s
          obtain ⟨rfl,h|h|h⟩ := early <;> cases h
          all_goals constructor
          all_goals first | (change (2337:Nat)≠2855; decide) | (change (2338:Nat)≠2855; decide) |
            (change (2340:Nat)≠2855; decide) |
            (simp only [schedule,siteClock,workerClock,dispatchClock,Lib.Slots.publish,
              Lib.Slots.frame,ite_true]; omega)
        · have inv := (reached_table hf hg clean hs).2
          cases i with
          | mma =>
            have other : g%L.block/32=7 := inv.1
            omega
          | loader =>
            obtain ⟨_,ref,ord,_⟩ := inv
            have bal := loader_balance hp hX hf hg warp clean hs
            change n .elect=0 at clear
            rw [clear,Nat.zero_add,ord] at bal
            refine ⟨(Loader.pre_elect_time work (Lib.blocksOf_lt hp hg) ref bal).1,?_⟩
            change s.site.pc≠2855
            generalize s.site=site
            cases site <;> repeat' first | decide +kernel | (rename_i j; revert j)
    · exact (launch_lane hp hX hk hs).elim

/-- While the split owes a recurrent issue, a loader without any election
has not exited and its clock still precedes the first recurrent copy. -/
public theorem loader_pre_elect {Q L m X g} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hg : g<L.threads) (warp : g%L.block/32=6)
    (work : Iface.preloadCount Q L (g/L.block)<Lib.blocksOf Q L (g/L.block))
    (hu : NoUbOutside L X) (noVote : (X.tr g).countP isElectEv=0) :
    (∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩) ∧
    threadTime (schedule Q L) X g ≤
      Lib.Slots.readyCopy (Iface.preloadCount Q L (g/L.block)) 0 false := by
  have clean (j : Nat) : NoUbBefore X g j := (hu.worker (by omega)).before j
  constructor
  · intro k pc he
    obtain ⟨st,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
      hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
    have off := (before hp hX hf words hg warp work noVote (clean k)
      (List.getElem?_eq_some_iff.mp he).1.le hs).2
    have pcEq := event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    obtain ⟨_,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX he
    · cases bad
    have ret := Lib.ret_pc' code fire rfl
    have eq : pc=2855 := List.mem_singleton.mp ret
    exact off (pcEq.symm.trans eq)
  · change threadTime (schedule Q L) X g ≤ Lib.Slots.frame (Iface.preloadCount Q L (g/L.block))+6
    unfold threadTime
    split
    · rename_i d h
      exact Nat.le_trans (before hp hX hf words hg warp work noVote (clean _) (by omega) h).1
        (Nat.le_succ _)
    · exact Nat.zero_le _
    · split
      · rename_i d h
        have early := (before hp hX hf words hg warp work noVote (clean _) (by omega) h).1
        omega
      · exact Nat.zero_le _

end PTX.Kernels.InklingRelDecode.Proof.Export
