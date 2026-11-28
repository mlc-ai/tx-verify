-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Lib.Slots
public import Lemmas.Flow.ElectLead
import Kernels.InklingRelDecode.Proof.Common.FinalProducer
import all Kernels.InklingRelDecode.Proof.Common.Time
import all Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Flow.NotBulk

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Sched

private theorem mma_before {s : Mma.D} (live : s.site.beforeFinal) (inv : Mma.Inv s) :
    Mma.time s ≤ Lib.Slots.finalCommit := by
  obtain ⟨site,i,v⟩ := s
  have limit := Mma.low_lt v
  cases site <;> try contradiction
  all_goals simp only [Mma.time,Mma.Inv,Mma.D.limit,Mma.Site.position,Mma.slotTime,
    Lib.Slots.finalCommit,Lib.Slots.finish,Lib.Slots.mma,Lib.Slots.frame,Lib.Slots.stride,
    Lib.Slots.enter,Lib.Slots.reuse] at inv ⊢
  all_goals omega

private theorem before {Q L m X g j st} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hg : g<L.threads) (warp : g%L.block/32=7) (wins : ElectLead L g (X.tr g))
    (missing : ∀ i sp, X.get (g,i)≠some ⟨2553,.tc (.commit sp)⟩)
    (bound : j≤(X.tr g).length) (hs : stateAt (thread Q L) X g j=some (some st))
    (nu : NoUbBefore X g j) :
    (schedule Q L).time g st ≤ Lib.Slots.finalCommit ∧ (thread Q L g).pc st≠2855 := by
  have past := before_final_issue hp hX words warp wins missing bound hs nu
  obtain ⟨s,n⟩ := st
  rcases s with s|⟨r,d⟩
  · obtain ⟨s,t,x,w⟩ := s
    change startupClock _≤_ ∧ s.pc≠2855
    cases s
    case' enter r => cases r
    all_goals dsimp only [startupClock,Startup.Site.pc]; decide
  · rcases r with (r|r)
    · cases r with
      | prologue =>
        have := data_warp hp hX bound hs
        omega
      | dispatch w x =>
        rcases d with s|⟨i,s⟩
        · obtain ⟨s,r⟩ := s
          obtain ⟨rfl,h|h|h⟩ := past <;> cases h
          all_goals constructor
          all_goals first | (change (2337:Nat)≠2855; decide) | (change (2338:Nat)≠2855; decide) |
            (change (2340:Nat)≠2855; decide) |
            (simp only [schedule,siteClock,workerClock,dispatchClock,ite_true]; decide)
        · cases i with
          | loader => exact False.elim past
          | mma =>
            have inv := (reached_table hf hg nu hs).1
            refine ⟨mma_before past inv.1,?_⟩
            change s.site.pc≠2855
            generalize s.site=site
            cases site <;> repeat' first | decide +kernel | (rename_i j; revert j)
    · exact (launch_lane hp hX bound hs).elim

/-- With no final notification yet issued, the elected producer is early and has
not exited. The election condition is vacuous before the warp's first election. -/
public theorem final_short {Q L m X g} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hg : g<L.threads) (warp : g%L.block/32=7) (wins : ElectLead L g (X.tr g))
    (missing : ∀ i sp, X.get (g,i)≠some ⟨2553,.tc (.commit sp)⟩) (hu : NoUbOutside L X) :
    threadTime (schedule Q L) X g < Lib.Slots.finalWait ∧
      ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ := by
  have clean (j : Nat) : NoUbBefore X g j := (hu.worker (by omega)).before j
  have gap : Lib.Slots.finalCommit+1<Lib.Slots.finalWait := by decide
  constructor
  · unfold threadTime
    split
    · rename_i d state
      have := (before hp hX hf words hg warp wins missing (by omega) state (clean _)).1
      omega
    · omega
    · split
      · rename_i d state
        have := (before hp hX hf words hg warp wins missing (by omega) state (clean _)).1
        omega
      · omega
  · intro k pc he
    obtain ⟨d,state,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
      hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
    have off := (before hp hX hf words hg warp wins missing
      (List.getElem?_eq_some_iff.mp he).1.le state (clean k)).2
    have pcEq := event_pcU (fun g hg => thread_sound hp hg) hX he state (by simp)
    obtain ⟨_,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX he
    · cases bad
    exact off (pcEq.symm.trans (List.mem_singleton.mp (Lib.ret_pc' code fire rfl)))

end PTX.Kernels.InklingRelDecode.Proof.Export
