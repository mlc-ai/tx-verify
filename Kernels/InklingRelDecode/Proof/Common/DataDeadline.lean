-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Deadline
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Softmax.Time
import all Kernels.InklingRelDecode.Proof.Common.Time
import all Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Sched

private def pendingData {Q L g} (P : Softmax.Control.D → Prop) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.prologue _),.inr ⟨_,.inl s⟩⟩,_) => P s
  | (.inr ⟨.inl (.prologue _),.inr ⟨_,.inr _⟩⟩,_) => False
  | _ => True

private theorem initial {Q L g P} (s : Startup.D) (n : Cls → Nat) :
    pendingData P (Code.enter (Startup.code Q L g)
      (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> first | trivial | (rename_i r; cases r <;> trivial)

/-- Prior to a missing Softmax production, a data lane may still be running the
prologue. It can enter the epilogue only after leaving the producer invariant. -/
theorem data_deadline {Q L m X g bound} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hu : NoUbLane X g)
    (hg : g<L.threads) (dataLane : g%L.block<128) (large : 600<bound)
    (P : Softmax.Control.D → Prop) (start : P {})
    (clock : ∀ d, P d → Softmax.time d≤bound)
    (seen : ∀ {w ent d n k e}, X.get (g,k)=some e →
      stateAt (thread Q L) X g k=some (some (softState w ent d n)) →
      P d → Softmax.time d≠bound)
    (next : ∀ {w ent d n k e dn}, X.get (g,k)=some e →
      stateAt (thread Q L) X g k=some (some (softState w ent d n)) →
      P d → Softmax.Control.next ent L g d e=some (some dn) →
      P dn ∧ dn.site≠.epilogue) :
    threadTime (schedule Q L) X g≤bound ∧ ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ := by
  apply deadline_of_states hp hX hg
  intro k st hk hs
  have clean : NoUbBefore X g k := hu.before k
  have inv : pendingData P st := by
    apply reference_induction (pendingData P) _ _ hk hs (prefix_ub_zero hs clean)
    · apply initial
    · rintro j ⟨s,n⟩ e ⟨sn,nn⟩ he prev _ old move
      obtain ⟨sub,_⟩ := Code.counted_next_some move
      rcases s with s|⟨r,s⟩
      · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some sub; apply initial
      obtain ⟨_,step,rfl⟩ := Code.glue_inr_some sub
      rcases r with r|r
      · cases r with
        | dispatch => trivial
        | prologue w =>
          rcases s with d|⟨ent,d⟩
          · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some step
            unfold Code.enter
            split <;> first | exact start | trivial
          · obtain ⟨_,localStep,rfl⟩ := Code.glue_inr_some step
            rcases d with d|d
            · obtain ⟨dn,go,rfl⟩ := Code.glue_inl_some localStep
              obtain ⟨p,stay⟩ := next he prev old go
              simp only [Code.enter,epiExit,stay,↓reduceIte]
              exact p
            · exact False.elim old
      · trivial
  obtain ⟨s,n⟩ := st
  rcases s with s|⟨r,d⟩
  · obtain ⟨s,t,x,w⟩ := s
    change startupClock _≤bound ∧ s.pc≠2855 ∧ (_ → startupClock _<bound)
    cases s
    case' enter r => cases r
    all_goals exact ⟨by dsimp only [startupClock]; omega,by decide,
      by dsimp only [startupClock]; omega⟩
  rcases r with r|r
  · cases r with
    | dispatch => have := (worker_warp hp hX hk hs).1; omega
    | prologue w =>
      rcases d with d|⟨ent,d|d⟩
      · have cap : Prologue.time d < 600 := by
          have card : Prologue.allSites.length<500 := by decide +kernel
          have idx := List.idxOf_le_length (a := d.site) (l := Prologue.allSites)
          unfold Prologue.time Lib.Slots.prologue; omega
        have range := d.site.pc_range
        exact ⟨Nat.le_trans cap.le large.le,by change d.site.pc≠2855; omega,
          fun _ => cap.trans large⟩
      · have pc : d.site.pc≠2855 := by
          generalize d.site=s
          cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
        exact ⟨clock d inv,pc,fun lt => Nat.lt_of_le_of_ne (clock d inv)
          (seen (List.getElem?_eq_getElem lt) hs inv)⟩
      · exact False.elim inv
  · exact (launch_lane hp hX hk hs).elim

end PTX.Kernels.InklingRelDecode.Proof
