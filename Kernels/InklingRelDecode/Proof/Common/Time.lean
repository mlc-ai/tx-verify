-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Kernel.Progress.NextEv
import Kernels.InklingRelDecode.Proof.Common.Sound
public import Kernels.InklingRelDecode.Proof.Common.Follow
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Lemmas.Kernel.FrameU
import Kernels.InklingRelDecode.Proof.Epilogue.Time
import Kernels.InklingRelDecode.Proof.Softmax.Time
import Kernels.InklingRelDecode.Proof.Prologue.Time
import Kernels.InklingRelDecode.Proof.Loader.Time
import Kernels.InklingRelDecode.Proof.Mma.Time

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Sched

private def startupClock (d : Startup.D) : Nat :=
  match d.site with
  | .alloc => 2 | .allocWr => 4 | .bar0 => 10 | .ld0 => 12 | .bar1 => 20
  | .relinq => 22 | .shfl => 24 | .enter _ => 26

private def dispatchClock (d : Dispatch.D) : Nat :=
  let finish := Lib.Slots.finish
  let late := if d.round = 0 then 0 else finish+7
  match d.site with
  | .head => if d.round = 0 then 30 else finish + 284
  | .sync => Lib.Slots.publish + late | .read => 283 + late | .idleDec => Lib.Slots.enter
  | .idleSync => Lib.Slots.reuse | .idleSyncAgain => finish + 276 | .idleInc => finish + 280
  | .badSync => 284 + late | .badSyncAgain => 285 + late
  | .loaderEntry | .mmaEntry => Lib.Slots.enter
  | .exitSync => finish + 292 | .exitDealloc => finish + 296 | .ret => finish + 300

private noncomputable def workerClock {Q L g w x} : (workerCode Q L g w x).D → Nat
  | .inl d => dispatchClock d
  | .inr ⟨.loader _, d⟩ => Loader.time d
  | .inr ⟨.mma _, d⟩ => Mma.time d

private noncomputable def siteClock {Q L g} : (thread Q L g).D → Nat
  | (.inl d, _) => startupClock d
  | (.inr ⟨.inl (.dispatch ..), d⟩, _) => workerClock d
  | (.inr ⟨.inl (.prologue _), .inl d⟩, _) => Prologue.time d
  | (.inr ⟨.inl (.prologue _), .inr ⟨_,.inl d⟩⟩, _) => Softmax.time d
  | (.inr ⟨.inl (.prologue _), .inr ⟨_,.inr ⟨_,d⟩⟩⟩, _) => Epilogue.time d
  | (.inr ⟨.inr _,_⟩, _) => 2

/-- Virtual time in the common startup, dispatch rounds and slot schedules. -/
public noncomputable def schedule (Q : Params) (L : Launch) :
    Timed kernel Assumptions.all L := ⟨thread Q L, fun _ => siteClock⟩

private theorem worker_floor {Q L g w x} (d : (workerCode Q L g w x).D) : 2 ≤ workerClock d := by
  rcases d with ⟨s,n⟩ | ⟨n,d⟩
  · cases s <;> simp [workerClock, dispatchClock,
      Lib.Slots.enter,Lib.Slots.reuse,Lib.Slots.publish] <;>
      split_ifs <;> omega
  · cases n with
    | loader => exact (Loader.time_bounds d).1
    | mma =>
      obtain ⟨s,i,v⟩ := d
      cases s <;> simp [workerClock,Mma.time,Mma.slotTime,Lib.Slots.mma,
        Lib.Slots.frame,Lib.Slots.stride,Lib.Slots.enter,Lib.Slots.reuse,Lib.Slots.finish] <;> omega

private theorem schedule_floor {Q L g} (d : (thread Q L g).D) : 2 ≤ (schedule Q L).time g d := by
  obtain ⟨s,n⟩ := d
  rcases s with d | ⟨r,d⟩
  · obtain ⟨s,tm,x,w⟩ := d
    cases s <;> simp [schedule, siteClock, startupClock]
  · rcases r with r | r
    · cases r with
      | dispatch => exact worker_floor d
      | prologue =>
        rcases d with p|⟨_,s|⟨_,e⟩⟩
        · exact Prologue.time_floor p
        · exact Softmax.time_floor s
        · exact Epilogue.time_floor e
    · cases r <;> exact Nat.le_refl 2

/-- A witnessed worker poll has a nonempty prefix and a ranked, live thread. -/
public theorem poll_floor {Q L m X g pc l q sc} (hp : Pre Q L m) (hF : Follow Q L X)
    (hpc : 20 ≤ pc) (he : NextEv L kernel Assumptions.all m X g
      ⟨pc, .wait l q false true sc⟩) :
    X.tr g ≠ [] ∧ 2 ≤ threadTime (schedule Q L) X g := by
  have hg := he.lt
  obtain ⟨Y,hY,hpre,hget⟩ := he
  have hstate := stateAt_congr (C := thread Q L) (X := X) (Y := Y) (g := g) (k := (X.tr g).length)
    (by simp [hpre])
  have hnu : ∀ f, (Event.mk pc (.wait l q false true sc)).kind ≠ .ub f := fun _ => nofun
  rcases Frame.firedU (fun g hg => thread_sound hp hg) hY hget with ⟨σ,o,hs,_⟩ | ⟨_,p,f,h⟩
  · cases σ with
    | none =>
      exact False.elim ((hF g hg _).1 (hstate ▸ hs))
    | some d =>
      have hd := Frame.event_pcU (fun g hg => thread_sound hp hg) hY hget hs hnu
      have hx : Frame.stateAt (thread Q L) X g (X.tr g).length = some (some d) := hstate ▸ hs
      refine ⟨?_, (threadTime_of (M := schedule Q L) hx).symm ▸ schedule_floor d⟩
      intro hempty
      rw [hempty, List.length_nil, Frame.stateAt_zero] at hx
      cases hx
      change pc = (thread Q L g).pc (thread Q L g).init at hd
      have hi : (thread Q L g).pc (thread Q L g).init = (Startup.init L g).site.pc := by
        let P := Startup.code Q L g
        let R := Code.withStubs (frag Q L g) Startup.Entry.pc
        let E := Code.gatedExit (P := P) Startup.enterOf (sel L g)
        change (Code.glue P R E).pc (Code.enter P R E (Startup.init L g)) = _
        rw [Code.enter_none (Code.gatedExit_none.mpr (by unfold Startup.init; split <;> rfl))]
      rw [hi] at hd
      unfold Startup.init at hd
      split at hd <;> simp only [Startup.Site.pc] at hd <;> omega
  · cases h

end PTX.Kernels.InklingRelDecode.Proof
