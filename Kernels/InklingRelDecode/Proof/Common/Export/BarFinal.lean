-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.UbPrefix
import Kernels.InklingRelDecode.Proof.Common.Staged.Early
public import Kernels.InklingRelDecode.Proof.Common.BarCount0
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Kernel.Progress.BarPhasedSteps
import Kernels.InklingRelDecode.Proof.Common.Export.TcLag
import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Kernels.InklingRelDecode.Proof.Common.FinalCap
import Kernels.InklingRelDecode.Proof.Common.FinalPrefix
import Kernels.InklingRelDecode.Proof.Common.WorkerBar
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import all Kernels.InklingRelDecode.Proof.Common.EndTime
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section

/-! # The last generation of barrier 0

A lane without a last-generation arrival is no later than the final rendezvous, whose clock is
`finish + 292`, and has not exited. A lane has one last-generation arrival. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Sched

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A lane has at most one last-generation arrival.** -/
public theorem final_one {j pc j'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g, j) = some ⟨pc, .bar 0 none .sync⟩) (hord : 2 ≤ c0 X g j)
    (h' : BarFinalArr X 0 2 g j') : j' = j := by
  obtain ⟨pc', md', he', hord'⟩ := h'
  obtain rfl : md' = .sync := (Lib.recorded_bar hX hp.block he').1
  have fin := (final_late hp hX he).mpr hord
  have fin' := (final_late hp hX he').mpr hord'
  have mem (a b : Nat) (pa pb : Nat) (ha : X.get (g, a) = some ⟨pa, .bar 0 none .sync⟩)
      (hb : X.get (g, b) = some ⟨pb, .bar 0 none .sync⟩) (ab : a < b)
      (fa : Lib.finalSync pa = true) (fb : Lib.finalSync pb = true) : False := by
    have first := final_first hp hX hb fb
    have mem : (⟨pa, .bar 0 none .sync⟩ : Event) ∈ (X.tr g).take b :=
      List.mem_of_getElem? (by rw [List.getElem?_take_of_lt ab]; exact ha)
    exact List.countP_eq_zero.mp first _ mem fa
  rcases Nat.lt_trichotomy j' j with lt | eq | gt
  · exact (mem j' j pc' pc he' he lt fin' fin).elim
  · exact eq
  · exact (mem j j' pc pc' he he' gt fin fin').elim

/-- A last-generation arrival is in any prefix with a final-rendezvous event. -/
private theorem arrival_of {y t} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (nuy : NoUbLane X y)
    (h : 0 < ((X.tr y).take t).countP (fun e => Lib.finalSync e.pc)) :
    ∃ j, BarFinalArr X 0 2 y j := by
  obtain ⟨u, ev, get, hit, -⟩ := MbarRing.Slot.exists_nth_countP
    (fun e : Event => Lib.finalSync e.pc) (c := 0) h
  have ub := (List.getElem?_eq_some_iff.mp get).1
  rw [List.length_take] at ub
  have ut : u < t := by omega
  rw [List.getElem?_take_of_lt ut] at get
  have kind := Lib.final_kind hX (i := (y, u)) get hit (nuy.kind get)
  obtain ⟨p, kd⟩ := ev
  cases kind
  exact ⟨u, p, .sync, get, (final_late hp hX get).mp hit⟩

/-- **A lane without a last-generation arrival has not exited and is no later than the final
rendezvous.** -/
public theorem bar0_final_lag {j pc y} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g, j) = some ⟨pc, .bar 0 none .sync⟩) (hord : 2 ≤ c0 X g j)
    (hy : y < L.threads) (nuy : NoUbLane X y) (hno : ∀ j', ¬ BarFinalArr X 0 2 y j') :
    (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
      threadTime (schedule Q L) X y ≤ timeAt (schedule Q L) X g j := by
  have hg := Frame.lt_of_get hX he
  have fin := (final_late hp hX he).mpr hord
  have zero (t : Nat) : ((X.tr y).take t).countP (fun e => Lib.finalSync e.pc) = 0 := by
    rcases Nat.eq_zero_or_pos (((X.tr y).take t).countP (fun e => Lib.finalSync e.pc)) with h | h
    · exact h
    · exact absurd (arrival_of hp hX nuy h) (fun ⟨j', h'⟩ => hno j' h')
  have tg : timeAt (schedule Q L) X g j = Lib.Slots.finish + 292 := by
    obtain ⟨s, hs, -⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX he
      (fun _ f h => by simp at h) (hf g hg j)
    have hk := (List.getElem?_eq_some_iff.mp he).1.le
    have cap := final_cap_state hp hX hf words hg hk hs (Frame.noUbBefore_of_get hX he)
    have hpc : pc = (thread Q L g).pc s :=
      Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    rw [time_at hs]
    rw [← hpc] at cap
    exact (cap (by simp [Lib.afterFinal, Lib.finalSync] at fin ⊢; omega)).2.2 fin
  rw [tg]
  refine ⟨fun k pc' hx => ?_, ?_⟩
  · obtain ⟨u, p, -, hu, ho⟩ := exit_final_bar hp hX hx
    exact hno u ⟨p, .sync, hu, ho⟩
  · rw [threadTime_eq_timeAt]
    rcases tc_time_cases hf hy (X.tr y).length with hal | h0 | ⟨hpos, hal, hteq⟩
    · obtain ⟨s, hs⟩ := alive_iff.1 hal
      rw [time_at hs]
      have pre := final_prefix hp hX hy (nuy.before _) hs
      rw [zero] at pre
      have cap := final_cap_state hp hX hf words hy le_rfl hs (nuy.before _)
      exact (cap pre.symm).1
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨s, hs⟩ := alive_iff.1 hal
      have hu : (X.tr y).length - 1 < (X.tr y).length := by omega
      obtain ⟨e, ge⟩ : ∃ e, X.get (y, (X.tr y).length - 1) = some e :=
        ⟨_, List.getElem?_eq_getElem hu⟩
      have pre := final_prefix hp hX hy (nuy.before _) hs
      rw [zero] at pre
      have cap := final_cap_state hp hX hf words hy (by omega) hs (nuy.before _)
      have hpc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX ge hs (nuy.kind ge)
      have nf : Lib.finalSync ((thread Q L y).pc s) = false := by
        by_contra hb
        simp only [Bool.not_eq_false] at hb
        have := arrival_of hp hX nuy (t := (X.tr y).length) (by
          obtain ⟨p, k⟩ := e
          have step := countP_take_succ (p := fun e : Event => Lib.finalSync e.pc) (g := y) ge
            (by rw [hpc] at *; exact hb)
          rw [Nat.sub_add_cancel hpos, List.take_length] at step
          have z0 := zero ((X.tr y).length - 1)
          rw [List.take_length]
          omega)
        exact absurd this (fun ⟨j', h'⟩ => hno j' h')
      rw [hteq, time_at hs]
      have := (cap pre.symm).2.1 nf
      omega

/-- **A worker lane's last-generation arrival follows exactly the two startup rendezvous.** -/
public theorem worker_final_c0 {j pc y} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (y, j) = some ⟨pc, .bar 0 none .sync⟩) (hord : 2 ≤ c0 X y j)
    (lw : 128 ≤ y % L.block) : c0 X y j = 2 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hs, -⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ f h => by simp at h) (hf y hg j)
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  have hpc : pc = (thread Q L y).pc s :=
    Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  have fin := (final_late hp hX he).mpr hord
  have a := worker_final_count hp hX words hk hs (Frame.noUbBefore_of_get hX he) lw
    (by rw [← hpc]; exact fin)
  have b := fcount hs (.bar 0)
  simp only [cls_bar0] at b
  exact b.symm.trans a

end PTX.Kernels.InklingRelDecode.Proof.Export
