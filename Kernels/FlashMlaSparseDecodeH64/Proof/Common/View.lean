-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound
public import Lemmas.Kernel.Safety.TableU
public import Lemmas.Kernel.Counted
public import Lemmas.Kernel.Progress.NextEv
public import Lemmas.Kernel.FrameU
public import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The state behind an event (for the roles' exports)

Under `Follow`, an event of a launched thread that is no undefined behaviour is fired from a state
of the thread machine with the role table's invariant and shape (`ev_state`, from the UB-tolerant
soundness `thread_sound` and the shape obligation `shapeOk`); its ghost counts are the prefix
counts of the thread's trace (`Frame.count_eq`). An event before which the thread passed no
barrier-0 event is the startup's (`startup_view`): every fragment's invariant has passed it.
A role's export file imports this file privately; files above `Common/` do not. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The state behind an event.** -/
theorem ev_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ σ, Frame.stateAt (thread P L) X g k = some (some σ) ∧ (table P L).J g σ ∧
      (thread P L g).inv σ ∧ (table P L).Ev g σ e := by
  have hF := follow_iff.mp hFw
  exact Frame.RoleTable.ev_of_ne_ubU (T := table P L) (fun _ _ => thread_sound hp) hX
    (shapeOk hp _).toShapeOkU hF (Frame.lt_of_get hX he) he hub

/-- The ghost count of a class at the state behind an event is the thread's prefix count. -/
theorem state_count {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) (c : Cls) :
    σ.2 c = ((X.tr g).take k).countP (cls c) :=
  Frame.count_eq (C := fun g => Code.glue (startupCode P L g)
      (Code.withStubs (frag P L g) Entry.pc) (Code.gatedExit (startupEnter P L g) (sel P L g)))
    (cls := fun _ => cls) hσ c

/-- **A state before an event has counted no undefined behaviour** (it would be the thread's
last event). -/
theorem state_ub (hX : Consistent L kernel Assumptions.all m X) {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) (he : X.get (g, k) = some e) :
    σ.2 .ub = 0 := by
  rw [state_count hσ .ub]
  refine List.countP_eq_zero.mpr fun f hf hcl => ?_
  obtain ⟨j, hj, hfj⟩ := List.getElem_of_mem hf
  have hjk : j < k := by simp only [List.length_take] at hj; omega
  have hget : X.get (g, j) = some f := by
    show (X.tr g)[j]? = some f
    rw [← List.getElem?_take_of_lt hjk, List.getElem?_eq_getElem hj, hfj]
  obtain ⟨pc, kd⟩ := f
  cases kd <;> simp [cls] at hcl
  have := ub_last hX hget he
  omega

/-- **An event before which the thread passed no barrier-0 event is fired from a startup state**,
with the startup's invariant (at the prefix counts) and shape. -/
theorem startup_view (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (h0 : ((X.tr g).take k).countP (cls .bar0) = 0) :
    ∃ d, Startup.Ref d (((X.tr g).take k).countP (cls .mbInit)) 0 ∧ Startup.Ev L g d e ∧
      Startup.exitOf d = none := by
  obtain ⟨⟨s, n⟩, hσ, hJ, hi, hev⟩ := ev_state hp hX hFw he hub
  have hb := state_count hσ .bar0
  have hm := state_count hσ .mbInit
  simp only at hb hm
  rcases s with d | ⟨i | r, d'⟩
  · refine ⟨d, ?_, hev, ?_⟩
    · obtain ⟨hJ', -⟩ : Startup.Ref d (n .mbInit) (n .bar0) ∧ _ := hJ
      rw [hm, hb, h0] at hJ'
      exact hJ'
    · have hx := hi.2
      simpa [Code.gatedExit, startupEnter] using hx
  · exfalso
    have hJ' : 1 ≤ n .bar0 := by cases i <;> exact hJ.1
    omega
  · exact hJ.elim

/-- **The state behind a next event**: under `Follow`, a next event of a lane (no undefined
behaviour) is fired from the lane's state at its trace's end, with the role table's invariant and
shape, at the state's pc. -/
theorem next_state (hp : Pre P L m) (hFw : Follow P L X)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ σ, Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ) ∧
      (table P L).J g σ ∧ (thread P L g).inv σ ∧ (table P L).Ev g σ e ∧
      e.pc = (thread P L g).pc σ := by
  have hF := follow_iff.mp hFw
  obtain ⟨Y, hY, hpre, he⟩ := hn
  have hg := Frame.lt_of_get hY he
  have hC : ∀ g < L.threads, (thread P L g).SoundU := fun g _ => thread_sound hp
  have hst : Frame.stateAt (thread P L) Y g (X.tr g).length =
      Frame.stateAt (thread P L) X g (X.tr g).length :=
    Sched.stateAt_congr (by rw [hpre, List.take_length])
  have hG := hF g hg (X.tr g).length
  rcases Frame.firedU hC hY he with ⟨σo, o, hs, -⟩ | ⟨-, pc, f, rfl⟩
  · cases σo with
    | none => exact absurd (hst ▸ hs) hG.1
    | some σ =>
      have hsX : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ) := hst ▸ hs
      obtain ⟨t, ins, o', hat, hi, hc, hf⟩ := Frame.fired_siteU hC hY he hs hub
      exact ⟨σ, hsX, hG.2 σ hsX, hi,
        (shapeOk hp (fun _ => True)).shape g trivial σ t ins e o' (hG.2 σ hsX) hat hi hc hf,
        EventFrame.fires_source_pc hf⟩
  · exact absurd rfl (hub f)

/-- **The state behind a next event has no undefined behaviour**: the lane's state at its trace's
end, when the lane has a next event, has global ub count 0. -/
theorem next_ub (hn : Sched.NextEv L kernel Assumptions.all m X g e) {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ)) : σ.2 .ub = 0 := by
  obtain ⟨Y, hY, hpre, he⟩ := hn
  exact state_ub hY ((Sched.stateAt_congr (by rw [hpre, List.take_length])).trans hσ) he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
