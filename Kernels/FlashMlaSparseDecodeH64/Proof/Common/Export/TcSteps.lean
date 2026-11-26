-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Lemmas.Kernel.Progress.TcCollU
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0TcLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Bound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Measure
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.TcOrd

@[expose] public section

/-! # Progress at a warp-collective `tcgen05` event

A pending lane blocked at a warp-collective event some lane of its warp has not reached steps
(`tc_steps`, by `Sched.tc_stepsU`). The time table's two facts are taken privately here:

* a collective event is of warps 0–3 (`tc_warp`, from the Tensor Memory rows: the MMA warp's
  events are not collective), and the lag is `w0_tcLag`;
* after a collective event the lane's state is later (`tc_after`): warpgroup 0's collectives
  raise its place (`Wg0.place_next`), the startup's allocation (time 92) is followed by the
  address store or the read (93, 94) and its relinquishment (98) by the CTA barrier (99). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X)
include hp hX hFw

omit hnu in
/-- A collective event is of warps 0–3. -/
theorem tc_warp (hg : g < L.threads) {j : Nat} {e : Event} (he : X.get (g, j) = some e)
    (hc : isTcColl e = true) : warp L g < 4 := by
  have hR := tmem_rows hp hX hFw
  obtain ⟨pc, kd⟩ := e
  obtain ⟨a, rfl⟩ := isTcColl_kind hc
  rcases hR.place hg he rfl with h | h | h | h | h | h | h
  · obtain ⟨hw, -⟩ := hR.startup hg he h rfl
    omega
  · exact h.1
  · exact (hR.wg1 hg he h rfl).elim
  · rcases hR.mma hg he h rfl with h1 | ⟨_, _, -, -, h1, -⟩ | ⟨_, h1, -⟩ | ⟨_, _, -, -, h1, -⟩ |
      ⟨_, _, _, -, -, h1, -⟩ <;> simp only [Kind.tc.injEq] at h1 <;> subst h1 <;>
      simp [isTcColl] at hc
  · exact (hR.tma hg he h rfl).elim
  · exact (hR.index hg he h rfl).elim
  · exact (hR.dequant hg he h rfl).elim

include hnu

/-- **After a collective event the lane's state is later**, or the lane has no state after it. -/
private theorem tc_after (hg : g < L.threads) {j : Nat} {e : Event} {σ : (thread P L g).D}
    (he : X.get (g, j) = some e) (hc : isTcColl e = true)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ)) :
    (∃ σ', Frame.stateAt (thread P L) X g (j + 1) = some (some σ') ∧
      time P L g σ < time P L g σ') ∨ Frame.stateAt (thread P L) X g (j + 1) = none := by
  rcases h1 : Frame.stateAt (thread P L) X g (j + 1) with _ | _ | σ'
  · exact .inr rfl
  · exact absurd h1 ((follow_iff.mp hFw g hg (j + 1)).1)
  refine .inl ⟨σ', rfl, ?_⟩
  have hub := noUb_kind hnu he
  obtain ⟨σm, hσm, hn⟩ := prev_state he h1
  rw [hσ] at hσm
  cases hσm
  obtain ⟨σ0, hσ0, -, -, hev, -⟩ := ev_at hp hX hFw he hub
  rw [hσ] at hσ0
  cases hσ0
  rcases w0_bst hFw hnu (tc_warp hp hX hFw hg he hc) hg hσ with ⟨d, n, rfl, hxd⟩ |
    ⟨d, n, rfl, hC, -, -⟩
  · have hx : ∀ r, d.site ≠ .enter r := fun r h => by simp [Startup.exitOf, h] at hxd
    have hev' : Startup.Ev L g d e := hev
    have hsite := Startup.ev_tmem hx hev'
    rw [← (Startup.ev_tc hx hev').1, hc] at hsite
    rw [next_startup] at hn
    obtain ⟨d1, hs1, rfl⟩ := map_some hn
    have hsite' := hsite.symm
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hsite'
    obtain ⟨site, x1, x2⟩ := d
    simp only at hsite'
    rcases hsite' with rfl | rfl <;> simp only [Startup.succ] at hs1 <;> (try split_ifs at hs1) <;>
      simp only [Option.some.injEq] at hs1 <;> subst hs1 <;>
      simp [Code.enter, Code.gatedExit, startupEnter, Startup.exitOf, time, Startup.time,
        Startup.Site.pc]
  · rw [next_frag] at hn
    obtain ⟨d', hs, rfl⟩ := map_some hn
    have hs' : Proof.Wg0.Control.succ P L g (warpW L g) d e = some (some d') := hs
    obtain ⟨pc, kd⟩ := e
    obtain ⟨a, rfl⟩ := isTcColl_kind hc
    rcases Wg0.place_next hC hs' with ⟨-, hk⟩ | hlt
    · simp [Event.counts] at hk
    · rw [w0_time, w0_time]
      omega

end

/-- **A lane blocked at a warp-collective `tcgen05` event steps.** -/
theorem tc_steps (hp : Pre P L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hFw : Follow P L X) {g : Nat}
    (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g) (hw : Sched.TcWait L X g) :
    Sched.Steps (timed P L) m X (.thread g) := by
  have hX := hmax.1
  have hnu := Sched.safe_noUb (hs.2 X hX)
  rw [timed_eq]
  refine Sched.tc_stepsU (M := ⟨thread P L, time P L⟩) (fun _ _ => thread_sound hp) hs
    (fun h k hh => (follow_iff.mp hFw h hh k).1) ?_ ?_ hmax hpd hrel hw
  · intro g h j k d hg hh hsw hk hd hle
    obtain ⟨⟨e, he, hc⟩, -⟩ := id hk
    have h' := w0_tcLag hp hX hFw hnu (tc_warp hp hX hFw hg he hc) hsw hd hk hle
    rw [timed_eq] at h'
    exact h'
  · intro g j k d hg hk hd
    obtain ⟨⟨e, he, hc⟩, -⟩ := hk
    exact tc_after hp hX hFw hnu hg he hc hd

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
