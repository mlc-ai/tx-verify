-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Window
import Kernels.InklingRelDecode.Proof.Prologue.Export.NoUbWf
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.FollowHead
import Kernels.InklingRelDecode.Proof.Common.FollowStartup
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.Where
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # The events of a lane are well-formed for the window of the strict prologue

`WfG` of a clean event of a lane that is not at the barrier before the softmax: the prologue's
`Wf`, the zero word the startup's load of the base word reads, and the warp index its shuffle
delivers. Also `followedD`: the value thread machine follows the lane. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Strict

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem site13 (s : Startup.Site) (h : s.pc = 13) : s = .ld0 := by
  revert h
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem site17 (s : Startup.Site) (h : s.pc = 17) : s = .shfl := by
  revert h
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

/-- **The value thread machine follows the lane.** -/
theorem followedD (hf : Follow Q L X) (hg : g < L.threads) (k : Nat) :
    Frame.FollowedAt (threadD Q L) (fun g σ => guardedTable Q L g (eraseThread Q L g σ)) X g k := by
  refine ⟨fun h => ?_, fun d hd => followD hf hg hd⟩
  have hm := Frame.stateAt_map (threadD_stepMap (Q := Q) (L := L)) X g k
  rw [h] at hm
  exact (hf g hg k).1 hm.symm

/-- A clean event below pc 27 is fired from a state of the startup. -/
private theorem start_of_event (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {ev : Event} (he : X.get (g, k) = some ev)
    (clean : ∀ f, ev.kind ≠ .ub f) (hlt : ev.pc < 27) :
    ∃ t n, Frame.stateAt (thread Q L) X g k = some (some (.inl t, n)) ∧ ev.pc = t.site.pc := by
  obtain ⟨s, hs, -⟩ := Frame.good_stateU (J := fun _ _ => True)
    (fun g hg => thread_sound hp hg) hX he (fun _ f h => clean f (congrArg Event.kind h))
    ⟨control_tracked hp hX g k hg, fun _ _ => trivial⟩
  have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs clean
  obtain ⟨t, n, rfl⟩ := (pos ▸ state_role s).startup hlt
  exact ⟨t, n, hs, pos⟩

/-- **A clean event of a lane that is not at the barrier before the softmax is well-formed** for
the window of the strict prologue. -/
theorem wfg_event (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (hg : g < L.threads) {ev : Event}
    (he : X.get (g, k) = some ev) (clean : ∀ f, ev.kind ≠ .ub f) (h573 : ev.pc ≠ 573) :
    WfG Q L g ev := by
  refine ⟨wf_event hp hX hf hg he clean, h573, fun a bs hpc hk => ?_,
    fun _ m' a b c recv ok hpc hk => ?_⟩
  · obtain ⟨t, n, hs, pos⟩ := start_of_event hp hX hg he clean (by omega)
    have hev := start_ev hp hX he hs clean
    unfold Startup.Ev at hev
    rw [site13 t.site (pos.symm.trans hpc)] at hev
    obtain ⟨ac, bs', heq, hl, hsz, -⟩ := hev
    rw [heq] at hk he
    simp only [Kind.rd.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact base he hl hsz
  · obtain ⟨t, n, hs, pos⟩ := start_of_event hp hX hg he clean (by omega)
    have hsite := site17 t.site (pos.symm.trans hpc)
    have hev := start_ev hp hX he hs clean
    unfold Startup.Ev at hev
    rw [hsite] at hev
    obtain ⟨recv', ok', heq⟩ := hev
    have hlen := (List.getElem?_eq_some_iff.mp he).1.le
    have ord := startup_ordinal hp hX hlen (by simp [Startup.enterOf, hsite]) hs
    rw [heq] at hk he
    simp only [Kind.shfl.injEq] at hk
    obtain ⟨-, -, -, -, rfl, rfl⟩ := hk
    exact startup_recv hp hX he ord
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
