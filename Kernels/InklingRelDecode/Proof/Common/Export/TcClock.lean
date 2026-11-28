-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Softmax.Export.TcLag
import Kernels.InklingRelDecode.Proof.Common.TcState
import all Kernels.InklingRelDecode.Proof.Common.EndTime
import all Kernels.InklingRelDecode.Proof.Common.Time
import Lemmas.Kernel.Progress.TcCollU
public import Lemmas.Kernel.Progress.Blocked

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof PTX.Sched PTX.Tmem.Pair TcState
variable {Q : Params} {L : Launch} {g : Nat}
/-- **After a collective `tcgen05` event the lane's clock is later.** -/
public theorem tc_after {m X j pc k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g < L.threads)
    (he : X.get (g, j) = some ⟨pc, k⟩) (tc : isTcColl ⟨pc, k⟩ = true) :
    timeAt (schedule Q L) X g j < timeAt (schedule Q L) X g (j + 1) := by
  obtain ⟨s, hs, -⟩ := coll_state hp hX hf he tc
  have ne := tracked_ne hf hg (j + 1)
  rcases h1 : Frame.stateAt (thread Q L) X g (j + 1) with _ | _ | d'
  · rw [time_at hs, time_dead hs h1]
    exact Nat.lt_succ_self _
  · exact absurd h1 ne
  · rw [time_at hs, time_at h1]
    exact (coll_after hp hX hf he tc hs h1).1
/-- **The clocks of a lane's collective events rise with their order.** -/
public theorem tc_time_lt {m X j j' pc pc' k k'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hu : NoUbLane X g)
    (hg : g < L.threads) (he : X.get (g, j) = some ⟨pc, k⟩) (he' : X.get (g, j') = some ⟨pc', k'⟩)
    (tc : isTcColl ⟨pc, k⟩ = true) (tc' : isTcColl ⟨pc', k'⟩ = true) (hj : j < j') :
    timeAt (schedule Q L) X g j < timeAt (schedule Q L) X g j' := by
  obtain ⟨s, hs, -, -, nub, cls⟩ := coll_state hp hX hf he tc
  obtain ⟨s', hs', -, -, nub', cls'⟩ := coll_state hp hX hf he' tc'
  rw [time_at hs, time_at hs']
  have hlen : j' < (X.tr g).length := (List.getElem?_eq_some_iff.mp he').1
  have soft : SoftEpi s → siteTime s < siteTime s' := by
    intro se
    obtain ⟨s1, hs1, -⟩ := next_of hp hX hf hg hu hs (by omega)
    obtain ⟨lt, se1⟩ := coll_after hp hX hf he tc hs hs1
    obtain ⟨s2, hs2, -, le⟩ := chain hp hX hf hu hg hs1 (se1 se) (show j + 1 ≤ j' by omega) hlen
    rw [hs'] at hs2
    cases hs2
    omega
  rcases cls with ⟨st, n, rfl, hpc, hpc2⟩ | ⟨w, ent, d, n, rfl, hpc, hl⟩ |
      ⟨w, ent, d, n, rfl, hpc, hl⟩
  · have pcs := siteTime_startup_pc (Q := Q) (L := L) (g := g) st n
    rw [← hpc] at pcs
    have pc22 : siteTime (Q := Q) (L := L) (g := g) (.inl st, n) ≤ 22 := by
      rcases hpc2 with h | h <;> simp [h] at pcs <;> omega
    rcases cls' with ⟨st', n', rfl, hpc', hpc2'⟩ | ⟨w, ent, d, n', rfl, hpc', hl⟩ |
        ⟨w, ent, d, n', rfl, hpc', hl⟩
    · have pcs' := siteTime_startup_pc (Q := Q) (L := L) (g := g) st' n'
      rw [← hpc'] at pcs'
      have tm := Export.tc_tmem hp hX hf he tc
      have tm' := Export.tc_tmem hp hX hf he' tc'
      have nu : ∀ f, (⟨pc, k⟩ : Event).kind ≠ .ub f := by
        intro f h
        change k = .ub f at h
        subst h
        simp [isTcColl] at tc
      have isT : isTmemOp ⟨pc, k⟩ = true := by
        have := (Lib.tcColl_event hX he nu).symm.trans tc
        rcases hpc2 with h | h <;> (subst h; simpa [Lib.dataPcs] using this)
      have ge := PTX.Frame.Handoff.countP_take_succ_ge (P := isTmemOp) (es := X.tr g) (i := j)
        (e := j' - 1) he isT (by omega)
      rw [Nat.sub_add_cancel (by omega)] at ge
      change tmemOps ((X.tr g).take j) + 1 ≤ tmemOps ((X.tr g).take j') at ge
      rcases hpc2 with h | h <;> rcases hpc2' with h' | h' <;> simp [h, h'] at tm tm' pcs pcs' <;>
        omega
    · have := Softmax.Export.time_coll (hpc' ▸ hl)
      rw [siteTime_soft]
      omega
    · have := Epilogue.Export.time_fin d
      rw [siteTime_epi]
      omega
  · exact soft (.inl ⟨_, _, _, _, rfl⟩)
  · exact soft (.inr ⟨_, _, _, _, rfl⟩)
/-- **A lane waiting at a collective `tcgen05` event steps** when its warp-mates are no later. -/
public theorem tc_steps {m X g} (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hlag : ∀ {g h j k}, g < L.threads → h < L.threads → SameWarp L g h → X.TcK (g, j) k →
      (X.tr h).countP isTcColl ≤ k → threadTime (schedule Q L) X h ≤ timeAt (schedule Q L) X g j)
    (hafter : ∀ {g j k}, g < L.threads → X.TcK (g, j) k →
      timeAt (schedule Q L) X g j < timeAt (schedule Q L) X g (j + 1))
    (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g) (hw : Sched.TcWait L X g) :
    Sched.Steps (schedule Q L) m X (.thread g) :=
  Sched.tc_stepsU (M := schedule Q L) (fun _ hg => thread_sound hp hg) hs
    (fun h k hh => tracked_ne hf hh k)
    (fun {g h j k d} hg hh sw hk hd hle => by
      have := hlag hg hh sw hk hle
      rw [time_at hd] at this
      exact this)
    (fun {g j k d} hg hk hd => by
      rcases h1 : Frame.stateAt (thread Q L) X g (j + 1) with _ | _ | d'
      · exact .inr h1
      · exact absurd h1 (tracked_ne hf hg _)
      · refine .inl ⟨d', h1, ?_⟩
        have := hafter hg hk
        rw [time_at hd, time_at h1] at this
        exact this)
    hmax hpd hrel hw
