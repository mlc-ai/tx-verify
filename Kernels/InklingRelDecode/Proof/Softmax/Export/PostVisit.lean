-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.Dissent
public import Kernels.InklingRelDecode.Proof.Lib.PostVisit
import Kernels.InklingRelDecode.Proof.Softmax.Export.PredBar
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData
import Kernels.InklingRelDecode.Proof.Softmax.RescaleChoice

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow Control TcState

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {h : Nat}

private theorem site_of (s : Site) (p : Nat) (hp : p = 2328 ∨ p = 2329 ∨ p = 999)
    (h : s.pc = p) : s = .stO ∨ s = .waitStO ∨ s = .bar20 := by
  subst h
  revert hp
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem flat_not {u e} {p : Event → Bool} (get : X.get (h, u) = some e)
    (hp : p e = false) : ((X.tr h).take (u + 1)).countP p = ((X.tr h).take u).countP p := by
  have : (X.tr h)[u]? = some e := get
  rw [List.take_add_one, this, Option.toList_some, List.countP_append]
  simp [hp]

private theorem flat_bar {u e} {p : Event → Bool} (get : X.get (h, u) = some e)
    (hp : p e = true) : ((X.tr h).take (u + 1)).countP p = ((X.tr h).take u).countP p + 1 := by
  have : (X.tr h)[u]? = some e := get
  rw [List.take_add_one, this, Option.toList_some, List.countP_append]
  simp [hp]

/-- One step back of a Softmax state at a site of the rescale's path after the visit. -/
private theorem back {t} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hu : NoUbLane X h) (ht : t ≤ (X.tr h).length) {s : Site} (hs : s ≠ .setMaxReg)
    (sh : ∃ w ent d n, Frame.stateAt (thread Q L) X h t = some (some (softState w ent d n)) ∧
      d.site = s) :
    ∃ w ent old cnt u ev, u + 1 = t ∧
      Frame.stateAt (thread Q L) X h u = some (some (softState w ent old cnt)) ∧
      X.get (h, u) = some ev ∧ ev.pc = old.site.pc ∧ (∀ f, ev.kind ≠ .ub f) ∧
      ∃ d n, Frame.stateAt (thread Q L) X h t = some (some (softState w ent d n)) ∧
        d.site = s ∧ Control.next ent L h old ev = some (some d) := by
  obtain ⟨w, ent, d, n, hs0, site⟩ := sh
  obtain ⟨u, old, cnt, ev, rfl, hold, gev, nxt⟩ :=
    soft_prev ht (by rintro rfl; exact hs site.symm) hs0
  have nu := hu.kind gev
  exact ⟨w, ent, old, cnt, u, ev, rfl, hold, gev,
    Frame.event_pcU (fun g hg => thread_sound hp hg) hX gev hold nu, nu, d, n, hs0, site, nxt⟩

/-- A state at the store (site `stO`) follows the optional rendezvous of its lane. -/
private theorem visit_stO {t} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hu : NoUbLane X h) (ht : t ≤ (X.tr h).length)
    (sh : ∃ w ent d n, Frame.stateAt (thread Q L) X h t = some (some (softState w ent d n)) ∧
      d.site = .stO) :
    ∃ u kd, u + 1 = t ∧ X.get (h, u) = some ⟨2326, kd⟩ ∧
      ((X.tr h).take u).countP (Execution.isBarId 0) + 1 =
        ((X.tr h).take t).countP (Execution.isBarId 0) := by
  obtain ⟨w, ent, old, cnt, u, ev, rfl, hold, gev, pce, nu, d, n, hs, site, nxt⟩ :=
    back hp hX hu ht (by decide) sh
  have ob := pred_stO nxt site
  obtain ⟨pe, ke⟩ := ev
  have p2326 : pe = 2326 := by simpa [ob, Site.pc] using pce
  subst p2326
  refine ⟨u, ke, rfl, gev, ?_⟩
  have bz : Execution.isBarId 0 ⟨2326, ke⟩ = true := by
    rw [Lib.zero_event hX hp.block gev nu]
    show Lib.zeroSite 2326 = true
    decide +kernel
  rw [flat_bar gev bz]

/-- A state at the store's wait follows the optional rendezvous of its lane. -/
private theorem visit_waitStO {t} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hu : NoUbLane X h)
    (ht : t ≤ (X.tr h).length)
    (sh : ∃ w ent d n, Frame.stateAt (thread Q L) X h t = some (some (softState w ent d n)) ∧
      d.site = .waitStO) :
    ∃ u kd, X.get (h, u) = some ⟨2326, kd⟩ ∧
      ((X.tr h).take u).countP (Execution.isBarId 0) + 1 =
        ((X.tr h).take t).countP (Execution.isBarId 0) := by
  obtain ⟨w, ent, old, cnt, u, ev, rfl, hold, gev, pce, nu, d, n, hs, site, nxt⟩ :=
    back hp hX hu ht (by decide) sh
  have ob := pred_waitStO nxt site
  obtain ⟨u2, kd, hu2, g2, c2⟩ := visit_stO hp hX hu (by omega) ⟨w, ent, old, cnt, hold, ob⟩
  refine ⟨u2, kd, g2, ?_⟩
  have nb : Execution.isBarId 0 ev = false := by
    have : ev.pc = 2328 := by rw [pce, ob]; rfl
    rw [Lib.zero_event hX hp.block gev nu, this]
    decide +kernel
  rw [flat_not gev nb]
  omega

/-- **A lane after the rescale decision of a round, in a round after the first, is past the
visit or has skipped.** -/
public theorem post_visit {t i R pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hu : NoUbLane X h)
    (ht : t ≤ (X.tr h).length) (hpc : pc = 2328 ∨ pc = 2329 ∨ pc = 999)
    (sh : SoftAt Q L X h t pc i R) (pos : 0 < i) : Lib.PostVisit L X h t := by
  obtain ⟨w, ent, d, n, hs, hpcd, hi, hR⟩ := sh
  have site := site_of d.site pc hpc hpcd
  have st : ∃ w ent d' n, Frame.stateAt (thread Q L) X h t =
      some (some (softState w ent d' n)) ∧ d'.site = d.site := ⟨w, ent, d, n, hs, rfl⟩
  rcases site with e | e | e
  · obtain ⟨u, kd, -, g2, c2⟩ := visit_stO hp hX hu ht ⟨w, ent, d, n, hs, e⟩
    exact .inl ⟨u, kd, g2, c2⟩
  · obtain ⟨u, kd, g2, c2⟩ := visit_waitStO hp hX hu ht ⟨w, ent, d, n, hs, e⟩
    exact .inl ⟨u, kd, g2, c2⟩
  · obtain ⟨w', ent', old, cnt, u, ev, rfl, hold, gev, pce, nu, d', n', hs', site', nxt⟩ :=
      back hp hX hu ht (by decide) ⟨w, ent, d, n, hs, e⟩
    rcases pred_bar20 nxt site' with ⟨t1, m1, a1, b1, c1, r1, ok1, kind1, skip1⟩ | t1 |
        ⟨t1, zero⟩
    · right
      obtain ⟨p, kd⟩ := ev
      have pc2 : p = 2255 := by simpa [t1, Site.pc] using pce
      subst pc2
      cases kind1
      obtain ⟨rfl, -, -⟩ := shuffle_2255_shape hp hX gev
      refine ⟨u, a1, b1, c1, r1, ok1, gev, (Control.skip_free L h a1 r1).symm.trans skip1, ?_⟩
      rw [flat_not gev (by simp [Execution.isBarId])]
    · obtain ⟨u2, kd, g2, c2⟩ := visit_waitStO hp hX hu (by omega) ⟨w', ent', old, cnt, hold, t1⟩
      refine .inl ⟨u2, kd, g2, ?_⟩
      have nb : Execution.isBarId 0 ev = false := by
        have : ev.pc = 2329 := by rw [pce, t1]; rfl
        rw [Lib.zero_event hX hp.block gev nu, this]
        decide +kernel
      rw [flat_not gev nb]
      exact c2
    · have hd : d' = d := by
        have h2 := Option.some.inj (Option.some.inj (hs.symm.trans hs'))
        simp [softState] at h2
        exact h2.1.2.2.symm
      subst hd
      omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
