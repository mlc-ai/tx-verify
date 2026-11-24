-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
public import Lemmas.Kernel.Followed
public import Lemmas.Tcgen05.TcFence
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
import Kernels.TmlFa4Fwd.Proof.LdWarp.Mem
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Lemmas.Step.WarpShfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # What the loader warps' events return, and the never-dropped theorem

`lexpect` assembles the references' expectations at a role state of a loader lane: the launch words
at the scheduler's reads (`expect_word`, `expect_q`, `expect_uk`), the source lanes' values at the
scan's collectives, a word at every shuffle (`sent_word`), the lane's own stores at its local loads
(`local_word`), and the launch's page-table word at the page-table loads (`pg_word`). `good` is
`Frame.followedOn` for the lanes of loader warp `w`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-- The collectives up to an event do not decrease along a thread. -/
theorem μ_mono (X : Execution) (g : Nat) {j k : Nat} (h : j ≤ k) : μ X (g, j) ≤ μ X (g, k) :=
  ((List.take_prefix_take_left (by omega : j + 1 ≤ k + 1)).sublist).countP_le

theorem lex_lt {j k : Nat} (h : j < k) : Frame.lexOrder (μ X) (g, j) (g, k) := by
  rcases Nat.lt_or_eq_of_le (μ_mono X g (Nat.le_of_lt h)) with h' | h'
  · exact .inl h'
  · exact .inr ⟨h', h⟩

set_option maxHeartbeats 4000000 in
/-- **What a loader lane's event at a role state returns is what the references say**: the
launch words at the scheduler's reads, the source lanes' values at its collectives, a word at
every shuffle, the lane's stores at its local loads, and the launch's page-table words at the
page-table loads. -/
theorem lexpect (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat} {bb : Bool} {d : D}
    {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g bb d n)))
    (hbw : wOf bb = w) (hJ : Loader.Ref p L g w (d, lcn n))
    (hF : LFits p L g d (n .shfl) (n .vote) (n (.load .commit)))
    (IH : isColl e = true → GoodUpTo p L w X (n .shfl + n .vote))
    (hnb : ∀ j < k, ¬ Frame.Bad (thread p L) (Ref p L w) X (g, j)) :
    LExpect p L g d (n .shfl) (n (.load .commit)) e ∧ Loader.Expect (d, lcn n) e := by
  have hev0 := (lfired hp hX he hσ).1
  have hev : Ev p L g w d e := by rw [← hbw]; exact hev0
  -- every shuffle receives a word, and a scan shuffle the source lane's value at its site
  have shfl : ∀ mode a b c recv ok, e.kind = .shfl mode a b c recv ok →
      (∃ x, recv = .bits 32 x) ∧ (d.site.epi.shfl = true →
        Epilogue.Expect p L g (toE d) (n .shfl - 32 * n (.load .commit)) e) := by
    intro mode a b c recv ok hk
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    have hsl := Step.shflSource_lt mode (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) b c
    obtain ⟨hsT, hsW, hsC, -, -⟩ := lane_facts hp hg hw hsl
    obtain ⟨j, pc', b', c', r', o', hj, hG, hcj⟩ := lshfl_src hp hX hg hw he hσ hF (IH rfl)
    refine ⟨sent_word hp hX hsW hj hG, fun hse => ?_⟩
    obtain ⟨b1, d1, n1, -, -, -, hF1, hE1, hs1, -⟩ :=
      role_at hp hX hj hG (.inr (.inr ⟨rfl, by have := lfits_three hF; omega⟩))
    obtain ⟨hsite, hns⟩ := lshfl_same hsC.symm hF hse hF1 ((lev_class hE1).1 rfl) (by omega)
    obtain ⟨hl1, hnd1⟩ := shfl_lc' (s := d1.site) (by rw [hsite]; exact hse)
    obtain ⟨dE, hFE, -, h1, -, -⟩ := lband hF1 hl1
    rw [h1 hnd1, hns] at hFE
    refine Epilogue.expect_shfl_of_src hp hg hw (ev_toE (shfl_scan hse) hev)
      ⟨toE d1, n1 .vote, hFE, by simp [toE, hsite], ?_⟩
    exact Epilogue.ev_opnd (ev_toE (by rw [hsite]; exact shfl_scan hse) hE1)
  have hsfits := fun (hs : d.site.sched = true) => (sched_fits hs hF).2.1
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case down sk | up sk _ | total sk | pre sk | tiles sk =>
    have hk : ∃ md a b c r ok, kind = .shfl md a b c r ok := by
      simp only [Ev, Epilogue.Ev, Site.toE] at hev
      obtain ⟨r, ok, h⟩ := hev
      exact ⟨_, _, _, _, _, _, h⟩
    obtain ⟨md, a, b, c, r, ok, rfl⟩ := hk
    obtain ⟨⟨x, rfl⟩, h2⟩ := shfl md a b c r ok rfl
    refine ⟨?_, by simp only [Loader.Expect, ret]; exact acc_shfl rfl⟩
    simp only [LExpect]
    intro _
    exact h2 rfl
  case xl | xh =>
    have hk : ∃ md a b c r ok, kind = .shfl md a b c r ok := by
      simp only [Ev] at hev
      obtain ⟨r, ok, h⟩ := hev
      exact ⟨_, _, _, _, _, _, h⟩
    obtain ⟨md, a, b, c, r, ok, rfl⟩ := hk
    obtain ⟨⟨x, rfl⟩, -⟩ := shfl md a b c r ok rfl
    exact ⟨by simp [LExpect, Site.sched, Site.scan],
      by simp only [Loader.Expect, ret]; exact acc_shfl rfl⟩
  case vote l =>
    refine ⟨?_, by simp only [Loader.Expect, ret]; exact RetKind.accepts_none _⟩
    simp only [LExpect]
    intro _
    have hE0 := ev_toE (by rfl) hev
    simp only [Epilogue.Ev, toE, Site.epi] at hE0
    obtain ⟨b, hb⟩ := hE0
    subst hb
    have hbits := lvote_bits hp hX hg hw rfl he hσ hF (IH isColl_vote)
    exact Epilogue.expect_vote_of_bits hp hg hw (by rfl) fun i hi => by
      obtain ⟨di, nvi, h1, h2, h3⟩ := hbits i hi
      exact ⟨toE di, nvi, h1, h2, h3⟩
  case word sk =>
    have hFE := hsfits rfl
    have hEx := Epilogue.expect_word hp hReads he (by rfl) hFE (ev_toE rfl hev)
    refine ⟨by simp only [LExpect]; intro _; exact hEx, ?_⟩
    simp only [Loader.Expect, ret]
    simp only [Ev, Epilogue.Ev, Site.toE] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Epilogue.Expect, toE, Site.epi] at hEx
      simp only [Epilogue.Fits, toE, Site.epi] at hFE
      obtain ⟨r, n0, v0, hP, hR, hns, -⟩ := hFE
      exact acc_rd rfl (hEx r n0 v0 hP hR hns)
    · exact acc_ub ⟨f, hk⟩
  case q0 | q1 =>
    have hFE := hsfits rfl
    have hEx := Epilogue.expect_q hp hReads he (by simp [toE, Site.epi]) hFE (ev_q (by simp) hev)
    refine ⟨by simp only [LExpect]; intro _; exact hEx, ?_⟩
    simp only [Loader.Expect, ret]
    simp only [Ev] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Epilogue.Expect, toE, Site.epi] at hEx
      exact acc_rd rfl hEx
    · exact acc_ub ⟨f, hk⟩
  case uk =>
    simp only [Ev] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    · subst hk
      have h := expect_uk (w := w) hp hX he rfl hF (by simp only [Ev]; exact .inl ⟨bs, rfl⟩) rfl
      exact ⟨by simp only [LExpect]; exact h, by simp only [Loader.Expect, ret]; exact acc_rd rfl h⟩
    · subst hk
      exact ⟨by simp [LExpect, Site.sched, Site.scan], acc_ub ⟨f, rfl⟩⟩
  case pgLd per it =>
    refine ⟨by simp [LExpect, Site.sched, Site.scan], ?_⟩
    exact pg_word hp hX he hσ hF rfl
  case ptP | ptR | lw =>
    refine ⟨by simp [LExpect, Site.sched, Site.scan], ?_⟩
    subst hbw
    exact local_word hp hX he hσ hJ hnb rfl
  all_goals exact ⟨by simp [LExpect, Site.sched, Site.scan],
    by simp only [Loader.Expect, ret]; exact RetKind.accepts_none _⟩

set_option maxHeartbeats 1000000 in
/-- **Every event of a lane of loader warp `w` at a state that holds `Ref` makes a good step**
once no lane of the warp is bad at an earlier collective position. -/
theorem step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X) (hw14 : w = 14 ∨ w = 15)
    (g k : Nat) (σ : (thread p L g).D) (e : Event)
    (hQ : InWarp L w g) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hR : Ref p L w g σ)
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → InWarp L w j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L w) X j) :
    Frame.StepGood (thread p L) (Ref p L w) g σ e := by
  obtain ⟨hg, hw⟩ := hQ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | b | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact start_step hp hX hg hw hw14 he hσ hR hprev
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim
  · refine role_step hp hX he hσ hR fun _ => ?_
    obtain ⟨hbw, hR'⟩ := hR
    obtain ⟨hJ, hF⟩ := hR' (ub_zero hX he hσ)
    obtain ⟨hcs, hcv⟩ := counts hσ
    exact lexpect hp hX hReads hg hw he hσ hbw hJ hF (fun hce => by
      have := upTo_of_prev (fun _ => ref_init) he hce hprev
      rwa [countColl ((X.tr g).take k), hcs, hcv] at this)
      fun j hj => hprev (g, j) (lex_lt hj) ⟨hg, hw⟩
  · exact hR.elim

/-- **Every lane of loader warp `w` is followed, and its states hold the reference invariant.** -/
theorem good (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw14 : w = 14 ∨ w = 15) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = w) (k : Nat) : Good p L w X g k :=
  Frame.followedOn (C := thread p L) (J := Ref p L w) (Q := InWarp L w)
    (Frame.inductive_lex (μ X)) (fun _ _ => ref_init)
    (step hp hX (cuQReadsFromLaunch hp hX) hw14) ⟨hg, hw⟩ k

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
