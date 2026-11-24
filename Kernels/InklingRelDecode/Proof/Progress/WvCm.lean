-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WvLane

@[expose] public section

/-!
# `CmLag`: the committing MMA lane lags a default-partition poller

A softmax thread at `waitS` of iteration `i` (`i < n`, `n` the CTA's `num_iters`) has made
`i / 2` successful polls of `s_ready (i % 2)`; at `waitO` (`1 ≤ i < n`) `i - 1` of `o_done`; an
epilogue thread at its `wait` none of `o_final` (`Rd.sm_cnt`, `Hs.epi_cnt`). The thread is at a
state after its last event, so it has not exited, its state has its invariant (`Frame.end_at`)
and it has made two barrier-1 events (`phase_inv`).

**The committing lane `cm`** (`Hs.cmOf`). If some lane of the CTA's MMA warp made an election
returning its own lane, `cm` is that lane and every election of `cm` returned its lane, so its
commits are the counts of its state (`Wv.mma_commits_le`): with no more commits than the
poller's polls, it is at an iteration up to the poller's (QK commits `qkDone`, PV commits
`oDoneC`), or before its `o_final` commit (`finDone`), and the slot schedule puts it earlier.
Otherwise no lane of the MMA warp has made any election: an election of a lane has a partner of
every lane of its mask (`ElectOrd.partner`, the needs of an election in the dependency order),
of the same leader, so the leader's lane would have made one returning its lane. Then `cm` is
lane 0 of the warp and has made no election, so it is before its role's first election (`PreE`,
`elect_of`), at most at the election of iteration 0, or at the end of a loop that does not run
(only possible when the CTA has no iteration, `fin0`, so not under a softmax poller).

In both cases `cm` is not at a later-round or exit state and has not exited (`noLate`,
`noExit_peer`: it would have a third barrier-1 event of a passed generation, of which the poller
is a member), and its states before its role are before the loop.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The MMA machine's counts by site class -/

theorem site_cases (s : Mma.Site) : Mma.PreSite s ∨ Mma.QkSite s ∨ Mma.PvSite s ∨ FinSite s := by
  cases s <;> simp [Mma.PreSite, Mma.QkSite, Mma.PvSite, FinSite]

theorem cnt_qk {d : Mma.D} (hI : Mma.Inv d) (h : Mma.QkSite d.site) :
    d.i ≤ SO.Mm.qkDone d ∧ d.i - 1 ≤ SO.Mm.oDoneC d ∧ SO.Mm.finDone d = 0 := by
  have hq := hI.qk h
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp_all [Mma.QkSite, SO.Mm.qkDone, SO.Mm.oDoneC, SO.Mm.finDone]

theorem cnt_pv {d : Mma.D} (h : Mma.PvSite d.site) :
    min (d.i + 1) d.n ≤ SO.Mm.qkDone d ∧ d.i - 1 ≤ SO.Mm.oDoneC d ∧ SO.Mm.finDone d = 0 := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp_all [Mma.PvSite, SO.Mm.qkDone, SO.Mm.oDoneC, SO.Mm.finDone]

theorem cnt_fin {d : Mma.D} (h : FinSite d.site) :
    SO.Mm.qkDone d = (if d.i = 0 then 0 else d.n) ∧
      SO.Mm.oDoneC d = (if d.i = 0 then 0 else d.n) ∧
      (SO.Mm.finDone d = 0 → d.site = .finBar ∨ d.site = .finElect ∨ d.site = .finCommit) := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  unfold FinSite at h
  simp only at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    simp [SO.Mm.qkDone, SO.Mm.oDoneC, SO.Mm.finDone]

theorem mmaT_pre {d : Mma.D} (h : Mma.PreSite d.site) : mmaT d ≤ c1 := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp only [Mma.PreSite] at h <;> simp only [mmaT] <;> wt_omega

theorem mmaT_fin {d : Mma.D} (h : d.site = .finBar ∨ d.site = .finElect ∨ d.site = .finCommit) :
    mmaT d ≤ epi0 - 92 := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  simp only at h
  rcases h with rfl | rfl | rfl <;> simp only [mmaT] <;> wt_omega

/-- A loop state of iteration at most `2 ^ 32` is before the epilogue. -/
theorem mmaT_loop_epi {d : Mma.D} (h : Mma.QkSite d.site ∨ Mma.PvSite d.site)
    (hi : d.i ≤ 2 ^ 32) : mmaT d + 1 < epi0 := by
  have h1 := mmaT_loop_le d h
  have h2 := slot_le_slot hi
  unfold slot at h2
  unfold slot bandM at h1
  unfold epi0 loop0 span at *
  omega

/-! ### The MMA lane's state against the poll -/

/-- `below2 b x ≤ i / 2` with `b = i % 2` means `x ≤ i`. -/
theorem le_of_below2 {x i : Nat} (h : below2 (i % 2) x ≤ i / 2) : x ≤ i := by
  by_contra hx
  have := below2_mono (b := i % 2) (show i + 1 ≤ x by omega)
  unfold below2 at this h
  omega

/-- **Against `waitS` of iteration `i`.** -/
theorem lt_waitS {d : Mma.D} (hI : Mma.Inv d) {i N : Nat} (hiN : i < N)
    (hN : N ≤ 2147483646) (hn : d.site ≠ .setMaxReg → d.site ≠ .ldNum → d.n = N)
    (hfin : FinSite d.site → 1 ≤ d.n → d.n ≤ 2147483646 → d.i = d.n + 1)
    (hc : d.site ≠ .setMaxReg → below2 (i % 2) (SO.Mm.qkDone d) ≤ i / 2) :
    mmaT d + 1 < slot i + bandS := by
  have hs0 := slot_le_slot (Nat.zero_le i)
  rcases site_cases d.site with h | h | h | h
  · have := mmaT_pre h
    unfold slot at hs0
    unfold slot bandS at *
    wt_omega
  · have hne : d.site ≠ .setMaxReg := fun h' => by rw [h'] at h; exact h
    have hx := le_of_below2 (hc hne)
    replace hx := le_trans (cnt_qk hI h).1 hx
    have h1 := mmaT_loop_le d (.inl h)
    have h2 := slot_le_slot hx
    unfold bandM bandS at *
    omega
  · have hne : d.site ≠ .setMaxReg := fun h' => by rw [h'] at h; exact h
    have hne2 : d.site ≠ .ldNum := fun h' => by rw [h'] at h; exact h
    have hx := le_of_below2 (hc hne)
    replace hx := le_trans (cnt_pv h).1 hx
    rw [hn hne hne2] at hx
    have hp := hI.pv h
    rw [hn hne hne2] at hp
    have hdi : d.i ≤ i := by
      rcases Nat.le_total (d.i + 1) N with h' | h'
      · rw [Nat.min_eq_left h'] at hx; omega
      · rw [Nat.min_eq_right h'] at hx; omega
    have h1 := mmaT_loop_le d (.inr h)
    have h2 := slot_le_slot hdi
    unfold bandM bandS at *
    omega
  · exfalso
    have hne : d.site ≠ .setMaxReg := fun h' => by
      rw [h'] at h; unfold FinSite at h; rcases h with h | h | h | h | h <;> cases h
    have hne2 : d.site ≠ .ldNum := fun h' => by
      rw [h'] at h; unfold FinSite at h; rcases h with h | h | h | h | h <;> cases h
    have hdn := hn hne hne2
    have hx := le_of_below2 (hc hne)
    have hi := hfin h (by omega) (by omega)
    rw [(cnt_fin h).1] at hx
    split at hx <;> omega

/-- **Against `waitO` of iteration `i`.** -/
theorem lt_waitO {d : Mma.D} (hI : Mma.Inv d) {i N : Nat} (hi1 : 1 ≤ i) (hiN : i < N)
    (hN : N ≤ 2147483646) (hn : d.site ≠ .setMaxReg → d.site ≠ .ldNum → d.n = N)
    (hfin : FinSite d.site → 1 ≤ d.n → d.n ≤ 2147483646 → d.i = d.n + 1)
    (hc : d.site ≠ .setMaxReg → SO.Mm.oDoneC d ≤ i - 1) :
    mmaT d + 1 < slot i + bandS := by
  have hs0 := slot_le_slot (Nat.zero_le i)
  rcases site_cases d.site with h | h | h | h
  · have := mmaT_pre h
    unfold slot at hs0
    unfold slot bandS at *
    wt_omega
  · have hne : d.site ≠ .setMaxReg := fun h' => by rw [h'] at h; exact h
    have hx := hc hne
    replace hx := le_trans (cnt_qk hI h).2.1 hx
    have h1 := mmaT_loop_le d (.inl h)
    have h2 := slot_le_slot (show d.i ≤ i by omega)
    unfold bandM bandS at *
    omega
  · have hne : d.site ≠ .setMaxReg := fun h' => by rw [h'] at h; exact h
    have hx := hc hne
    replace hx := le_trans (cnt_pv h).2.1 hx
    have h1 := mmaT_loop_le d (.inr h)
    have h2 := slot_le_slot (show d.i ≤ i by omega)
    unfold bandM bandS at *
    omega
  · exfalso
    have hne : d.site ≠ .setMaxReg := fun h' => by
      rw [h'] at h; unfold FinSite at h; rcases h with h | h | h | h | h <;> cases h
    have hne2 : d.site ≠ .ldNum := fun h' => by
      rw [h'] at h; unfold FinSite at h; rcases h with h | h | h | h | h <;> cases h
    have hdn := hn hne hne2
    have hx := hc hne
    have hi := hfin h (by omega) (by omega)
    rw [(cnt_fin h).2.1] at hx
    split at hx <;> omega

/-- **Against the epilogue's `wait`.** -/
theorem lt_epi {d : Mma.D} (hI : Mma.Inv d) (hc : d.site ≠ .setMaxReg → SO.Mm.finDone d = 0) :
    mmaT d + 1 < epi0 := by
  rcases site_cases d.site with h | h | h | h
  · have := mmaT_pre h
    wt_omega
  · exact mmaT_loop_epi (.inl h) (by have := hI.qk h; have := hI.n; omega)
  · exact mmaT_loop_epi (.inr h) (by have := hI.pv h; have := hI.n; omega)
  · have hne : d.site ≠ .setMaxReg := fun h' => by
      rw [h'] at h; unfold FinSite at h; rcases h with h | h | h | h | h <;> cases h
    have := mmaT_fin ((cnt_fin h).2.2 (hc hne))
    wt_omega

/-- **A state before the first election against a softmax poll of iteration `i`.** -/
theorem preE_lt_sm {d : Mma.D} (h : PreE d) {i N : Nat} (hN1 : 1 ≤ N) (hN : N ≤ 2147483646)
    (hn : d.site ≠ .setMaxReg → d.site ≠ .ldNum → d.n = N)
    (h0 : (d.site = .finBar ∨ d.site = .finElect) → d.i = 0 → d.n = 0 ∨ 2147483646 < d.n) :
    mmaT d + 1 < slot i + bandS := by
  have hs0 := slot_le_slot (Nat.zero_le i)
  rcases h with h | ⟨hi, h⟩
  · have := mmaT_pre h
    unfold slot at hs0
    unfold slot bandS at *
    wt_omega
  · rcases h with h | h | h | h | h | h | h
    all_goals first
      | (have hq : Mma.QkSite d.site := by rw [h]; trivial
         have h1 := mmaT_loop_le d (.inl hq)
         rw [hi] at h1
         unfold bandM bandS at *
         omega)
      | (exfalso
         have hne : d.site ≠ .setMaxReg := by rw [h]; nofun
         have hne2 : d.site ≠ .ldNum := by rw [h]; nofun
         have := h0 (by simp [h]) hi
         have := hn hne hne2
         omega)

/-- **A state before the first election against the epilogue's poll.** -/
theorem preE_lt_epi {d : Mma.D} (h : PreE d) : mmaT d + 1 < epi0 := by
  rcases h with h | ⟨hi, h⟩
  · have := mmaT_pre h
    wt_omega
  · rcases h with h | h | h | h | h | h | h
    all_goals first
      | (have hq : Mma.QkSite d.site := by rw [h]; trivial
         exact mmaT_loop_epi (.inl hq) (by omega))
      | (have := mmaT_fin (d := d) (by simp [h])
         wt_omega)

/-! ### The lag of a lane of the MMA warp -/

/-- A worker state of the first round is before the loop. -/
theorem workerT_early (w : Worker.D) (h : ¬ Worker.late w.P) : workerT w ≤ c0 + 4 := by
  obtain ⟨s, P⟩ := w
  cases s <;> simp only [workerT, h, ite_false] <;> wt_omega

/-- **A lane of the CTA's MMA warp lags a poller** when each of its MMA states is before the
poller's time `T0`. -/
theorem lags_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hub : ¬ HasUb X) {g y : Nat}
    {s : DComp.St} {T0 : Nat} (hT0 : T0 ≤ dcompT s) (hc0 : c0 + 6 < T0)
    (hnxg : ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) (hgb : b1N X g (X.tr g).length ≤ 2)
    (hy : Hs.MmaOf L (g / L.block) y)
    (hm : ∀ ky d P, ky ≤ (X.tr y).length → St Q L X y ky = some (some (.w (.mma d P))) →
      Mma.Inv d → mmaT d + 1 < T0) :
    Wy.Lags Wt.time Q L X y g (.d s) := by
  obtain ⟨hyl, hyc, hyw⟩ := hy
  have hb : L.block = 256 := hpre.block
  have hyd : ¬ y % L.block < 128 := by omega
  have hc : g / L.block = y / L.block := hyc.symm
  have hnxy := noExit_peer hpre hX hf hR hc hyd hnxg hgb
  refine ⟨hnxy, ?_⟩
  have key : ∀ ky σ, ky ≤ (X.tr y).length → St Q L X y ky = some (some σ) →
      (threadCode L y Q).inv σ → Wt.time y σ + 1 < T0 := by
    intro ky σ hk hσ hinv
    have hnl := noLate hpre hX hf.sound hR hc hk hnxg hgb hσ
    have hrw := roleWarp_inv hf.roleWarp _ _ hk hσ
    cases σ with
    | d s' => exact absurd ((cls_inv ky _ hk hσ).mp trivial) hyd
    | w s' =>
      cases s' with
      | worker w =>
        have := workerT_early w hnl
        show workerT w + 1 < T0
        omega
      | idle d =>
        simp only [RoleWarp, roleWarp] at hrw
        omega
      | loader d P =>
        simp only [RoleWarp, roleWarp] at hrw
        omega
      | mma d P => exact hm ky d P hk hσ hinv.2.1
      | exit x => exact absurd trivial hnl
  show Sched.threadTime (timed Wt.time Q L) X y < dcompT s
  rcases Wu.end_cases hX hf.sound hf.tracked hub hyl hnxy with
    ⟨σ, hσy, hinv⟩ | ⟨σ, e1, hpos, hσy, hnone, hinv, he1⟩
  · rw [threadTime_eq hσy]
    have := key _ σ le_rfl hσy hinv
    omega
  · rw [threadTime_stop hσy hnone]
    have := key _ σ (Nat.sub_le _ _) hσy hinv
    omega

/-! ### The poller -/

/-- **The facts of a default-partition poller at the end of its trace**: it has not exited, has
made two barrier-1 events, and its state has its invariant. -/
theorem poller_end (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hub : ¬ HasUb X) {g : Nat}
    (hg : g < L.threads) {s : DComp.St}
    (hσ : St Q L X g (X.tr g).length = some (some (.d s))) (hph : (dPh s).2 = 2) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧ b1N X g (X.tr g).length ≤ 2 ∧
      (threadCode L g Q).inv (.d s) := by
  have hnx := noExit_of_end hX hf hσ
  obtain ⟨-, t, -, hb1, h3, -, -, -⟩ := phase_inv hpre hX hf.sound hR _ _ le_rfl hσ
  have ht : t = 0 := h3 rfl
  obtain ⟨tt, hr⟩ := Frame.run_some hX hub (pending_of_noExit hX hg hnx)
  have hσ' : Frame.stateAt (code L Q) X g (X.tr g).length = some (some (.d s)) := hσ
  obtain ⟨-, -, -, -, hinv, -⟩ := Frame.end_at hf.sound hg hr hσ'
  refine ⟨hnx, ?_, hinv⟩
  rw [hb1, ht]
  exact Nat.le_of_eq (by simpa [tPh] using hph)

/-- The iteration of a softmax state at a late site, with its invariant, is below the CTA's
`num_iters`. -/
theorem sm_iter_lt (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X) {g k : Nat}
    (hg : g < L.threads) {d : Sm.D} (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hI : Sm.Inv L g d) (hl : Sm.LateSite d.site) :
    d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
  have hm := ((hf.reach hg hσ).2 : SmMeans Q L g d.e)
  have hr25 := hm.ent.r25
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
  have hn31 := numIters_lt31 hpre hz (ProA.cta L g .x)
  have hr26 : d.e.r26 = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    have h1 := hI.ok.r26
    rw [hr25] at h1
    rw [h1]
    simp only [hn31, ↓reduceIte]
  have := (hI.late hl).2.2
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
