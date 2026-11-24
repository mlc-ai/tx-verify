-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WvParity
public import Kernels.InklingRelDecode.Proof.Progress.WxAll
public import Kernels.InklingRelDecode.Proof.Interface.WvArr

@[expose] public section

/-!
# `P0Lag`: thread 0 lags an MMA lane at its poll of `p_ready`

An MMA lane at `pWait` of iteration `i` (`1 ≤ i ≤ n`, `n` the CTA's `num_iters`) polls
`p_ready b`, `b = (i - 1) % 2`, after `(i - 1) / 2 = below2 b (i - 1)` successful polls of it
(`Wv.mma_polls_le`). If thread 0 has made at most that many arrivals on it, then:

* it is not in the epilogue, where it has made `below2 b n ≥ below2 b i` (`Wv.arr_epi`), so it
  has not exited (its exit is an epilogue state);
* at a softmax state of iteration `i'` it has made `below2 b i'` (`Rr.arr_cnt`), so `i' < i`, and
  every softmax state of iteration `i' < i` is timed before slot `i`, whose MMA band holds the
  lane's state (`Wt.smT_loop_band`, `Wt.mmaT_band`); the setup, the prologue and the common start
  are before every slot.

Its time, one more if it stopped at its last event (`Wu.end_cases`), is below the lane's.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX.Kernels.InklingRelDecode.Proof.EvW (pReady)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- `below2 b` is monotone. -/
theorem below2_mono {b x y : Nat} (h : x ≤ y) : below2 b x ≤ below2 b y := by
  unfold below2
  omega

/-- **Thread 0 of the CTA is before the MMA lane's `pWait` of iteration `i`** at any of its
states where it has made no more arrivals on `p_ready ((i - 1) % 2)` than `(i - 1) / 2`. -/
theorem p0_before (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {y : Nat} (hy : y < L.threads) (hy0 : y % L.block = 0)
    {i : Nat} (hi : 1 ≤ i) (hiN : i ≤ Q.numIters (ProA.cta L y .z) (ProA.cta L y .x))
    (hA : arrivals (pReady L (y / L.block) ((i - 1) % 2)) (X.tr y) ≤ (i - 1) / 2)
    {k : Nat} (hk : k ≤ (X.tr y).length) {s : DComp.St}
    (hσ : St Q L X y k = some (some (.d s))) : dcompT s < slot i := by
  have hb : (i - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hbi : below2 ((i - 1) % 2) i = (i - 1) / 2 + 1 := by unfold below2; omega
  have hsub : arrivals (pReady L (y / L.block) ((i - 1) % 2)) ((X.tr y).take k) ≤
      arrivals (pReady L (y / L.block) ((i - 1) % 2)) (X.tr y) :=
    (List.take_sublist _ _).countP_le
  have hs0 := slot_le_slot (show 0 ≤ i from Nat.zero_le _)
  cases s with
  | dstart d0 =>
    have := dstartT_le d0
    simp only [dcompT]
    wt_omega
  | pro p =>
    have := Wx.pro_idx_le p.site
    simp only [dcompT, proT]
    wt_omega
  | sm d' =>
    by_cases hset : d'.site = .setMaxReg ∨ d'.site = .bar0 ∨ ∃ j, d'.site = .pre j
    · have := smT_setup_lt d' hset
      simp only [dcompT]
      wt_omega
    · have h1 : ∀ j, d'.site ≠ .pre j := fun j h => hset (.inr (.inr ⟨j, h⟩))
      have h2 : d'.site ≠ .setMaxReg := fun h => hset (.inl h)
      have h3 : d'.site ≠ .bar0 := fun h => hset (.inr (.inl h))
      have hband := smT_loop_band d' h1 h2 h3
      have hc := (Rr.arr_cnt hpre hX hf hy hy0 k hk _ hσ).2 d' rfl _ hb
      have hlt : d'.i < i := by
        by_contra hge
        have := below2_mono (b := (i - 1) % 2) (show i ≤ d'.i by omega)
        omega
      have := slot_lt_slot hlt
      simp only [dcompT]
      unfold span at this hband
      omega
  | epi d' =>
    exfalso
    have h := Proof.Wv.arr_epi hpre hX hf hy hy0 (by omega) hk hσ _ hb
    have := below2_mono (b := (i - 1) % 2) hiN
    omega

/-- **`Wy.P0Lag`** for `Wt.time`. -/
theorem p0Lag_of (hpre : Pre Q L mem0)
    (hF : ∀ X, Consistent L kernel asms mem0 X → ThreadFacts Q L mem0 X)
    (hR : ∀ X, Consistent L kernel asms mem0 X → RoleReads L X)
    (hB : ∀ X, Consistent L kernel asms mem0 X → BaseWordRead L X)
    (hN : ∀ X, Consistent L kernel asms mem0 X → NumWordRead Q L X) :
    Wy.P0Lag Wt.time Q L mem0 := by
  intro X g d P m par hX hub hg hσ hs hat hle
  have hf := hF X hX
  rcases hat with ⟨hs', -, -⟩ | ⟨-, rfl, rfl⟩
  · rw [hs] at hs'; cases hs'
  have hsr : d.site ≠ .setMaxReg := by rw [hs]; nofun
  obtain ⟨hp, -⟩ := Proof.Wv.mma_polls_le hpre hX hf (hR X hX) le_rfl hσ hsr
  rw [List.take_length] at hp
  have hb : (d.i - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  rw [hp _ hb] at hle
  have h1 : SO.Mm.pPolled d = d.i - 1 := by simp [SO.Mm.pPolled, hs]
  rw [h1, SO.below2_of_buf hb rfl] at hle
  obtain ⟨hi1, hin⟩ := Proof.Wv.mma_pWait_iter hX hf le_rfl hσ hs
  have hw := (words_inv hpre hX hf (hB X hX) (hN X hX) _ _ hσ).2.2 hsr (by rw [hs]; nofun)
  -- thread 0
  have hb256 : L.block = 256 := hpre.block
  have hgrid : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  obtain ⟨hy, hyc, -⟩ := Hs.p0_soft hpre hgrid
  have hy0 : Hs.p0Of L (g / L.block) % L.block = 0 := by
    unfold Hs.p0Of
    exact Nat.mul_mod_left _ _
  have hcta : ∀ a, ProA.cta L (Hs.p0Of L (g / L.block)) a = ProA.cta L g a :=
    fun a => ProA.cta_eq_of_block hyc a
  have hiN : d.i ≤ Q.numIters (ProA.cta L (Hs.p0Of L (g / L.block)) .z)
      (ProA.cta L (Hs.p0Of L (g / L.block)) .x) := by
    rw [hcta, hcta, ← hw.1]
    exact hin
  have hA : arrivals (pReady L (Hs.p0Of L (g / L.block) / L.block) ((d.i - 1) % 2))
      (X.tr (Hs.p0Of L (g / L.block))) ≤ (d.i - 1) / 2 := by
    rw [hyc]
    exact hle
  have hmT : slot d.i + bandM ≤ mmaT d := (mmaT_band d (.inr (by rw [hs]; trivial))).1
  have hbef := fun {k} {s} hk hσ' =>
    p0_before hpre hX hf hy hy0 hi1 hiN hA (k := k) (s := s) hk hσ'
  -- not exited
  have hnx : ∀ j pc, X.get (Hs.p0Of L (g / L.block), j) ≠ some ⟨pc, .exit⟩ := by
    intro j pc hj
    have hj' : j ≤ (X.tr (Hs.p0Of L (g / L.block))).length :=
      (List.getElem?_eq_some_iff.mp (show (X.tr _)[j]? = _ from hj)).1.le
    rcases exit_event_state hX hf.sound hf.tracked hj with ⟨de, hσ', -⟩ | ⟨x, hσ', -⟩
    · exfalso
      have h := Proof.Wv.arr_epi hpre hX hf hy hy0 (by omega) hj' hσ' _ hb
      have hsub : arrivals (pReady L (Hs.p0Of L (g / L.block) / L.block) ((d.i - 1) % 2))
          ((X.tr (Hs.p0Of L (g / L.block))).take j) ≤
          arrivals (pReady L (Hs.p0Of L (g / L.block) / L.block) ((d.i - 1) % 2))
            (X.tr (Hs.p0Of L (g / L.block))) :=
        (List.take_sublist _ _).countP_le
      have := below2_mono (b := (d.i - 1) % 2) hiN
      have hbi : below2 ((d.i - 1) % 2) d.i = (d.i - 1) / 2 + 1 := by unfold below2; omega
      omega
    · obtain ⟨s', hs'⟩ := B0N.dstate_of hj' hσ' (by omega)
      cases hs'
  refine ⟨hnx, ?_⟩
  show Sched.threadTime (timed Wt.time Q L) X _ < mmaT d
  rcases Wu.end_cases hX hf.sound hf.tracked hub hy hnx with
    ⟨σ, hσy, -⟩ | ⟨σ, e1, hpos, hσy, hnone, -, he1⟩
  · obtain ⟨sy, rfl⟩ := B0N.dstate_of le_rfl hσy (by omega)
    rw [threadTime_eq hσy]
    have := hbef le_rfl hσy
    show dcompT sy < mmaT d
    unfold bandM at hmT
    omega
  · obtain ⟨sy, rfl⟩ := B0N.dstate_of (Nat.sub_le _ _) hσy (by omega)
    rw [threadTime_stop hσy hnone]
    have := hbef (Nat.sub_le _ _) hσy
    show dcompT sy + 1 < mmaT d
    unfold bandM at hmT
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
