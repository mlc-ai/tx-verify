-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WxTcOrder
public import Kernels.InklingRelDecode.Proof.Progress.WxLag0
public import Kernels.InklingRelDecode.Proof.Progress.WtMono

@[expose] public section

/-!
# `TcWaitFacts.lag`: a lane of the warp with no more `tcgen05` collectives is no later

The statement (`Assemble.TcLag`): thread `g` makes its `k`-th warp-collective `tcgen05` event from
its state `d`; a lane `h` of its warp has made at most `k` events of the class. Then
`threadTime h ≤ time d`.

Only default-partition threads make events of the class (`Lk.tcSt`), so `g` and `h` are default
threads of one warp: one CTA (one decision table, one `num_iters`) and one `w0`. When the CTA's
lazy-rescale decisions agree (`Lk.DecAgree`), the count before a state is
`tcF s + 4 Rval` (`tc_inv`, `B0N.rinv_all`), a function of the state and the warp; `WxTcOrder.lean`
orders the states of each region by it, and the regions are in time order (the common start, the
prologue, the softmax region, the epilogue). `h` is at a state now, or stopped at its last event
(`Wu.end_cases`); an exited `h` would have more events than `g` (`tc_cmp` at its exit state).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Interface.B0N
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem dsTc_congr {g h : Nat} (hw : w0 L h = w0 L g) (s : DStart.Site) :
    dsTc L h s = dsTc L g s := by
  cases s <;> simp [dsTc, hw]

theorem tcF_congr {g h : Nat} (hw : w0 L h = w0 L g) (hn : Lk.NI Q L h = Lk.NI Q L g) :
    tcF Q L h = tcF Q L g := by
  funext s
  cases s <;> simp [tcF, dsTc_congr hw, hw, hn]

/-- **The comparison of a lane's state with a `tcgen05` state of its warp.** `c` is `0`, or the
lane's own event of the class (then the comparison is strict). -/
theorem tc_cmp (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hD : ∀ c j, DecAgree Q L X c j) {g h j ky c : Nat}
    {ev : Event} {s sy : DComp.St} (hg : g < L.threads) (hh : h < L.threads)
    (hcta : h / L.block = g / L.block) (hw : w0 L h = w0 L g) (hgd : g % L.block < 128)
    (hhd : h % L.block < 128) (hev : X.get (g, j) = some ev)
    (hσ : St Q L X g j = some (some (.d s))) (ht : Lk.dTc s = true)
    (hky : ky ≤ (X.tr h).length) (hσy : St Q L X h ky = some (some (.d sy)))
    (hinvy : ∀ m1, sy = .sm m1 → Sm.Inv L h m1) (hc : c = 0 ∨ c = bit (Lk.dTc sy))
    (hle : Lk.cnt isTcColl X h ky + c ≤ Lk.cnt isTcColl X g j) :
    dcompT sy ≤ dcompT s ∧ (c = bit (Lk.dTc sy) → dcompT sy < dcompT s) := by
  have hj : j ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp hev).1.le
  have hN : nIt Q L h = nIt Q L g := by
    simp only [nIt, ProA.cta_eq_of_block hcta .z, ProA.cta_eq_of_block hcta .x]
  have hNI : Lk.NI Q L h = Lk.NI Q L g := hN
  have hDc : Dc Q L X (h / L.block) = Dc Q L X (g / L.block) := by rw [hcta]
  obtain ⟨Cg, Sg⟩ := tc_inv hpre hX hf hg j hj hσ
  obtain ⟨Jg, Rg⟩ := rinv_all hpre hX hf hg hgd (hD _) j hj s hσ
  have Kg := (Lk.cnt_inv hpre hX hf hg j hj hσ).2
  obtain ⟨Ch, -⟩ := tc_inv hpre hX hf hh ky hky hσy
  obtain ⟨Jh, Rh⟩ := rinv_all hpre hX hf hh hhd (hD _) ky hky sy hσy
  have Kh := (Lk.cnt_inv hpre hX hf hh ky hky hσy).2
  rw [tcF_congr hw hNI] at Ch
  rw [hDc] at Jh Rh
  rw [hN] at Rh
  rw [Cg, Rg] at hle
  rw [Ch, Rh] at hle
  have hc1 : c ≤ 1 := by
    rcases hc with rfl | rfl
    · omega
    · unfold bit; split <;> omega
  -- the barrier state is earlier than the epilogue
  have epi_hi : ∀ e1 : Epi.D, dcompT s < dcompT (.epi e1) ∨ ∃ me, s = .epi me := by
    intro e1
    cases s with
    | dstart d0 =>
      left; have := dstartT_le d0
      simp only [dcompT, epiT]; wt_omega
    | pro d0 => exact absurd ht (by simp [Lk.dTc])
    | sm m =>
      left
      have hI := Sv.sm_inv_at hX hf hev hσ
      have := smT_lt_epi0 hI
      simp only [dcompT, epiT]; omega
    | epi me => exact .inr ⟨me, rfl⟩
  cases s with
  | pro d0 => exact absurd ht (by simp [Lk.dTc])
  | dstart ds =>
    have hg32 : g % L.block < 32 := Sg (by
      simp only [dTc_ds, dsTcB, decide_eq_true_eq] at ht; exact ht)
    have hw1 : w0 L g = 1 := by simp [w0, hg32]
    have hdg : dsTc L g ds.site ≤ 1 := by
      simp only [dTc_ds, dsTcB, decide_eq_true_eq] at ht
      rcases ht with h1 | h1 <;> simp [dsTc, h1, hw1]
    have hR0 : ∀ x, Rval (Dc Q L X (g / L.block)) (nIt Q L g) (DComp.St.dstart x) = 0 :=
      fun _ => rfl
    have hT0 : ∀ x, tcF Q L g (.dstart x) = dsTc L g x.site := fun _ => rfl
    simp only [hR0, hT0] at hle
    cases sy with
    | dstart d1 =>
      simp only [hR0, hT0] at hle
      exact ds_tc_cmp (d1 := d1) hg32 ht hc (by omega)
    | pro d1 => exfalso; simp only [tcF] at hle; omega
    | sm d1 => exfalso; simp only [tcF] at hle; omega
    | epi d1 => exfalso; simp only [tcF] at hle; omega
  | sm m =>
    have hI := Sv.sm_inv_at hX hf hev hσ
    have hlt : m.i < nIt Q L g := by
      have := (hI.late (tc_late ht)).2.2
      rw [r26_numIters hpre hX hf hg hev hσ] at this
      simpa [nIt] using this
    have hloop := smT_loop (tc_loop ht)
    cases sy with
    | dstart d1 =>
      have := dstartT_le d1
      have := smT_setup (d := { m with site := .bar0 }) rfl
      simp only [dcompT, hloop]
      constructor <;> (try intro) <;> wt_omega
    | pro d1 =>
      have := pro_idx_le d1.site
      simp only [dcompT, proT, hloop]
      constructor <;> (try intro) <;> wt_omega
    | sm d1 =>
      simp only [Rval, tcF, JSx] at hle Jg Jh
      exact sm_tc_cmp Jh Jg ht hc (by simp only [dTc_sm] at hc; omega)
    | epi d1 =>
      exfalso
      simp only [Rval, tcF] at hle
      have h1 := rd_le (Dc Q L X (g / L.block)) m
      have h2 := nResc_mono (Dc Q L X (g / L.block)) (show m.i + 1 ≤ nIt Q L g by omega)
      have h3 := smO_tc m.site ht
      have : Lk.NI Q L g = nIt Q L g := rfl
      omega
  | epi me =>
    cases sy with
    | epi d1 =>
      simp only [Rval, tcF] at hle
      have hsk1 : d1.sk = Lk.skC Q L h := Kh.2
      have hsk : me.sk = Lk.skC Q L g := Kg.2
      have hskC : Lk.skC Q L h = Lk.skC Q L g := by simp only [Lk.skC, hNI]
      have hw' : me.site = .dealloc → w0 L g = 1 := fun h1 => by simp [w0, Sg h1]
      exact epi_tc_cmp (by rw [hsk1, hsk, hskC]) Kh.1 Kg.1 ht hw' hc (by omega)
    | sm d1 =>
      have := smT_lt_epi0 (hinvy d1 rfl)
      simp only [dcompT, epiT]
      constructor <;> (try intro) <;> omega
    | pro d1 =>
      have := pro_idx_le d1.site
      simp only [dcompT, epiT, proT]
      constructor <;> (try intro) <;> wt_omega
    | dstart d1 =>
      have := dstartT_le d1
      simp only [dcompT, epiT]
      constructor <;> (try intro) <;> wt_omega

/-- **`TcWaitFacts.lag`** (`Assemble.TcLag` for `Wt.time`), when the lazy-rescale decisions of
every CTA agree and the execution has no undefined behaviour. -/
theorem tcLag_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hub : ¬ HasUb X) (hD : ∀ c j, DecAgree Q L X c j)
    {g h j k : Nat} {d : TSt} (hg : g < L.threads) (hh : h < L.threads) (hsw : SameWarp L g h)
    (hK : X.TcK (g, j) k) (hσ : St Q L X g j = some (some d))
    (hle : (X.tr h).countP isTcColl ≤ k) :
    Sched.threadTime (timed Wt.time Q L) X h ≤ Wt.time g d := by
  obtain ⟨⟨ev, hev, htc⟩, hk⟩ := hK
  have hev' : X.get (g, j) = some ev := hev
  have hj : j ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp hev).1.le
  have hst := Lk.isTcColl_state hpre hX hf hg hev' hσ
  rw [htc] at hst
  obtain ⟨s, rfl⟩ : ∃ s, d = .d s := by
    cases d with
    | d s => exact ⟨s, rfl⟩
    | w s => simp [Lk.tcSt] at hst
  have ht : Lk.dTc s = true := hst.symm
  have hgd : g % L.block < 128 := (cls_inv j _ hj hσ).mp trivial
  obtain ⟨⟨-, -, hcta⟩, hwarp⟩ := hsw
  have hhd : h % L.block < 128 := by omega
  have hw : w0 L h = w0 L g := by
    simp only [w0]
    by_cases h1 : g % L.block < 32
    · simp [h1, show h % L.block < 32 by omega]
    · simp [h1, show ¬ h % L.block < 32 by omega]
  have hcnt : Lk.cnt isTcColl X g j = k := hk
  have hall : (X.tr h).countP isTcColl = Lk.cnt isTcColl X h (X.tr h).length := by
    unfold Lk.cnt; rw [List.take_length]
  have hle' : Lk.cnt isTcColl X h (X.tr h).length ≤ Lk.cnt isTcColl X g j := by
    rw [hcnt, ← hall]; exact hle
  have hinv_of : ∀ {k' : Nat} {e' : Event} {m1 : Sm.D}, X.get (h, k') = some e' →
      St Q L X h k' = some (some (.d (.sm m1))) → Sm.Inv L h m1 :=
    fun he' hσ' => Sv.sm_inv_at hX hf he' hσ'
  -- `h` has not exited
  have hnx : ∀ jx pc', X.get (h, jx) ≠ some ⟨pc', .exit⟩ := by
    intro jx pc' hjx
    have hjx' : jx ≤ (X.tr h).length :=
      (List.getElem?_eq_some_iff.mp (show (X.tr h)[jx]? = _ from hjx)).1.le
    rcases exit_event_state hX hf.sound hf.tracked hjx with ⟨de, hσ', hx⟩ | ⟨x, hσ', -⟩
    · have h2 : Lk.cnt isTcColl X h jx ≤ Lk.cnt isTcColl X h (X.tr h).length :=
        (List.take_sublist_take_left hjx').countP_le
      obtain ⟨h3, -⟩ := tc_cmp (c := 0) hpre hX hf hD hg hh hcta.symm hw hgd hhd hev' hσ ht
        hjx' hσ' (fun _ h => by cases h) (.inl rfl) (by omega)
      cases s with
      | pro d0 => simp [Lk.dTc] at ht
      | dstart d0 =>
        have := dstartT_le d0
        simp only [dcompT, epiT] at h3; wt_omega
      | sm m =>
        have := smT_lt_epi0 (Sv.sm_inv_at hX hf hev' hσ)
        simp only [dcompT, epiT] at h3; omega
      | epi me =>
        simp only [dcompT, epiT, Bound.Epi.siteRank, hx] at h3
        simp only [dTc_epi, epTc, decide_eq_true_eq] at ht
        rcases ht with h1 | h1 | h1 <;> simp only [h1] at h3 <;> omega
    · obtain ⟨s', hs'⟩ := dstate_of hjx' hσ' hhd
      cases hs'
  rcases Wu.end_cases hX hf.sound hf.tracked hub hh hnx with
    ⟨σ, hσy, hinv⟩ | ⟨σ, e1, hpos, hσy, hnone, hinv, he1⟩
  · obtain ⟨sy, rfl⟩ := dstate_of le_rfl hσy hhd
    rw [threadTime_eq hσy]
    exact (tc_cmp (c := 0) hpre hX hf hD hg hh hcta.symm hw hgd hhd hev' hσ ht le_rfl hσy
      (fun m1 h1 => by subst h1; exact hinv.2) (.inl rfl) (by omega)).1
  · have hk1 : (X.tr h).length - 1 ≤ (X.tr h).length := Nat.sub_le _ _
    obtain ⟨sy, rfl⟩ := dstate_of hk1 hσy hhd
    rw [threadTime_stop hσy hnone]
    have hs1 : (X.tr h).length = (X.tr h).length - 1 + 1 := by omega
    have hcs : Lk.cnt isTcColl X h (X.tr h).length = Lk.cnt isTcColl X h ((X.tr h).length - 1) +
        if isTcColl e1 = true then 1 else 0 := by
      conv_lhs => rw [hs1]
      exact Lk.cnt_succ _ (show (X.tr h)[(X.tr h).length - 1]? = some e1 from he1)
    have hb := Lk.isTcColl_state hpre hX hf hh he1 hσy
    have hbit : (if isTcColl e1 = true then 1 else 0) = bit (Lk.dTc sy) := by
      rw [hb]; rfl
    have := (tc_cmp (c := bit (Lk.dTc sy)) hpre hX hf hD hg hh hcta.symm hw hgd hhd hev' hσ ht
      hk1 hσy (fun m1 h1 => by subst h1; exact hinv.2) (.inr rfl) (by omega)).2 rfl
    show dcompT sy + 1 ≤ dcompT s
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
