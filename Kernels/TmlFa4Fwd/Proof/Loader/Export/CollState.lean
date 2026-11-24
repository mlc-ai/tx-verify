-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Export.CollBlk
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every state of a loader warp stands in its schedule of collectives -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (scanBase endBase primeBase doneBase passTime clk bandL)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hub : ¬ HasUb X)
  (hg : g < L.threads) {b : Bool} (hw : Prologue.warpIndex L g = wOf b)
include hp hX hub hg hw

/-- A role state. -/
private theorem role_cls {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n))) :
    LCls p L g b (n .shfl + n .vote + els X g k) (Progress.Ld.time p d n) (tagS d.site) := by
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [Proof.cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  obtain ⟨-, hR⟩ := (LdWarp.good hp hX wOf_or hg hw k).2 _ hσ
  obtain ⟨hJ, hF⟩ := hR hub0
  have hSu := su_pick hp hX hg (wb hw) hσ hub0
  have hcm : Progress.cmax p = 7 * (p.batch + 3) + 6 := rfl
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hdn : endBase p + 4 * Progress.cmax p + 8 = doneBase p := rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := lc_cases d.site
  have E0 : lc d.site = .early ∨ lc d.site = .p1 ∨ lc d.site = .req → n (.load .commit) = 0 →
      els X g k = 0 := fun hl hz => by
    rw [ld_els hp hX hg hw hσ hub0 (fun h14 => (ld_els_out hp hX hg h14 hσ hub0 rfl).1 hl hz)]
    split <;> rfl
  cases hlc : lc d.site with
  | early =>
    have hs := c3 hlc
    obtain ⟨h1, h2, h3⟩ : n .shfl = 3 ∧ n .vote = 0 ∧ n (.load .commit) = 0 := by
      simpa only [LFits, hlc] using hF
    rw [E0 (.inl hlc) h3, h1, h2]
    have ht : Progress.Ld.time p d n = scanBase := by simp only [Progress.Ld.time, hs]
    have htg : tagS d.site = none := by rw [hs]; rfl
    rw [ht, htg]
    exact .scanOff _ _ (by omega) (by omega) (by omega)
  | p1 =>
    obtain ⟨hsc, hl⟩ := c1 hlc
    obtain ⟨h0, hFE⟩ : n (.load .commit) = 0 ∧ Epilogue.Fits p L g (toE d) (n .shfl) (n .vote) := by
      simpa only [LFits, hlc] using hF
    rw [E0 (.inr (.inl hlc)) h0, Nat.add_zero]
    have hep : d.site.epi = (toE d).site := rfl
    have he0 : d.site.epi = d.site.toE := by
      revert hsc; cases d.site <;> simp [Site.scan, Site.epi, Site.toE]
    obtain ⟨n0, v0, hps, hn0, hnv, w1, w2, w3, w4⟩ := ld_scan_band hFE hsc (by rw [← hep, he0])
    rw [hl] at hps w4
    have hbd := Epilogue.fits_coll_le hp hFE (by rw [← hep, he0, w4])
    simp only [Epilogue.PassStart, Bool.false_eq_true, ite_false] at hps
    rw [time_scan hsc, hl, h0]
    simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.sub_zero]
    cases hco : Progress.Out.coll (Progress.Ld.toE d.site) with
    | true =>
      obtain ⟨l, n0', v0', q, hps', hq1, hq⟩ :=
        Epilogue.coll_pos hFE (by rw [← hep, he0, w3]; exact hco)
      have hll : l = false := by rw [← hq.late, ← hep, he0, w4]
      subst hll
      simp only [Epilogue.PassStart, Bool.false_eq_true, ite_false] at hps'
      have hN : n .shfl + n .vote = 3 + q := by omega
      have ht : passTime scanBase (n .shfl + Progress.Out.ballots (Progress.Ld.toE d.site)) true =
          scanBase + 2 * (3 + q) := by simp only [passTime, ite_true]; omega
      have htg : tagS d.site = some (.site d.site) := by simp [tagS, w1, hco]
      rw [hN, ht, htg]
      exact .scan q d.site he0 hsc (by rw [hep]; exact hq) (by omega)
    | false =>
      have htg : tagS d.site = none := by simp [tagS, w1, hco]
      rw [htg]
      simp only [passTime, Bool.false_eq_true, ite_false]
      exact .scanOff _ _ (by omega) (by omega) (by omega)
  | req =>
    have hq := c4 hlc
    obtain ⟨h0, hFE, -⟩ : n (.load .commit) = 0 ∧
        Epilogue.Fits p L g (toE d) (n .shfl) (n .vote) ∧ d.v.co = coords p L g d.v.sc := by
      simpa only [LFits, hlc] using hF
    rw [E0 (.inr (.inr hlc)) h0, Nat.add_zero]
    have hC : ∃ R bal, Epilogue.ChosenVals p L g R bal (toE d) (n .shfl) (n .vote) := by
      have h2' := hFE
      rcases hq with h | h | h <;> simp only [Epilogue.Fits, toE, h, Site.epi] at h2'
      · exact h2'
      · obtain ⟨R0, bal, hC, -⟩ := h2'; exact ⟨R0, bal, hC⟩
      · obtain ⟨R0, bal, hC, -⟩ := h2'; exact ⟨R0, bal, hC⟩
    obtain ⟨R, bal, hP, -, -, -, -, -, -, hns, hnv⟩ := hC
    have hN : n .shfl + n .vote = chN R bal := by unfold chN; omega
    have htg : tagS d.site = none := by rcases hq with h | h | h <;> rw [h] <;> rfl
    rw [hN, htg]
    refine .req _ _ _ _ _ ⟨R, bal, hP, rfl, rfl, rfl, rfl⟩ ?_
    rcases hq with h | h | h <;> simp only [Progress.Ld.time, h] <;> omega
  | p2 =>
    obtain ⟨hsc, hl⟩ := c2 hlc
    obtain ⟨h32, hFE, -, hpk⟩ : 32 * n (.load .commit) ≤ n .shfl ∧
        Epilogue.Fits p L g (toE d) (n .shfl - 32 * n (.load .commit)) (n .vote) ∧
        SuRef p L g d.v ∧ n (.load .commit) = pkts d.v.su.r28 := by
      simpa only [LFits, hlc] using hF
    obtain ⟨R, bal, hP, hT⟩ := sus_tile (hSu.1 (.inr hlc))
    have hz : n (.load .commit) ≠ 0 := fun h => absurd (pkts_ge d.v.su.r28) (by
        rw [← hpk, h]; decide)
    have hE := ld_els hp hX hg hw hσ hub0
      (fun h14 => (ld_els_out hp hX hg h14 hσ hub0 rfl).2.1 hlc hz)
    have hTot : 32 * n (.load .commit) + els X g k =
        blkTot b (w0 d.v.su.r28) (decide (Last d.v)) (pkts d.v.su.r28) := by
      rw [hE, hpk]; exact tot_eq ..
    clear hpk
    generalize pkts d.v.su.r28 = P at hT hTot ⊢
    generalize w0 d.v.su.r28 = W at hT hTot ⊢
    have hep : d.site.epi = (toE d).site := rfl
    have he0 : d.site.epi = d.site.toE := by
      revert hsc; cases d.site <;> simp [Site.scan, Site.epi, Site.toE]
    obtain ⟨n0, v0, hps, hn0, hnv, w1, w2, w3, w4⟩ := ld_scan_band hFE hsc (by rw [← hep, he0])
    rw [hl] at hps w4
    have hv0 := Epilogue.passStart_v0 hps
    simp only [ite_true] at hv0
    have hbd := Epilogue.fits_coll_le_all hp hFE
    have hge : n0 + v0 = chN R bal := by
      have hps' := hps
      simp only [Epilogue.PassStart, ite_true] at hps'
      obtain ⟨R', bal', hP', rfl, rfl⟩ := hps'
      obtain ⟨rfl, rfl⟩ := hP'.unique hP
      unfold chN; omega
    have hba : Progress.Out.ballots (Progress.Ld.toE d.site) ≤ 1 := by
      unfold Progress.Out.ballots; split <;> omega
    rw [time_scan hsc, hl]
    simp only [ite_true]
    cases hco : Progress.Out.coll (Progress.Ld.toE d.site) with
    | true =>
      obtain ⟨l, n0', v0', q, hps', hq1, hq⟩ :=
        Epilogue.coll_pos hFE (by rw [← hep, he0, w3]; exact hco)
      have hll : l = true := by rw [← hq.late, ← hep, he0, w4]
      subst hll
      obtain ⟨rfl, rfl⟩ := Epilogue.PassStart.same rfl hps hps'
      have hN : n .shfl + n .vote + els X g k = blkTot b W (decide (Last d.v)) P +
          (n0 + v0 + q) := by omega
      have ht : passTime (endBase p) (n .shfl - 32 * n (.load .commit) +
          Progress.Out.ballots (Progress.Ld.toE d.site)) true =
          endBase p + 2 * (n0 + q) := by simp only [passTime, ite_true]; omega
      have htg : tagS d.site = some (.site d.site) := by simp [tagS, w1, hco]
      rw [hN, ht, htg]
      exact .scan2 _ _ _ _ n0 v0 q d.site hT hps he0 hsc (by rw [hep]; exact hq) hv0
        (by omega)
    | false =>
      have htg : tagS d.site = none := by simp [tagS, w1, hco]
      have hN : n .shfl + n .vote + els X g k = blkTot b W (decide (Last d.v)) P +
          (n .shfl - 32 * n (.load .commit) + n .vote) := by omega
      rw [htg, hN]
      simp only [passTime, Bool.false_eq_true, ite_false]
      have h12 := hT.ch_ge
      exact .scan2Off _ _ _ _ _ _ hT (by omega) (by omega) (by omega) (by omega)
  | drain =>
    obtain ⟨l, h32, hFE, h1, h2⟩ : ∃ l, 32 * n (.load .commit) ≤ n .shfl ∧
        Epilogue.Fits p L g { d.v.sc with site := .exit l } (n .shfl - 32 * n (.load .commit))
          (n .vote) ∧
        (l = true → SuRef p L g d.v ∧ n (.load .commit) = pkts d.v.su.r28) ∧
        (l = false → n (.load .commit) = 0) := by
      simpa only [LFits, hlc] using hF
    have hx : Epilogue.Fits.ExitAt p L g l (n .shfl - 32 * n (.load .commit)) (n .vote) := hFE
    have ht : Progress.Ld.time p d n = doneBase p + drT d.site := by
      rcases c5 hlc with ⟨j, h⟩ | h | h | h | h <;> simp only [Progress.Ld.time, h, drT]
    have hde : b = true → d.site ≠ .de := fun hb hc => by
      subst hb
      have := hJ.tma (by rw [hc]; rfl)
      cases this
    rw [ht]
    cases l with
    | false =>
      have h0 := h2 rfl
      have hE := ld_els hp hX hg hw hσ hub0
        (fun h14 => ((ld_els_out hp hX hg h14 hσ hub0 rfl).2.2 hlc).1 h0)
      have hN : n .shfl + n .vote + els X g k =
          (n .shfl - 32 * n (.load .commit)) + n .vote + drN b d.site := by
        rw [hE, h0, Nat.mul_zero, Nat.sub_zero]; unfold drN; rfl
      rw [hN]
      exact .end1 _ _ _ hlc hde hx
    | true =>
      obtain ⟨-, hpk⟩ := h1 rfl
      have hz : n (.load .commit) ≠ 0 := fun h => absurd (pkts_ge d.v.su.r28) (by
        rw [← hpk, h]; decide)
      obtain ⟨R, bal, hP, hT⟩ := sus_tile ((hSu.2 hlc).resolve_left hz)
      have hE := ld_els hp hX hg hw hσ hub0
        (fun h14 => ((ld_els_out hp hX hg h14 hσ hub0 rfl).2.2 hlc).2 hz)
      have hTot : 32 * n (.load .commit) + els X g k =
          blkTot b (w0 d.v.su.r28) (decide (Last d.v)) (pkts d.v.su.r28) + drN b d.site := by
        rw [hE, hpk]; exact tot_eq' ..
      clear hpk h1 h2
      generalize pkts d.v.su.r28 = P at hT hTot ⊢
      generalize w0 d.v.su.r28 = W at hT hTot ⊢
      have hN : n .shfl + n .vote + els X g k =
          blkTot b W (decide (Last d.v)) P +
            (n .shfl - 32 * n (.load .commit) + n .vote) + drN b d.site := by omega
      rw [hN]
      exact .end2 _ _ _ _ _ _ _ hT hlc hde hx
  | blk =>
    have hblk := lc_blk.mp hlc
    obtain ⟨h32, hFE, -, hRd, -⟩ := lfits_blk_of hblk hF
    obtain ⟨R, bal, hP, hT⟩ := sus_tile (hSu.1 (.inl hlc))
    have hC : ∃ R bal, Epilogue.ChosenVals p L g R bal (toE d)
        (n .shfl - 32 * n (.load .commit) - pktSh d.site) (n .vote) := by
      have h2' := hFE
      simp only [Epilogue.Fits, toE, epi_blk hblk] at h2'
      obtain ⟨R0, bal, hC, -⟩ := h2'
      exact ⟨R0, bal, hC⟩
    obtain ⟨R', bal', hP', -, -, -, -, -, -, hns, hnv⟩ := hC
    obtain ⟨rfl, rfl⟩ := hP'.unique hP
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hblk
    have htm : b = true → isT d.site = false := fun hb => by
      subst hb
      by_contra hc
      have := hJ.tma (by revert hc; cases d.site <;> simp [isT, Site.isTma])
      cases this
    have hPlc : ∃ x, Plc (w0 d.v.su.r28) (decide (Last d.v)) (pkts d.v.su.r28) x o ∧
        els X g k + 32 * n (.load .commit) + pktSh d.site =
          plcN b (w0 d.v.su.r28) (decide (Last d.v)) x d.site ∧
        (o = .prime → x = 0) ∧ (o ≠ .prime → 1 ≤ x ∧
          n (.load .commit) = 2 + 2 * (x - 1) + inBlk d.site) := by
      exact blk_plc hp hX hg hw hσ hub0 hRd.2 ho htm
    obtain ⟨x, hx, hN, hx0, hx1⟩ := hPlc
    have hbm := hT.pkts_le hp hg
    have hwm := hT.warm_le
    have ht : Progress.Ld.time p d n = blkT p x d.site := by
      rw [time_blk ho]
      unfold blkT
      by_cases hop : o = .prime
      · simp only [hop, hx0 hop, ite_true]
      · obtain ⟨h1, h2⟩ := hx1 hop
        have hx' : x ≤ Progress.bmax p := hx.le hwm hbm
        have hs : Progress.Ld.slot p (Progress.Ld.idx d.site n) = x - 1 := by
          unfold Progress.Ld.slot
          rw [idx_blk d.site h2]
          exact Progress.slotOf_eq (Nat.le_trans (Nat.sub_le _ _) hx')
        have hx0' : x ≠ 0 := Nat.one_le_iff_ne_zero.mp h1
        simp only [hop, hx0', ite_false, hs]
    have hN' : n .shfl + n .vote + els X g k =
        chN R' bal' + plcN b (w0 d.v.su.r28) (decide (Last d.v)) x d.site := by
      rw [← hN]; unfold chN; clear * - hns hnv h32; omega
    rw [ht, hN']
    exact .blk _ _ _ _ _ o d.site hT ho hx htm

/-- **Where a state of a loader warp stands.** -/
theorem ld_cls {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    LCls p L g b (((X.tr g).take k).countP Sched.isWarpColl) (Progress.time p L g σ)
      (tagOf p L g σ) := by
  rw [ld_cnt_eq hp hX hub hg (wb hw) hσ]
  have hR := (LdWarp.good hp hX wOf_or hg hw k).2 _ hσ
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · obtain ⟨hS, hv, hZ⟩ := hR
    have hel : els X g k = 0 := ld_start_els hp hX hg (wb hw) hσ
    rw [hel]
    simp only
    rw [hv]
    simp only [Nat.add_zero]
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp only [StartAt] at hS
    case sh j =>
      rw [hS.1]
      have ht : Progress.time p L g (.inl ⟨.sh j, x1, x2, x3⟩, n) = Progress.shPc j.val := by
        fin_cases j <;> rfl
      rw [ht]
      exact .start j
    case fence =>
      rw [hS.1]
      exact .scanOff _ _ (by decide) (by show 172 < 256 + 6; decide)
        (by show 172 < _; rw [hprv, hsb]; omega)
    case bar =>
      rw [hS.1]
      exact .scanOff _ _ (by decide) (by show 173 < 256 + 6; decide)
        (by show 173 < _; rw [hprv, hsb]; omega)
  · obtain ⟨hbw, -⟩ := hR
    rename_i b'
    have : b' = b := by
      cases b' <;> cases b <;> first | rfl | simp [wOf] at hbw
    subst this
    exact role_cls hp hX hub hg hw hσ

/-- **A lane of a loader warp at its return.** -/
theorem ld_exit_cls {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hs : d.site = .exit) : ExitN p L g b (((X.tr g).take k).countP Sched.isWarpColl) := by
  have h := ld_cls hp hX hub hg hw hσ
  have htg : tagOf p L g (LdWarp.linj p L g b d n) = none := by
    show tagS d.site = none
    rw [hs]; rfl
  have ht : Progress.time p L g (LdWarp.linj p L g b d n) = doneBase p + 12 := by
    show Progress.Ld.time p d n = _
    simp only [Progress.Ld.time, hs]
  rw [ht, htg] at h
  exact h.exit hp hg

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
