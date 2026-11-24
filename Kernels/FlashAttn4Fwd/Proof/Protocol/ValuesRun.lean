-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.Values
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsBaseCausality
public import Lemmas.Flow.NthEv
public import Lemmas.Real.Softmax
public import Lemmas.Real.Rescale

@[expose] public section

/-! # The staged values are an online softmax

A correction thread `g` writes the staging byte of slot `(x, y, k)` of half `hh` of stage `st` in
the final pass of item `j` (`CorrValues.final`): byte `k` of the half-precision product of the
value `o` its final load of column `d = 64 hh + x` returned and `1 / l'`, for the row sum `l` its
statistics load read. With `n = kvBlocks P`, visit `τ` of item `j` is tile `u = n j + τ` of the
row's softmax thread `h` (`SoftPartner`, unique, `Stats.soft_unique`), whose loads returned the
scores of the visit (`ScoreLoads`); `h` computed on them a reference exponent `c u` and a row sum
`l u` (`SoftValues`), and the PV MMAs left `R u d` at the row's accumulator (`PvChain`). The run
of item `j` (`run`) is `c (n j + τ)`, `l (n j + τ)` and `R (n j + τ) d`:

* the first visit and the row sums are the softmax's (`SoftValues.sumFirst`, `sumStep`);
* a loop visit `τ + 1` adds its probabilities times `V` to the correction's rescale store of the
  credit when there is one, which holds `R (u - 1) d · α` for the factor `α` of the trip
  (`CorrValues.rescale`, `StatsReads`, `SoftValues.alphaStore`), and to `R (u - 1) d` otherwise;
  then the factor is not below one (`CorrValues.trip`), and the reference does not decrease
  (`SoftValues.refStep`), so it is one (`Numeric.two_rpow_sub_eq_one`).

The final load returned `R (n j + n - 1) d` and the statistics load the row sum `l (n j + n - 1)`
(`SoftValues.sumStore`), which is positive (`Numeric.softmax_sum_pos`), so the byte is that of
the half-precision ratio of the run's final accumulator and row sum (`outputValues`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

namespace Values

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Visit `τ` of item `J` is tile `n J + τ`. -/
theorem div_mod_eq {n J τ : Nat} (hn : 0 < n) (hτ : τ < n) :
    (n * J + τ) / n = J ∧ (n * J + τ) % n = τ := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hτ, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hτ]

/-- The tiles of item `j` depend on a thread only through its CTA. -/
theorem tile_eq {g h : Nat} (hc : ctaOf L h = ctaOf L g) (j st : Nat) :
    tileBatch L h j = tileBatch L g j ∧ tileHead L h j = tileHead L g j ∧
      tileRow L h j st = tileRow L g j st := by
  simp [tileRow, tileBlock, tileHead, tileBatch, workOf, clusterOf, rankOf, hc]

/-- The partner's scores of visit `τ` of item `J`. -/
theorem tileScore_eq {g st h u J τ : Nat} (hp : SoftPartner L g st h)
    (h1 : u / kvBlocks P = J) (h2 : u % kvBlocks P = τ) (k : Nat) :
    tileScore P L h u k = score P (tileBatch L g J) (tileHead L g J) (tileRow L g J st + rowOf L g)
      (visitKey P τ k) := by
  obtain ⟨-, -, hst, hc, hr⟩ := hp
  obtain ⟨t1, t2, t3⟩ := tile_eq (L := L) hc J st
  simp only [tileScore, h1, h2, hst, hr, t1, t2, t3]

/-- The PV sum of visit `τ` of item `J`. -/
theorem pvSum_eq {g u J τ d : Nat} (pv : Nat → Nat → ℝ) (h1 : u / kvBlocks P = J)
    (h2 : u % kvBlocks P = τ) :
    pvSum P L g pv u d = ∑ k ∈ Finset.range 128,
      pv u k * P.v (tileBatch L g J) (tileHead L g J) (visitKey P τ k) d := by
  simp only [pvSum, h1, h2]

/-- The credit arrivals grow along the trace. -/
theorem pArr_mono {g st i n : Nat} (h : i ≤ n) : pArr L X g st i ≤ pArr L X g st n := by
  unfold pArr arrivals
  exact countP_take_mono _ _ h

/-- **The staged values.** Every staging byte a correction thread writes in the final pass of an
item is byte `k` of the half-precision ratio of the final accumulator and row sum of an online
softmax of its row (`SoftmaxRun`), given that the Tensor Memory loads return single-precision
floats and the correction threads' statistics reads read finite words (`LoadFloats`,
`StatsFloats`). -/
theorem outputValues (hpre : Pre P L mem0) (hv : ValueFacts P L X) (hsc : ScoreLoads P L X)
    (hrd : StatsReads L X) (hpv : PvChain P L X)
    (hlf : ∀ {g k pc a : Nat} {vals : List Value}, g < L.threads →
      X.get (g, k) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩ → F32s vals)
    (hsf : ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}, g < L.threads →
      8 ≤ warpOf L g → warpOf L g < 12 → X.get (g, k) = some ⟨pc, .rd a bs⟩ →
        ∃ x, F32Read bs x) : OutputValues P L X := by
  constructor
  intro g n st hh x y k dst bs hg h8 h12 hw hst hhh hx hy hk hcov
  have hn : 0 < kvBlocks P := by
    have := hpre.skPos
    unfold kvBlocks
    omega
  have hcv := hv.corr hg h8 h12
  obtain ⟨rfl, i, a, p, r, vals, bl, hin, hld, hq, hp, hcol, hsr, hval⟩ :=
    hcv.final hw hst hhh hx hy hk hcov
  generalize arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take n) = J at hq hsr hval ⊢
  -- the row's softmax thread and its values
  obtain ⟨h, il, pcl, al, wsl, hpart, hgetl, hssl, hordl, hbl⟩ := hrd hg h8 h12 hst hsr
  obtain ⟨c, l, hs⟩ := hv.soft hpart.1 hpart.2.1 (hsc hpart.1 hpart.2.1)
  obtain ⟨R, hR0, hRs, hRn, hRl⟩ :=
    hpv (pv := fun u k => (2 : ℝ) ^ (P.scale * tileScore P L h u k - c u)) hg h8 h12 hst hpart
      hs.pStore
  have huniq : ∀ {h' : Nat}, SoftPartner L g st h' → h' = h := fun hp' =>
    Stats.soft_unique hpre (hp'.2.2.2.1.trans hpart.2.2.2.1.symm) hp'.2.1 hpart.2.1
      (hp'.2.2.1.trans hpart.2.2.1.symm) (hp'.2.2.2.2.trans hpart.2.2.2.2.symm)
  -- the factor of loop trip `τ` of item `J`
  have halpha : ∀ τ r' (bs' : List (Option Byte)), τ + 1 < kvBlocks P →
      StatRead L X g st ((kvBlocks P + 1) * J + 1 + τ) r' bs' →
      F32Read bs' ((2 : ℝ) ^ (c (kvBlocks P * J + τ) - c (kvBlocks P * J + τ + 1))) := by
    intro τ r' bs' hτ hr'
    obtain ⟨h', i', pc', a', ws', hp', hget', hss', hord', hbs'⟩ := hrd hg h8 h12 hst hr'
    obtain rfl := huniq hp'
    obtain ⟨v, -, hrb, hval⟩ := hs.alphaStore hget' hss' hτ hord'
    exact ⟨v, hbs' ▸ hrb, hval⟩
  -- the visits of item `J`
  have hvis : ∀ τ < kvBlocks P, (kvBlocks P * J + τ) / kvBlocks P = J ∧
      (kvBlocks P * J + τ) % kvBlocks P = τ := fun τ hτ => div_mod_eq hn hτ
  have hsum : ∀ τ < kvBlocks P, ∀ e : ℝ → ℝ,
      ∑ kk ∈ Finset.range 128, e (P.scale * tileScore P L h (kvBlocks P * J + τ) kk) =
        ∑ kk ∈ Finset.range 128, e (P.scale * score P (tileBatch L g J) (tileHead L g J)
          (tileRow L g J st + rowOf L g) (visitKey P τ kk)) := by
    intro τ hτ e
    refine Finset.sum_congr rfl fun kk _ => ?_
    rw [tileScore_eq hpart (hvis τ hτ).1 (hvis τ hτ).2]
  have hpvs : ∀ τ < kvBlocks P, ∀ d,
      pvSum P L g (fun u k => (2 : ℝ) ^ (P.scale * tileScore P L h u k - c u))
          (kvBlocks P * J + τ) d =
        ∑ kk ∈ Finset.range 128, (2 : ℝ) ^ (P.scale * score P (tileBatch L g J) (tileHead L g J)
          (tileRow L g J st + rowOf L g) (visitKey P τ kk) - c (kvBlocks P * J + τ)) *
          P.v (tileBatch L g J) (tileHead L g J) (visitKey P τ kk) d := by
    intro τ hτ d
    rw [pvSum_eq _ (hvis τ hτ).1 (hvis τ hτ).2]
    refine Finset.sum_congr rfl fun kk _ => ?_
    rw [tileScore_eq hpart (hvis τ hτ).1 (hvis τ hτ).2]
  have hpn : kvBlocks P * J + (kvBlocks P - 1) + 1 ≤ pArr L X g st n := by
    have h1 := pArr_mono (L := L) (X := X) (g := g) (st := st) hin.le
    rw [hq, Nat.mul_succ] at h1
    omega
  have hrun : SoftmaxRun P (tileBatch L g J) (tileHead L g J) (tileRow L g J st + rowOf L g)
      (fun τ => c (kvBlocks P * J + τ)) (fun τ => l (kvBlocks P * J + τ))
      (fun τ d => R (kvBlocks P * J + τ) d) := by
    refine ⟨fun d hd => ?_, fun τ hτ d hd => ?_, ?_, fun τ hτ => ?_⟩
    · show R (kvBlocks P * J + 0) d = _
      rw [hR0 _ d (hvis 0 hn).2 hd, hpvs 0 hn d]
    · have hu0 : (kvBlocks P * J + τ + 1) % kvBlocks P ≠ 0 := by
        have := (hvis (τ + 1) hτ).2
        rw [← Nat.add_assoc] at this
        omega
      have hu1 : kvBlocks P * J + τ + 1 - 1 = kvBlocks P * J + τ := rfl
      have hpvs1 : pvSum P L g (fun u k => (2 : ℝ) ^ (P.scale * tileScore P L h u k - c u))
          (kvBlocks P * J + τ + 1) d = ∑ kk ∈ Finset.range 128, (2 : ℝ) ^ (P.scale *
            score P (tileBatch L g J) (tileHead L g J) (tileRow L g J st + rowOf L g)
              (visitKey P (τ + 1) kk) - c (kvBlocks P * J + τ + 1)) *
            P.v (tileBatch L g J) (tileHead L g J) (visitKey P (τ + 1) kk) d :=
        hpvs (τ + 1) hτ d
      show R (kvBlocks P * J + τ + 1) d = R (kvBlocks P * J + τ) d *
          2 ^ (c (kvBlocks P * J + τ) - c (kvBlocks P * J + τ + 1)) + ∑ kk ∈ Finset.range 128,
            (2 : ℝ) ^ (P.scale * score P (tileBatch L g J) (tileHead L g J)
              (tileRow L g J st + rowOf L g) (visitKey P (τ + 1) kk) -
                c (kvBlocks P * J + τ + 1)) *
            P.v (tileBatch L g J) (tileHead L g J) (visitKey P (τ + 1) kk) d
      rw [← hpvs1]
      by_cases hex : ∃ yv, CorrStored L X g st (kvBlocks P * J + τ + 1) d yv
      · obtain ⟨yv, hyv⟩ := hex
        rw [hRs _ d yv hu0 hd hyv]
        obtain ⟨i1, a1, p1, vals1, hst1, hq1, hp1, hcol1, hv1⟩ := hyv
        have hO1 : InO st (tcDataCell32 L g a1 p1) := by
          unfold InO
          rw [hcol1]
          omega
        obtain ⟨i', a', p', r', vals', bs', -, hld', hq', hp', hcell', -, hsr', himp⟩ :=
          hcv.rescale hst1 hst hq1 hp1 hO1
        have hload := hRl hld' hq' hp' (by rw [hcell']; exact hO1)
        rw [hcell', hcol1, Nat.add_sub_cancel_left, hu1] at hload
        rw [hu1, (hvis τ (by omega)).1, (hvis τ (by omega)).2] at hsr'
        have hv2 := himp (hlf hg hld'.choose_spec) _ _ hload (halpha τ r' bs' hτ hsr')
        rw [hv1] at hv2
        have hy : yv = R (kvBlocks P * J + τ) d *
            2 ^ (c (kvBlocks P * J + τ) - c (kvBlocks P * J + τ + 1)) := by
          simpa using hv2
        rw [hy]
      · rw [hRn _ d hu0 hd hex, hu1]
        obtain ⟨r2, bs2, -, hsr2, himp2⟩ := hcv.trip (j := J) (t := τ) (e := n) hst hτ (by omega)
        have hnlt : ¬ (2 : ℝ) ^ (c (kvBlocks P * J + τ) - c (kvBlocks P * J + τ + 1)) < 1 :=
          fun hlt => hex (himp2 _ (halpha τ r2 bs2 hτ hsr2) hlt
            (fun _ _ _ _ _ h => hlf hg h) (fun _ _ _ _ _ h => hsf hg h8 h12 h) d hd)
        have hle := hs.refStep _ hu0
        rw [hu1] at hle
        rw [Numeric.two_rpow_sub_eq_one hle hnlt, mul_one]
    · show l (kvBlocks P * J + 0) = _
      rw [hs.sumFirst _ (hvis 0 hn).2]
      exact hsum 0 hn fun e => (2 : ℝ) ^ (e - c (kvBlocks P * J + 0))
    · have hu0 : (kvBlocks P * J + τ + 1) % kvBlocks P ≠ 0 := by
        have := (hvis (τ + 1) hτ).2
        rw [← Nat.add_assoc] at this
        omega
      show l (kvBlocks P * J + τ + 1) = l (kvBlocks P * J + τ) *
          2 ^ (c (kvBlocks P * J + τ) - c (kvBlocks P * J + τ + 1)) + _
      rw [hs.sumStep _ hu0]
      congr 1
      exact hsum (τ + 1) hτ fun e => (2 : ℝ) ^ (e - c (kvBlocks P * J + τ + 1))
  -- the final load and the row sum
  have hO : InO st (tcDataCell32 L g a p) := by
    unfold InO
    rw [hcol]
    omega
  have hfin := hRl hld hq hp hO
  rw [hcol, Nat.add_sub_cancel_left] at hfin
  have hlast : kvBlocks P * (J + 1) - 1 = kvBlocks P * J + (kvBlocks P - 1) := by
    rw [Nat.mul_succ]
    omega
  rw [hlast] at hfin
  have hlw := hs.sumStore hgetl hssl hordl
  have hl1 : kvBlocks P * J + kvBlocks P - 1 = kvBlocks P * J + (kvBlocks P - 1) := by omega
  rw [hl1] at hlw
  have hw' := hval (hlf hg hld.choose_spec) _ _ hfin (by
    obtain ⟨v, -, hrb, hval⟩ := hlw
    exact ⟨v, hbl ▸ hrb, hval⟩)
  have hpos : 0 < l (kvBlocks P * J + (kvBlocks P - 1)) :=
    Numeric.softmax_sum_pos (n := kvBlocks P) (b := 128)
      (x := fun τ kk => P.scale * score P (tileBatch L g J) (tileHead L g J)
        (tileRow L g J st + rowOf L g) (visitKey P τ kk))
      (c := fun τ => c (kvBlocks P * J + τ)) (l := fun τ => l (kvBlocks P * J + τ))
      (by norm_num) hrun.sum0 hrun.sumStep (kvBlocks P - 1) (by omega)
  refine ⟨_, _, _, hrun, ?_⟩
  rw [hw', Numeric.mul_recip_guard hpos]

end Values

end
end PTX.Kernels.FlashAttn4Fwd.Proof
