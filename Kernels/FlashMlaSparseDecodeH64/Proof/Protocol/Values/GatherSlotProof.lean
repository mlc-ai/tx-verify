-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherSlot
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.CoordBits
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.CoordWord
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.GatherRows
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.GatherBlk
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.CoordRd
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Use
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.CoordStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LastRun
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid

@[expose] public section

/-! # The slot of every gather row

`gather_slot`: as `gather_rows_good` (the same read of the index lane's coordinate store), but
keeping which slot: row `i` of gather `q` of block `r` is the word of the lane `2 q + i / 2`'s
element `i % 2` of block `r`, the position `64 r + 4 q + i` of the cache's index array, rebased
on the main cache's blocks for an extra block. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.ClusterTrace PTX.Kit

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem cpc_inj {a b : Nat} (ha : a < 16) (hb : b < 16)
    (h : coordLoadPc a = coordLoadPc b) : a = b := by
  simp only [coordLoadPc] at h
  split_ifs at h <;> omega

private theorem origBlocks_eq (P : Params) (e : Nat) :
    w0OrigBlocks P e = FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen e) := by
  unfold w0OrigBlocks FlashMlaSparseDecodeH64.numOrigBlocks FlashMlaSparseDecodeH64.origPadded
    FlashMlaSparseDecodeH64.ceilToMultiple FlashMlaSparseDecodeH64.topkBlock
  omega

/-- **Every gather's row words name the block's slots.** -/
theorem gather_slot (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hN : CoordInputs L X) : GatherSlot P L X := by
  intro g k pc a s he hat
  have hW : CoordWordsBits L X := coord_words_bits hp hX hFw hR hI hB hN
  obtain ⟨q, hq, hpcq, h0, ys, hys, hyj⟩ := tma_gather_rows hp hX hFw hW he hat
  obtain ⟨q2, hq2, r, hpcg, hcnt, hmain, hextra⟩ :=
    tma_gatherBlk hp hX hFw (e := ⟨pc, .tensorIssue a s⟩) he hat rfl
  have hqq : q2 = q := by
    have h := hpcg.symm.trans hpcq
    simp only [gatherPc] at h
    split_ifs at h <;> omega
  rw [hqq] at hcnt
  have hM := origBlocks_eq P (ctaidY L g)
  have hdesc : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      gatherMap P (w0BlockExtra P (ctaidY L g) r) := by
    by_cases hlt : r < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))
    · have : w0BlockExtra P (ctaidY L g) r = false := by
        simp only [w0BlockExtra, hM, decide_eq_false_iff_not]; omega
      rw [this]; exact hmain hlt
    · have : w0BlockExtra P (ctaidY L g) r = true := by
        simp only [w0BlockExtra, hM, decide_eq_true_iff]; omega
      rw [this]; exact hextra (by omega)
  have hq16 : q = q2 := hqq.symm
  refine ⟨q, hq, r, hpcq, hcnt, h0, hdesc, ys, hys, fun i => ?_⟩
  have hlen : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hnoub : ∀ i f, i < k → (X.tr g)[i]? = some f → 2165 ≤ f.pc → f.pc ≤ 2330 →
      ∀ fl, f.kind ≠ .ub fl := fun i f hi hf h1 h2 => tma_prefix_noUb hX he hi hf h1 h2
  have hrdE : ∀ (i : Nat) (f : Event), (X.tr g)[i]? = some f → tmaRd f = true →
      ∃ pc' a' bs', f = ⟨pc', .rd a' bs'⟩ ∧ 2165 ≤ pc' ∧ pc' ≤ 2330 := by
    intro i f hf hr
    obtain ⟨pc', kd⟩ := f
    cases kd <;> simp [tmaRd] at hr
    rename_i a' bs'
    exact ⟨pc', a', bs', rfl, hr⟩
  have hwarp := hat.1
  -- the reads of a quadruple of the gather's block
  have hblkOf : ∀ i f, i < k → (X.tr g)[i]? = some f → tmaRd f = true →
      ∃ r' q' j', q' < 16 ∧ j' < 4 ∧ f.pc = coordLoadPc q' ∧
        ((X.tr g).take i).countP tmaRd = 64 * r' + 4 * q' + j' := by
    intro i f hi hf hr
    obtain ⟨pc', a', bs', rfl, h1, h2⟩ := hrdE i f hf hr
    obtain ⟨r', q', j', hq', hj', hpq, hc', -⟩ :=
      tma_rdBlock hp hX hFw (g := g) (k := i) hf ⟨hwarp, by omega, by omega⟩
    exact ⟨r', q', j', hq', hj', hpq, hc'⟩
  have hldRd : ∀ i f, i < k → (X.tr g)[i]? = some f → f.pc = coordLoadPc q → tmaRd f = true := by
    intro i f hi hf hpc
    have hr : 2165 ≤ f.pc ∧ f.pc ≤ 2330 := by
      rw [hpc]; unfold coordLoadPc; split_ifs <;> omega
    exact tma_coordRd hp hX hFw hf hq hpc (hnoub i f hi hf hr.1 hr.2)
  have hbnd : (if q = 15 then 64 else 4 * q + 8) ≥ 4 * q + 4 ∧
      (if q = 15 then 64 else 4 * q + 8) ≤ 64 := by split_ifs <;> omega
  have hrun := lastAt_run (X := X) (g := g) (k := k) (p := coordLoadPc q) (c0 := 64 * r + 4 * q)
    (isR := tmaRd) hlen hldRd ?_ ?_
  rotate_left
  · intro j hj
    obtain ⟨kr, f, hkr, hf, hrd, hc⟩ :=
      exists_occ (X.tr g) tmaRd k (64 * r + 4 * q + j) (by omega)
    obtain ⟨r', q', j', hq', hj', hpq, hc'⟩ := hblkOf kr f hkr hf hrd
    have hqq : q' = q := by omega
    subst hqq
    exact ⟨kr, f, hkr, hf, hpq, hrd, by omega⟩
  · intro i f hi hf hpc
    have hr := hldRd i f hi hf hpc
    obtain ⟨r', q', j', hq', hj', hpq, hc'⟩ := hblkOf i f hi hf hr
    have hqq : q' = q := cpc_inj hq' hq (hpq.symm.trans hpc)
    subst hqq
    have := countP_take_lt_at hi hf hr (p := tmaRd)
    omega
  obtain ⟨kr, f, hkr, hf, hpcf, hrd, hc, hl⟩ := hrun i.val i.isLt
  have hwdv : (coordWords X g k q).getD i.val (.pred false) = rdVal f := by
    simp [coordWords, List.getD_eq_getElem?_getD, List.getElem?_map, hl]
  have hy := hyj i
  rw [hwdv] at hy
  obtain ⟨pc', a', bs', rfl, h1, h2⟩ := hrdE kr f hf hrd
  have hatT : MbarRow.TmaAt L g pc' := ⟨hwarp, by omega, by omega⟩
  obtain ⟨s', u, q', jj, gw, kw, pcw, aw, z, hq', hjj, ⟨hl1, -⟩, hgw, hgetw, hatw, hawz, hv1,
    hcw, hrv⟩ := coord_read_val hp hX hFw hR hI hB hN hf hatT
  obtain ⟨r1, q1, j1, hq1, hj1, hpq1, hc1, ⟨hl2, -⟩, hv2⟩ :=
    tma_rdBlock hp hX hFw hf hatT
  have hqq : q1 = q := cpc_inj hq1 hq (hpq1.symm.trans hpcf)
  subst hqq
  have hrr : r1 = r := by omega
  have hjj1 : j1 = i.val := by omega
  subst hrr hjj1
  -- the read's ring slot and use are the block's
  have hlocE := hl1.symm.trans hl2
  simp only [wsLoc, Loc.mk.injEq, true_and] at hlocE
  have hsl4 : s'.val = r1 % 4 := by omega
  have hq4 : q' = q1 := by omega
  have hjjE : jj = i.val := by omega
  have hsl : s' = MbarRow.slot4 r1 := Fin.ext hsl4
  subst hsl
  have hu : u = r1 / 4 := by omega
  obtain ⟨hpcw, rw_, el, z', helt, hcntw, hbsw, h2471, h2560⟩ :=
    index_coordStore hp hX hFw hgetw hatw hawz
  have hzE : z' = z := by
    have := congrArg (fun l => l[0]?) hbsw
    simp [Value.toBytes, Value.bytes, Value.byteAt] at this
    exact this.symm
  subst hzE
  have hrwE : rw_ = r1 ∧ el = jj % 2 := by
    by_cases hsig : (L.tidOf gw).x % 4 = 0 <;>
      simp only [hsig, ite_true, ite_false] at hcw hcntw <;> omega
  obtain ⟨hrwE, hel2E⟩ := hrwE
  subst hrwE
  have hcta : gw / L.block = g / L.block := by
    rw [hgw, hp.block]; omega
  have hcX : ctaidX L gw = ctaidX L g := by simp only [ctaidX, ctaOf, hcta]
  have hcY : ctaidY L gw = ctaidY L g := by simp only [ctaidY, ctaOf, hcta]
  obtain ⟨hxlt, hylt⟩ := ctaid_lt hp g
  have hy' : ys i = wordInt (.bits 32 z') := by rw [hy, hrv]
  have hlane : tidOf L gw % 32 = 2 * q1 + i.val / 2 := by
    rw [tidOf_eq hp, hgw, hp.block]; omega
  rw [hlane] at h2471 h2560
  have hel2' : el = i.val % 2 := by omega
  subst hel2'
  have hpos : 2 * (2 * q1 + i.val / 2) + i.val % 2 = 4 * q1 + i.val := by omega
  unfold SlotRowWord
  rcases hpcw with rfl | rfl
  · obtain ⟨hlt, hsw⟩ := h2471 rfl
    rw [hcX, hcY] at hsw
    rw [hcY] at hlt
    have hex : w0BlockExtra P (ctaidY L g) rw_ = false := by
      simp only [w0BlockExtra, hM, decide_eq_false_iff_not]; omega
    have hsl : w0BlockSlot P (ctaidY L g) rw_ (4 * q1 + i.val) =
        64 * rw_ + 2 * (2 * q1 + i.val / 2) + i.val % 2 := by
      simp only [w0BlockSlot, hex, Bool.false_eq_true, ↓reduceIte]; omega
    rw [hex, hsl]
    refine ⟨?_, fun hv => hy'.trans (hsw.2 hv)⟩
    rcases hsw.1 with h | ⟨hv, hrow⟩
    · exact .inl (hy'.trans h)
    · exact .inr ⟨hv, hy'.trans hrow⟩
  · obtain ⟨hge, hsw⟩ := h2560 rfl
    rw [hcX, hcY] at hsw
    rw [hcY] at hge
    have hex : w0BlockExtra P (ctaidY L g) rw_ = true := by
      simp only [w0BlockExtra, hM, decide_eq_true_iff]; omega
    have hsl : w0BlockSlot P (ctaidY L g) rw_ (4 * q1 + i.val) =
        64 * (rw_ - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) +
          2 * (2 * q1 + i.val / 2) + i.val % 2 := by
      simp only [w0BlockSlot, hex, hM, ↓reduceIte]; omega
    rw [hex, hsl]
    refine ⟨?_, fun hv => hy'.trans (hsw.2 hv)⟩
    rcases hsw.1 with h | ⟨hv, hrow⟩
    · exact .inl (hy'.trans h)
    · exact .inr ⟨hv, hy'.trans hrow⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
