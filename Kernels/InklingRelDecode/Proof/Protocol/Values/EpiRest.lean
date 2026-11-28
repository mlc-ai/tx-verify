-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiOutWord
public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiLseWord
public import Kernels.InklingRelDecode.Proof.Protocol.Values.FinalWord
import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiRun
import Kernels.InklingRelDecode.Proof.Epilogue.Export.Visit
import Kernels.InklingRelDecode.Proof.Common.Export.StoreAddress
import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalInject
import Kernels.InklingRelDecode.Proof.Lib.StoreInject
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Geometry

@[expose] public section

/-! # The output and LSE words of the specification are stored

Coverage and agreement: every word of `OPart` and `LsePart` that the specification names has a
store of a data lane at its location, and every epilogue store that overlaps one of its bytes
writes that byte of the word. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Proof Lib.SoftRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem pick_thread {Q : Params} {L : Launch} {m : Mem0} (hp : Pre Q L m) {r s tok h d : Nat}
    (hr : r < Q.b) (hs : s < Q.splits) (ht : tok < Q.qLen r) (hh : h < 12) (hd : d < 128) :
    ∃ g, g < L.threads ∧ g % L.block < 128 ∧ ctaZ L (g / L.block) = r ∧
      ctaXc L (g / L.block) = s ∧ ctaY L (g / L.block) = h / 6 ∧
      Lib.tokM (g % L.block) = tok ∧ Lib.rowM (g % L.block) % 6 = h % 6 ∧
      g % L.block / 16 % 2 = d / 64 := by
  have h10 := hp.qLenLe r hr
  have hb := hp.block
  have hbp := hp.bPos
  set c := s * (2 * Q.b) + (h / 6) * Q.b + r with hc
  have hcg : c < L.grid := by
    rw [hp.grid]
    have : (s + 1) * (2 * Q.b) ≤ Q.splits * 2 * Q.b := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
    simp only [kvHeads]
    have h2 : h / 6 < 2 := by omega
    have h3 : (h / 6) * Q.b + r < 2 * Q.b := by nlinarith
    nlinarith
  have hco := Lib.coordinates hp hcg
  obtain ⟨row, hrd⟩ : ∃ row, row = 6 * tok + h % 6 := ⟨_, rfl⟩
  obtain ⟨tb, htd⟩ : ∃ tb, tb = 32 * (row / 16) + row % 16 + 16 * (d / 64) := ⟨_, rfl⟩
  have hrow : row < 60 := by omega
  have htb : tb < 128 := by omega
  have hc' : c = Q.b * (2 * s + h / 6) + r := by rw [hc]; ring
  have h2 : h / 6 < 2 := by omega
  have hcb : c / Q.b = 2 * s + h / 6 := by
    rw [hc', Nat.mul_add_div hbp, Nat.div_eq_of_lt hr]; rfl
  have hz : c % Q.b = r := by rw [hc', Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hx : c / (kvHeads * Q.b) = s := by
    have : c = (kvHeads * Q.b) * s + ((h / 6) * Q.b + r) := by
      simp only [kvHeads]; rw [hc]; ring
    rw [this, Nat.mul_add_div (by simp only [kvHeads]; omega), Nat.div_eq_of_lt]
    · rfl
    · simp only [kvHeads]; nlinarith
  have hy : c / Q.b % kvHeads = h / 6 := by
    simp only [kvHeads]; rw [hcb]; omega
  have gb : (c * L.block + tb) / L.block = c := by rw [hb]; omega
  have gm : (c * L.block + tb) % L.block = tb := by rw [hb]; omega
  have rowEq : Lib.rowM tb = row := by
    clear gb gm hy hx hz hcb hco hc hc' hcg
    have e1 : tb / 32 = row / 16 := by omega
    have e2 : tb % 16 = row % 16 := by omega
    unfold Lib.rowM; rw [e1, e2]; omega
  refine ⟨c * L.block + tb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Launch.threads]; rw [hb]; omega
  · rw [gm]; exact htb
  · rw [gb]; simp only [ctaZ, hco, Dim3.get]; exact hz
  · rw [gb]; simp only [ctaXc, hco, Dim3.get]; exact hx
  · rw [gb]; simp only [ctaY, hco, Dim3.get]; exact hy
  · rw [gm]; unfold Lib.tokM; rw [rowEq]; omega
  · rw [gm, rowEq]; omega
  · rw [gm]; omega

/-- The row state of the lane `g` at the dimension `d`. -/
noncomputable def rowK (Q : Params) (L : Launch) (g d : Nat) : Lib.SoftFold.St :=
  kState Q (ctaZ L (g / L.block)) (ctaXc L (g / L.block)) (Lib.tokM (g % L.block))
    (ctaY L (g / L.block) * 6 + Lib.rowM (g % L.block) % 6) d

/-- The number of blocks of the CTA of the lane `g`. -/
abbrev cellIters (Q : Params) (L : Launch) (g : Nat) : Nat :=
  Q.numIters (ctaZ L (g / L.block)) (ctaXc L (g / L.block))

/-- **The entry of the epilogue**: at pc 2562 of a data lane whose row loads, with a block,
register 1915 holds the row sum, and (a positive sum) register 1914 the carried maximum and
register 498 the scale of the logarithm; the row sum does not depend on the column. Without a
block register 1915 holds the zero bits. -/
structure EpiEntryFacts (Q : Params) (L : Launch) (X : Execution) : Prop where
  sum : ∀ g, g < L.threads → g % L.block < 128 →
    Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block)) → 0 < cellIters Q L g →
    ∀ t, Iface.LaneState L X g t → t.pc = 2562 →
      t.regs 1915 = some (.float .f32 (rowK Q L g 0).l)
  scale : ∀ g, g < L.threads → g % L.block < 128 →
    Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block)) → 0 < cellIters Q L g →
    ∀ t, Iface.LaneState L X g t → t.pc = 2562 → 0 < (rowK Q L g 0).l →
      t.regs 1914 = some (.float .f32 (rowK Q L g 0).m.toReal) ∧
        t.regs 498 = some (.float .f32 (Q.scale * log2eF32))
  column : ∀ g, g < L.threads → g % L.block < 128 →
    Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block)) → 0 < cellIters Q L g →
    ∀ d, (rowK Q L g d).l = (rowK Q L g 0).l
  empty : ∀ g, g < L.threads → g % L.block < 128 →
    Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block)) → cellIters Q L g = 0 →
    ∀ t, Iface.LaneState L X g t → t.pc = 2562 →
      t.regs 1915 = some (.bits 32 (BitVec.ofNat 64 0))

theorem kState_l_nonneg (hs : 0 < Q.scale) (r s tok h d : Nat) : 0 ≤ (kState Q r s tok h d).l := by
  have pos : 0 < Q.scale * log2eF32 := mul_pos hs Lib.SoftRow.log2e_pos
  unfold kState
  by_cases hf : (kBlocks Q r s tok h d).flatten = []
  · rw [(Lib.SoftFold.fold_empty _ pos _ hf).1]
  · exact (Lib.SoftFold.fold_normalized _ pos _ hf).2.le

/-- The row the picked thread loads. -/
theorem pick_valid (hp : Pre Q L m) {g r tok h : Nat} (hr : r < Q.b) (ht : tok < Q.qLen r)
    (hz : ctaZ L (g / L.block) = r) (htok : Lib.tokM (g % L.block) = tok)
    (hrm : Lib.rowM (g % L.block) % 6 = h % 6) :
    Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block)) := by
  have h10 := hp.qLenLe r hr
  unfold Lib.tokM at htok
  refine ⟨by omega, ?_⟩
  have : (L.ctaidOf (g / L.block)).get .z = r := hz
  rw [this, htok]
  exact ht

private theorem toBytes_get {v : Value} (hb : v.bytes = 4) {j : Nat} (hj : j < 4) :
    v.toBytes[j]? = some (v.byteAt j) := by
  simp [Value.toBytes, hb, hj]

private theorem site_of {pc : Nat} (h : pc ∈ Shared.outputSites) : Shared.IsStoreSite pc := by
  simp only [Shared.outputSites, List.mem_cons, List.mem_map, List.mem_range] at h
  rcases h with rfl | ⟨j, hj, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨⟨j, hj⟩, rfl⟩

private theorem out_bytes (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (final : ∀ {t k0 a vals sh j}, X.get (t, k0) = some ⟨2607, .tc (.ld a vals sh)⟩ →
      j < vals.length → Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a j).lane) →
      vals[j]? = some (.float .f32 (rowState Q (ctaZ L (t / L.block)) (ctaXc L (t / L.block))
        (laneRow (tcDataCell L t sh a j).lane / 6)
        (ctaY L (t / L.block) * 6 + laneRow (tcDataCell L t sh a j).lane % 6)
        ((tcDataCell L t sh a j).column - 256)).o))
    (hs : 0 < Q.scale) (EF : EpiEntryFacts Q L X) {g r s tok h d : Nat} (hg : g < L.threads)
    (lane : g % L.block < 128) (hz : ctaZ L (g / L.block) = r) (hx : ctaXc L (g / L.block) = s)
    (hy : ctaY L (g / L.block) = h / 6) (htok : Lib.tokM (g % L.block) = tok)
    (hrm : Lib.rowM (g % L.block) % 6 = h % 6) (hbit : g % L.block / 16 % 2 = d / 64)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block)))
    {k j : Nat} {a : Acc} {bs : List Byte} (hj : j = d % 64)
    (he : X.get (g, k) = some ⟨2751 + j + j / 2, .wr a bs⟩) :
    bs = (if Q.numIters r s = 0 then b32 0
      else Value.float .f32 (oPart Q r s tok h d)).toBytes := by
  have hnr : cellIters Q L g = Q.numIters r s := by
    show Q.numIters (ctaZ L (g / L.block)) (ctaXc L (g / L.block)) = _
    rw [hz, hx]
  by_cases hn : Q.numIters r s = 0
  · simp only [hn, ↓reduceIte]
    have hb0 : Lib.blocksOf Q L (g / L.block) = 0 := by
      show Q.numIters (ctaZ L (g / L.block)) (ctaXc L (g / L.block)) = 0
      rw [hz, hx]; exact hn
    have wait : EpiWait L X g true := by simpa [hb0] using epi_wait_of (g := g) hp hX hf
    exact out_store_zero hX (EF.empty g hg lane hv (by rw [hnr]; exact hn)) wait (by omega) he
  have hnp : 0 < cellIters Q L g := by rw [hnr]; omega
  have := out_store hp hX hf base final hs hv (EF.sum g hg lane hv hnp)
    (fun d' => EF.column g hg lane hv hnp d') (j := j) (by omega) he
  have e1 : h / 6 * 6 + h % 6 = h := by omega
  have e2 : 64 * (d / 64) + d % 64 = d := by omega
  rw [hz, hx, htok, hy, hrm, hbit, hj, e1, e2] at this
  exact this

private theorem oloc_pick {g r s tok h d j : Nat} (hz : ctaZ L (g / L.block) = r)
    (hx : ctaXc L (g / L.block) = s) (hy : ctaY L (g / L.block) = h / 6)
    (htok : Lib.tokM (g % L.block) = tok) (hrm : Lib.rowM (g % L.block) % 6 = h % 6)
    (hbit : g % L.block / 16 % 2 = d / 64) (hj : j = d % 64) :
    oLoc Q ((L.ctaidOf (g / L.block)).get .x)
      (Q.qStart ((L.ctaidOf (g / L.block)).get .z) + Lib.tokM (g % L.block))
      ((L.ctaidOf (g / L.block)).get .y * 6 + Lib.rowM (g % L.block) % 6)
      (64 * (g % L.block / 16 % 2) + j) = oLoc Q s (Q.qStart r + tok) h d := by
  have e1 : h / 6 * 6 + h % 6 = h := by omega
  have e2 : 64 * (d / 64) + d % 64 = d := by omega
  change oLoc Q (ctaXc L (g / L.block)) (Q.qStart (ctaZ L (g / L.block)) + _)
    (ctaY L (g / L.block) * 6 + _) _ = _
  rw [hz, hx, hy, htok, hrm, hbit, hj, e1, e2]

/-- **Every word of `OPart` is stored, and every epilogue store that overlaps one of its bytes
writes that byte of it.** -/
theorem out_rest (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hc : Complete L X) (hcl : ∀ g, ¬ ClcCanceled L X g)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (final : ∀ {t k0 a vals sh j}, X.get (t, k0) = some ⟨2607, .tc (.ld a vals sh)⟩ →
      j < vals.length → Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a j).lane) →
      vals[j]? = some (.float .f32 (rowState Q (ctaZ L (t / L.block)) (ctaXc L (t / L.block))
        (laneRow (tcDataCell L t sh a j).lane / 6)
        (ctaY L (t / L.block) * 6 + laneRow (tcDataCell L t sh a j).lane % 6)
        ((tcDataCell L t sh a j).column - 256)).o))
    (hs : 0 < Q.scale) (EF : EpiEntryFacts Q L X) :
    ∀ r < Q.b, ∀ s < Q.splits, ∀ tok < Q.qLen r, ∀ h < heads, ∀ d < headDim,
      StoredWord X (oLoc Q s (Q.qStart r + tok) h d)
        (if Q.numIters r s = 0 then b32 0 else Value.float .f32 (oPart Q r s tok h d)) := by
  intro r hr s hs' tok ht h hh d hd
  obtain ⟨g, hg, lane, hz, hx, hy, htok, hrm, hbit⟩ := pick_thread hp hr hs' ht
    (by simpa [heads] using hh) (by simpa [headDim] using hd)
  have hv := pick_valid hp hr ht hz htok hrm
  obtain ⟨c1, -⟩ := Epilogue.Export.store_visit hp hX hc (hcl g) hg lane hv
  obtain ⟨k, a, bs, he⟩ := c1 ⟨d % 64, by omega⟩
  dsimp only at he
  obtain ⟨-, vt, sz, loc⟩ := Export.store_address hp hX hf he (Or.inr ⟨⟨d % 64, by omega⟩, rfl⟩)
  have hloc : a.loc = oLoc Q s (Q.qStart r + tok) h d := by
    rcases loc with ⟨j', hpc, hl⟩ | ⟨hpc, -, -⟩
    · have hj' : j'.val = d % 64 := by omega
      rw [hl]
      exact oloc_pick hz hx hy htok hrm hbit hj'
    · omega
  refine ⟨⟨_, 2751 + d % 64 + d % 64 / 2, a, bs, he, hloc, sz⟩, ?_⟩
  intro j' hj' i pc a' bs' he' site cov'
  obtain ⟨gi, ki⟩ := i
  have ca : a.Covers ((oLoc Q s (Q.qStart r + tok) h d).at j') := by
    simp [Acc.Covers, Loc.InRange, Loc.at, hloc, sz, hj']
  have site0 : Shared.IsStoreSite (2751 + d % 64 + d % 64 / 2) := .inr ⟨⟨d % 64, by omega⟩, rfl⟩
  obtain ⟨hgg, hfp⟩ := Shared.store_pair hp hX hf he he' site0 (site_of site) ca cov'
  subst hgg
  obtain ⟨-, vt', sz', loc'⟩ := Export.store_address hp hX hf he' (site_of site)
  have hl0 : a'.loc = oLoc Q s (Q.qStart r + tok) h d := hfp.1.symm.trans hloc
  rcases loc' with ⟨jj, hpc', hl'⟩ | ⟨hpc', -, hl'⟩
  · have eq : oLoc Q ((L.ctaidOf (g / L.block)).get .x)
        (Q.qStart ((L.ctaidOf (g / L.block)).get .z) + Lib.tokM (g % L.block))
        ((L.ctaidOf (g / L.block)).get .y * 6 + Lib.rowM (g % L.block) % 6)
        (64 * (g % L.block / 16 % 2) + jj.val) = oLoc Q s (Q.qStart r + tok) h d :=
      hl'.symm.trans hl0
    have hjj : jj.val = d % 64 := by
      have hh2 := congrArg Loc.addr eq
      have hh3 := congrArg Loc.addr (oloc_pick (Q := Q) (j := d % 64) hz hx hy htok hrm hbit rfl)
      simp only [oLoc] at hh2 hh3
      omega
    rw [hpc'] at he'
    have hbs := out_bytes hp hX hf base final hs EF hg lane hz hx hy htok hrm hbit hv hjj he'
    have hb : (if Q.numIters r s = 0 then b32 0 else Value.float .f32 (oPart Q r s tok h d)).bytes
        = 4 := by
      by_cases hn : Q.numIters r s = 0 <;> simp [hn, Value.bytes, FloatFmt.bytes, b32]
    unfold wbyte
    rw [hl0]
    simp only [Loc.at, Nat.add_sub_cancel_left]
    rw [hbs]
    exact toBytes_get hb hj'
  · exfalso
    have bx := (Lib.coordinate_bounds hp hg).1
    have bz := (Lib.coordinate_bounds hp hg).2.2
    have by1 := (Lib.coordinate_bounds hp hg).2.1
    have r0 := Lib.rowM_lt (g % L.block)
    have r1 := Lib.lseLoc_range (Q := Q) _ _ ((L.ctaidOf (g / L.block)).get .y * 6 +
      Lib.rowM (g % L.block) % 6) bx (Lib.token_lt hp bz vt')
      (by simp only [heads, kvHeads] at *; omega)
    have r2 := Lib.oLoc_range (Q := Q) s (Q.qStart r + tok) h d hs' (Lib.token_lt hp hr ht) hh hd
    rw [hl'.symm.trans hl0] at r1
    have ap := hp.oApartLse
    unfold Apart at ap
    omega

/-- A launch without a block has no key, so the row sum is zero. -/
theorem rowSum_empty (hp : Pre Q L m) {r s tok h : Nat} (hn : Q.numIters r s = 0) :
    rowSum Q r s tok h = 0 := by
  classical
  have none : keys Q r s tok = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k member
    obtain ⟨_, i, hi, _⟩ := (Lib.numIters_spec hp.splitsPos).mp (Finset.mem_filter.mp member).2.1
    omega
  simp [rowSum, none]

private theorem lse_bytes (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hs : 0 < Q.scale) (EF : EpiEntryFacts Q L X)
    {g r s tok h : Nat} (hg : g < L.threads) (lane : g % L.block < 128)
    (hz : ctaZ L (g / L.block) = r) (hx : ctaXc L (g / L.block) = s)
    (hy : ctaY L (g / L.block) = h / 6) (htok : Lib.tokM (g % L.block) = tok)
    (hrm : Lib.rowM (g % L.block) % 6 = h % 6)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block)))
    {k : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨2682, .wr a bs⟩) :
    bs = (if rowSum Q r s tok h = 0 then (FVal.inf true).toValue .f32
      else Value.float .f32 (lsePart Q r s tok h)).toBytes := by
  have hnr : cellIters Q L g = Q.numIters r s := by
    show Q.numIters (ctaZ L (g / L.block)) (ctaXc L (g / L.block)) = _
    rw [hz, hx]
  by_cases hn : Q.numIters r s = 0
  · simp only [rowSum_empty hp hn, ↓reduceIte]
    have hb0 : Lib.blocksOf Q L (g / L.block) = 0 := by
      show Q.numIters (ctaZ L (g / L.block)) (ctaXc L (g / L.block)) = 0
      rw [hz, hx]; exact hn
    have wait : EpiWait L X g true := by simpa [hb0] using epi_wait_of (g := g) hp hX hf
    exact lse_out_store_zero hX (EF.empty g hg lane hv (by rw [hnr]; exact hn)) wait
      setp_zero_bits he
  have hnp : 0 < cellIters Q L g := by rw [hnr]; omega
  have := lse_out_store (g := g) hX hp.splitsPos hs (z := ctaZ L (g / L.block))
    (x := ctaXc L (g / L.block)) (tok := Lib.tokM (g % L.block))
    (h := ctaY L (g / L.block) * 6 + Lib.rowM (g % L.block) % 6) (l := (rowK Q L g 0).l)
    (mr := (rowK Q L g 0).m.toReal) (kState_l_nonneg hs _ _ _ _ _) (EF.sum g hg lane hv hnp)
    (fun t ht hpc hpos => EF.scale g hg lane hv hnp t ht hpc hpos) (epi_wait_of hp hX hf) rfl
    (fun _ => rfl) he
  have e1 : h / 6 * 6 + h % 6 = h := by omega
  rw [hz, hx, htok, hy, hrm, e1] at this
  exact this

private theorem lseloc_pick {g r s tok h : Nat} (hz : ctaZ L (g / L.block) = r)
    (hx : ctaXc L (g / L.block) = s) (hy : ctaY L (g / L.block) = h / 6)
    (htok : Lib.tokM (g % L.block) = tok) (hrm : Lib.rowM (g % L.block) % 6 = h % 6) :
    lseLoc Q ((L.ctaidOf (g / L.block)).get .x)
      (Q.qStart ((L.ctaidOf (g / L.block)).get .z) + Lib.tokM (g % L.block))
      ((L.ctaidOf (g / L.block)).get .y * 6 + Lib.rowM (g % L.block) % 6) =
      lseLoc Q s (Q.qStart r + tok) h := by
  have e1 : h / 6 * 6 + h % 6 = h := by omega
  change lseLoc Q (ctaXc L (g / L.block)) (Q.qStart (ctaZ L (g / L.block)) + _)
    (ctaY L (g / L.block) * 6 + _) = _
  rw [hz, hx, hy, htok, hrm, e1]

/-- **Every word of `LsePart` is stored, and every epilogue store that overlaps one of its bytes
writes that byte of it.** -/
theorem lse_rest (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hc : Complete L X) (hcl : ∀ g, ¬ ClcCanceled L X g)
    (hs : 0 < Q.scale) (EF : EpiEntryFacts Q L X) :
    ∀ r < Q.b, ∀ s < Q.splits, ∀ tok < Q.qLen r, ∀ h < heads,
      StoredWord X (lseLoc Q s (Q.qStart r + tok) h)
        (if rowSum Q r s tok h = 0 then (FVal.inf true).toValue .f32
          else Value.float .f32 (lsePart Q r s tok h)) := by
  intro r hr s hs' tok ht h hh
  obtain ⟨g, hg, lane, hz, hx, hy, htok, hrm, hbit⟩ := pick_thread hp hr hs' ht
    (by simpa [heads] using hh) (d := 0) (by omega)
  have hv := pick_valid hp hr ht hz htok hrm
  obtain ⟨-, c2⟩ := Epilogue.Export.store_visit hp hX hc (hcl g) hg lane hv
  obtain ⟨k, a, bs, he⟩ := c2 (by omega)
  obtain ⟨-, vt, sz, loc⟩ := Export.store_address hp hX hf he (Or.inl rfl)
  have hloc : a.loc = lseLoc Q s (Q.qStart r + tok) h := by
    rcases loc with ⟨j', hpc, -⟩ | ⟨-, -, hl⟩
    · omega
    · rw [hl]; exact lseloc_pick hz hx hy htok hrm
  refine ⟨⟨_, 2682, a, bs, he, hloc, sz⟩, ?_⟩
  intro j' hj' i pc a' bs' he' site cov'
  obtain ⟨gi, ki⟩ := i
  have ca : a.Covers ((lseLoc Q s (Q.qStart r + tok) h).at j') := by
    simp [Acc.Covers, Loc.InRange, Loc.at, hloc, sz, hj']
  have site0 : Shared.IsStoreSite 2682 := .inl rfl
  obtain ⟨hgg, hfp⟩ := Shared.store_pair hp hX hf he he' site0 (site_of site) ca cov'
  subst hgg
  obtain ⟨-, vt', sz', loc'⟩ := Export.store_address hp hX hf he' (site_of site)
  have hl0 : a'.loc = lseLoc Q s (Q.qStart r + tok) h := hfp.1.symm.trans hloc
  rcases loc' with ⟨jj, hpc', hl'⟩ | ⟨hpc', -, hl'⟩
  · exfalso
    have bx := (Lib.coordinate_bounds hp hg).1
    have bz := (Lib.coordinate_bounds hp hg).2.2
    have by1 := (Lib.coordinate_bounds hp hg).2.1
    have r0 := Lib.rowM_lt (g % L.block)
    have r1 := Lib.oLoc_range (Q := Q) _ _ ((L.ctaidOf (g / L.block)).get .y * 6 +
      Lib.rowM (g % L.block) % 6) (64 * (g % L.block / 16 % 2) + jj.val) bx
      (Lib.token_lt hp bz vt') (by simp only [heads, kvHeads] at *; omega)
      (by have := jj.isLt; simp only [headDim]; omega)
    have r2 := Lib.lseLoc_range (Q := Q) s (Q.qStart r + tok) h hs' (Lib.token_lt hp hr ht) hh
    rw [hl'.symm.trans hl0] at r1
    have ap := hp.oApartLse
    unfold Apart at ap
    omega
  · rw [hpc'] at he'
    have hbs := lse_bytes hp hX hf hs EF hg lane hz hx hy htok hrm hv he'
    have hb : (if rowSum Q r s tok h = 0 then (FVal.inf true).toValue .f32
        else Value.float .f32 (lsePart Q r s tok h)).bytes = 4 := by
      by_cases hn : rowSum Q r s tok h = 0
      · simp [hn]
        decide
      · simp [hn, Value.bytes, FloatFmt.bytes]
    unfold wbyte
    rw [hl0]
    simp only [Loc.at, Nat.add_sub_cancel_left]
    rw [hbs]
    exact toBytes_get hb hj'

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
