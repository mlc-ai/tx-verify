-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MaxTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingPairHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxBarriers
import Lemmas.Flow.NthEv
import Lemmas.Order.Order

@[expose] public section

/-! # The same-block local maximum observed by the actual peer read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0MaxReadback

open PTX PTX.Proof PTX.Flow Wg0 MachineTracking

private instance : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i : Nat} {d : D} {a : Acc} {values : List (Option Byte)}

/-- The other half's lane shares the CTA and its four-byte row slot is found by toggling bit 6. -/
theorem partner_geometry (hpre : Pre P L mem0)
    (hg : g < L.threads) (hw : warpOf L g < 4) :
    let w := Wg0PeerSources.partner L g
    SameCta L w g ∧ wgOf L w = 0 ∧ tidOf L w % 128 = tidOf L g % 128 ^^^ 64 := by
  let w := Wg0PeerSources.partner L g
  have htid : tidOf L g < 128 := by unfold warpOf at hw; omega
  have hbits : ∀ t : Fin 128,
      32 * (t.val / 32 ^^^ 2) + t.val % 32 = t.val ^^^ 64 ∧ t.val ^^^ 64 < 128 := by
    decide
  have hb := hbits ⟨tidOf L g, htid⟩
  change 32 * (warpOf L g ^^^ 2) + laneOf L g = tidOf L g ^^^ 64 ∧
    tidOf L g ^^^ 64 < 128 at hb
  let t := tidOf L g ^^^ 64
  have ht : t < L.block := by rw [hpre.block]; exact hb.2.trans (by decide)
  have hw' : w = ctaOf L g * L.block + t := by unfold w Wg0PeerSources.partner; rw [hb.1]
  have hcta : ctaOf L w = ctaOf L g := by
    rw [hw']
    change (ctaOf L g * L.block + t) / L.block = _
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt ht),
      Nat.div_eq_of_lt ht, Nat.zero_add]
  have hwTid : tidOf L w = t := by
    rw [tidOf_eq hpre, hw', hpre.block, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (hb.2.trans (by decide))]
  refine ⟨⟨?_, hg, hcta⟩, ?_, ?_⟩
  · change w < L.threads
    rw [hw']
    exact NamedBar.cta_thread_lt (NamedBar.cta_lt hg) ht
  · unfold wgOf
    rw [hwTid, Nat.div_eq_of_lt hb.2]
  · rw [hwTid, Nat.mod_eq_of_lt hb.2, Nat.mod_eq_of_lt htid]

private theorem same_blocks (hc : SameCta L g i) : blocksOf P L g = blocksOf P L i := by
  have h : ctaOf L g = ctaOf L i := hc.2.2
  simp only [blocksOf, eOf, ctaidY, h]

section
variable {cut : Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .maxRead)
    (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
include hpre hX hs hr hd hsite hCut hLen

/-- The peer maximum is written at the same four-byte address by the paired lane, and the
block's second 128-thread barrier orders that actual write before the read. -/
theorem actual_source_of_read (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t) :
    let w := Wg0PeerSources.partner L g
    ∃ j q fp tag, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .rowMax ∧ q.block = d.block ∧ X.Writes (w, j) fp (rowLocalMax L q).toBytes ∧
      fp.loc = a.loc ∧ fp.size = 4 ∧ a.size = 4 ∧ baseCausality L X (w, j) (g, i) ∧
      X.IsBarrier (w, j + 1) 9 (some 128) tag ∧
      ((X.tr w).take (j + 1)).countP (Execution.isBarId 9) = 2 * d.block + 1 := by
  dsimp only
  let w := Wg0PeerSources.partner L g
  have he := hr.choose_spec
  have hg := Frame.lt_of_get hX he
  have hi : i < (X.tr g).length := PTX.len_of_get he
  obtain ⟨hLoc, hSize, hinv⟩ := Wg0MaxWrites.read_geometry hpre hX hs hr hd hsite
  obtain ⟨hc, hwg, htid⟩ := partner_geometry hpre hg hinv.warpLt
  change SameCta L w g at hc
  change wgOf L w = 0 at hwg
  change tidOf L w % 128 = tidOf L g % 128 ^^^ 64 at htid
  have hw := hc.1
  obtain ⟨rb, r, rt, hrb, hrs, hrBlock, hR, hReadBar⟩ :=
    Wg0MaxTrace.barrier_before_maxRead hpre hX hs hg (Nat.le_of_lt hi) hd hsite
  have hReaderCount := Wg0BarrierCount.rowMaxCount hpre hX (hs g hg).machine hReadBar hR (.inr hrs)
  rw [hrBlock] at hReaderCount
  have hPassed : rb + 1 < (X.tr g).length := by omega
  have hPART : (w % L.block) / 32 ∈ OutputPublication.stagingWarps := by
    have hWarp : warpOf L w < 4 := by unfold wgOf at hwg; unfold warpOf; omega
    simpa only [OutputPublication.stagingWarps, Finset.mem_range, warpOf, tidOf_eq hpre,
      hpre.block] using hWarp
  have hExit (hex : ∃ k tag, X.get (w, k) = some ⟨tag, .exit⟩) :
      ∃ wb wt, X.IsBarrier (w, wb) 9 (some 128) wt ∧
        ((X.tr w).take wb).countP (Execution.isBarId 9) =
          ((X.tr g).take rb).countP (Execution.isBarId 9) := by
    obtain ⟨k, tag, hget⟩ := hex
    have hCount := (barrier_counts_before_softmax_exit hpre hX hs hwg hget).2
    rw [same_blocks hc] at hCount
    have hlt : 2 * d.block + 1 < ((X.tr w).take k).countP (Execution.isBarId 9) := by
      have := hinv.blockLt
      omega
    obtain ⟨wb, eb, _, hGet, hIs, hOrd⟩ := exists_nthEv hlt
    obtain ⟨wt, cnt, mode, hKind⟩ := NamedBar.isBarId_form hIs
    rw [hKind] at hGet
    obtain ⟨_, hCnt, hMode⟩ := actual_bar9 hpre hX hs hGet
    rw [hCnt, hMode] at hGet
    exact ⟨wb, wt, hGet, hOrd.trans hReaderCount.symm⟩
  have hSources := OutputPublication.actual_sources hpre hX hs
  obtain ⟨wb, wt, hWriteBar, hOrd⟩ :=
    hSources.member_arrival hX (OutputPublication.shape hpre) hReadBar hPassed hc.2.2 hPART hExit
  have hFollow : Frame.stateAt (Machine.code P L) X w wb ≠ some none := by
    intro hBad
    obtain ⟨j, hj, hDismiss⟩ := prior_dismissal (PTX.len_of_get hWriteBar).le hBad
    exact hPrior (w, j) (hSources.same_ordinal_baseCausality hX (OutputPublication.shape hpre)
      hc hWriteBar hReadBar hPassed hOrd hj (by omega) hLen) hDismiss
  obtain ⟨s, hS, hss, hb⟩ :=
    Wg0BarrierCount.maxBarrier_of_followed_ordinal hpre hX (hs w hw).machine hFollow
      hWriteBar rfl (by rw [same_blocks hc]; exact hinv.blockLt) (hOrd.trans hReaderCount)
  have hwLen := PTX.len_of_get hWriteBar
  obtain ⟨j, q, fp, hj, hqs, hqBlock, hQ, hWrite, hfpSize, hfpLoc⟩ :=
    Wg0MaxTrace.rowMax_before_barrier hpre hX hs hw (Nat.le_of_lt hwLen) hS hss
  have hCta : ctaOf L w = ctaOf L g := hc.2.2
  have hSameLoc : fp.loc = a.loc := by
    rw [hfpLoc, hLoc, htid]
    simp only [shLoc, hCta]
  have hOrder := hSources.same_ordinal_baseCausality hX (OutputPublication.shape hpre) hc
    hWriteBar hReadBar hPassed hOrd (show j < wb by omega) (show rb < i by omega) hi
  change j + 1 = wb at hj
  refine ⟨j, q, fp, wt, hQ, hqs, hqBlock.trans hb, hWrite, hSameLoc, hfpSize, hSize, hOrder,
    ?_, ?_⟩
  · rwa [hj]
  · rw [hj]
    exact hOrd.trans hReaderCount

omit hpre hX hs hr hd hsite hCut hLen in
/-- The partner of an actual row-maximum read in a tracked execution. -/
theorem source_of_read (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maxRead) :
    let w := Wg0PeerSources.partner L g
    ∃ j q fp tag, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .rowMax ∧ q.block = d.block ∧ X.Writes (w, j) fp (rowLocalMax L q).toBytes ∧
      fp.loc = a.loc ∧ fp.size = 4 ∧ a.size = 4 ∧ baseCausality L X (w, j) (g, i) ∧
      X.IsBarrier (w, j + 1) 9 (some 128) tag ∧
      ((X.tr w).take (j + 1)).countP (Execution.isBarId 9) = 2 * d.block + 1 :=
  actual_source_of_read hpre hX hs hr hd hsite le_rfl (PTX.len_of_get hr.choose_spec)
    (fun t _ => tracked_not_dismisses hX ht t)

omit hpre hX hs hr hd hsite hCut hLen in
/-- Two overlapping writes in the row buffer come from the same softmax lane. -/
theorem word_overlap {s w : Nat} {f fp : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hs : warpOf L s < 4) (hw : wgOf L w = 0)
    (hLoc : f.loc = shLoc L s (rowMaxBase + 4 * (tidOf L s % 128)))
    (hLoc' : fp.loc = shLoc L w (rowMaxBase + 4 * (tidOf L w % 128)))
    (hsize : f.size = 4) (hsize' : fp.size = 4) (hf : f.Covers l) (hfp : fp.Covers l) : s = w := by
  obtain ⟨_, hcta, hl, hu⟩ := hf
  obtain ⟨_, hcta', hl', hu'⟩ := hfp
  rw [hLoc] at hcta hl hu
  rw [hLoc'] at hcta' hl' hu'
  rw [hsize] at hu
  rw [hsize'] at hu'
  simp only [shLoc, rowMaxBase] at hcta hl hu hcta' hl' hu'
  have htidS : tidOf L s < 128 := by unfold warpOf at hs; omega
  have htidW : tidOf L w < 128 := by unfold wgOf at hw; omega
  rw [Nat.mod_eq_of_lt htidS] at hl hu
  rw [Nat.mod_eq_of_lt htidW] at hl' hu'
  have htid : tidOf L s = tidOf L w := by omega
  have hCta := hcta.symm.trans hcta'
  rw [tidOf_eq hpre, tidOf_eq hpre] at htid
  unfold ctaOf at hCta
  rw [hpre.block] at hCta
  omega

omit hpre hX hs hr hd hsite hCut hLen in
/-- An overlapping source is the paired write, an older write hidden by it, or a later
write ordered after the read. The later row sum is included in this exclusion. -/
theorem competing_write_order (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maxRead)
    {j tag k : Nat} {fp f : Acc} {bytes bs : List Byte} {other : AsyncCopy.Ref}
    (hw : X.Writes (Wg0PeerSources.partner L g, j) fp bytes)
    (hLoc : fp.loc = a.loc) (hsize : fp.size = 4)
    (hBar : X.IsBarrier (Wg0PeerSources.partner L g, j + 1) 9 (some 128) tag)
    (hCount : ((X.tr (Wg0PeerSources.partner L g)).take (j + 1)).countP
      (Execution.isBarId 9) = 2 * d.block + 1)
    (hk : k < a.size) (hm : X.MemWrites other f bs) (hf : f.Covers (a.loc.at k)) :
    other = .thread (Wg0PeerSources.partner L g, j) ∨
      ByteCausality L X (a.loc.at k) other (.thread (Wg0PeerSources.partner L g, j)) ∨
      ByteCausality L X (a.loc.at k) (.thread (g, i)) other := by
  let w := Wg0PeerSources.partner L g
  let l := a.loc.at k
  have hg := Frame.lt_of_get hX hr.choose_spec
  obtain ⟨ha, haz, hinv⟩ := Wg0MaxWrites.read_geometry hpre hX hs hr hd hsite
  obtain ⟨hC, hwg, hTid⟩ := partner_geometry hpre hg hinv.warpLt
  change SameCta L w g at hC
  change wgOf L w = 0 at hwg
  change tidOf L w % 128 = _ at hTid
  have hCta : ctaOf L w = ctaOf L g := hC.2.2
  have hfpLoc : fp.loc = shLoc L w (rowMaxBase + 4 * (tidOf L w % 128)) := by
    rw [hLoc, ha, hTid]
    simp only [shLoc, hCta]
  have hsh : l.space = .shared := by simp [l, Loc.at, ha, shLoc]
  have hlo : L.sharedBase + 221184 ≤ l.addr := by
    simp only [l, Loc.at, ha, shLoc, rowMaxBase]
    omega
  have hhi : l.addr < L.sharedBase + 221696 := by
    have hbits : ∀ t : Fin 128, t.val ^^^ 64 < 128 := by decide
    have hx := hbits ⟨tidOf L g % 128, Nat.mod_lt _ (by decide)⟩
    simp only [l, Loc.at, ha, shLoc, rowMaxBase]
    rw [haz] at hk
    omega
  have hcov : fp.Covers l := by
    rw [haz] at hk
    simp only [l, hLoc, Loc.at, Acc.Covers, Loc.InRange, hsize, true_and]
    omega
  obtain ⟨s, t, rfl, hwr, hWarp, hfSize, hfLoc, m, hWriterCount⟩ :=
    Wg0MaxWrites.actual_covered_write hpre hX hs hm hf hsh hlo hhi
  have heq : s = w := word_overlap hpre hWarp hwg hfLoc hfpLoc hfSize hsize hf hcov
  subst s
  have hwrGet := hwr.choose_spec
  rcases lt_trichotomy t j with hBefore | rfl | hAfter
  · refine .inr (.inl (.direct (.inl (.single (.inl ?_)))))
    exact po_of_overlap (.inr (.inl ⟨_, hwr, rfl⟩)) (.inr (.inl ⟨_, hw, rfl⟩))
      rfl hBefore ⟨l, hf, hcov⟩
  · exact .inl rfl
  · have hneq : t ≠ j + 1 := by
      intro h
      subst t
      have heq := congrArg Event.kind (Option.some.inj (hwrGet.symm.trans hBar))
      cases heq
    have hMono := countP_take_mono (Execution.isBarId 9) (X.tr w)
      (show j + 2 ≤ t by omega)
    have hStep := countP_take_succ hBar
      (show Execution.isBarId 9 ⟨tag, .bar 9 (some 128) .sync⟩ = true from rfl)
    change ((X.tr w).take (j + 2)).countP (Execution.isBarId 9) =
      ((X.tr w).take (j + 1)).countP (Execution.isBarId 9) + 1 at hStep
    rw [hStep, hCount] at hMono
    have hCCount : 2 * d.block + 2 < ((X.tr w).take t).countP (Execution.isBarId 9) := by
      omega
    have hReadCount := Wg0BarrierCount.maxReadCount hpre hX (hs g hg).machine hr.choose_spec hd
      (.inl hsite)
    have hne : d.site ≠ .lseStore0 := by rw [hsite]; intro h; cases h
    rw [ite_eq_right hne] at hReadCount
    have hwg' : wgOf L g = 0 := by
      have h := hinv.warpLt
      unfold warpOf at h
      unfold wgOf
      omega
    refine .inr (.inr (.direct (.inl (Wg0PeerReadback.order_of_bar9_counts hpre hX hs
      ⟨hg, hC.1, hC.2.2.symm⟩ hinv.warpLt hwg' hr.choose_spec hwrGet rfl ?_ ?_))))
    · rw [hReadCount]
      exact hCCount
    · rw [hReadCount]
      have := hinv.blockLt
      omega

/-- All four bytes of the actual read take the matching shared write as their source. -/
theorem actual_readback_bytes (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t) :
    let w := Wg0PeerSources.partner L g
    ∃ j q fp, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .rowMax ∧ q.block = d.block ∧ X.Writes (w, j) fp (rowLocalMax L q).toBytes ∧
      baseCausality L X (w, j) (g, i) ∧
      fp.loc = a.loc ∧ (∀ k < 4, X.rf (.thread (g, i)) k = some (.thread (w, j))) ∧
      values = (rowLocalMax L q).toBytes.map some := by
  let w := Wg0PeerSources.partner L g
  obtain ⟨j, q, fp, tag, hq, hqs, hblock, hw, hloc, hsize, haz, hv, hbar, hcount⟩ :=
    actual_source_of_read hpre hX hs hr hd hsite hCut hLen hPrior
  let raw := (rowLocalMax L q).toBytes
  have hlen : raw.length = 4 := by
    simp only [raw, Value.toBytes, List.length_map, List.length_range,
      (Wg0MaxWrites.rowLocalMax_scalar L q).1]
  have hmem : X.MemReads (.thread (g, i)) a values := .inl hr
  have hrf := hX.rf (.thread (g, i)) a values hmem
  have hbyte k (hk : k < 4) :
      X.rf (.thread (g, i)) k = some (.thread (w, j)) ∧
      values[k]? = (raw.map some)[k]? := by
    have hka : k < a.size := haz ▸ hk
    have hcov : fp.Covers (a.loc.at k) := by
      simp only [hloc, Loc.at, Acc.Covers, Loc.InRange, hsize, true_and]
      omega
    have hVisible : ByteCausality L X (a.loc.at k) (.thread (w, j)) (.thread (g, i)) :=
      .direct (.inl hv)
    have hWrite : X.MemWrites (.thread (w, j)) fp raw := .inl hw
    have hh := hX.hidden _ _ _ k _ _ _ hmem hka hWrite hcov hVisible
    have hRf := hrf.2 k hka
    cases hsrc : X.rf (.thread (g, i)) k with
    | none => rw [hsrc] at hh; exact hh.elim
    | some other =>
      rw [hsrc] at hRf hh
      obtain ⟨f, bs, hOther, hc, hValue⟩ := hRf
      rcases competing_write_order hpre hX hs hr hd hsite hw hloc hsize hbar hcount hka
          hOther hc with heq | hBefore | hAfter
      · subst other
        obtain ⟨hFootprint, hBytes⟩ := hOther.unique hWrite
        have hidx : (a.loc.at k).addr - fp.loc.addr = k := by simp [hloc, Loc.at]
        have hRaw : raw[k]? = some (raw[k]'(by omega)) := List.getElem?_eq_getElem (by omega)
        refine ⟨rfl, ?_⟩
        simpa only [wbyte, hFootprint.1, hBytes, hidx, List.getElem?_map, hRaw, Option.map_some]
          using hValue
      · exact (hh hBefore).elim
      · exact (hX.noFuture _ _ _ k other hmem hka hsrc hAfter).elim
  refine ⟨j, q, fp, hq, hqs, hblock, hw, hv, hloc, fun k hk => (hbyte k hk).1, ?_⟩
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 4
  · exact (hbyte k hk).2
  · have hvlen := hrf.1.trans haz
    rw [List.getElem?_eq_none (by omega : values.length ≤ k)]
    exact (List.getElem?_eq_none (by rw [List.length_map, hlen]; omega)).symm

/-- The actual peer load rebuilds to the local maximum of the paired lane in the same block. -/
theorem actual_readback_value (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t) :
    let w := Wg0PeerSources.partner L g
    ∃ j q fp, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .rowMax ∧ q.block = d.block ∧ X.Writes (w, j) fp (rowLocalMax L q).toBytes ∧
      baseCausality L X (w, j) (g, i) ∧
      rebuild 3 values = .ok (rowLocalMax L q) := by
  obtain ⟨j, q, fp, hq, hqs, hb, hw, hv, _, _, hb'⟩ :=
    actual_readback_bytes hpre hX hs hr hd hsite hCut hLen hPrior
  refine ⟨j, q, fp, hq, hqs, hb, hw, hv, ?_⟩
  rw [hb']
  exact (Wg0MaxWrites.rowLocalMax_scalar L q).2
end

/-- The readback in a tracked execution. -/
theorem readback_value (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maxRead) :
    let w := Wg0PeerSources.partner L g
    ∃ j q fp, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .rowMax ∧ q.block = d.block ∧ X.Writes (w, j) fp (rowLocalMax L q).toBytes ∧
      rebuild 3 values = .ok (rowLocalMax L q) := by
  obtain ⟨j, q, fp, hq, hqs, hb, hw, _, hWord⟩ :=
    actual_readback_value hpre hX hs hr hd hsite le_rfl (PTX.len_of_get hr.choose_spec)
      (fun t _ => tracked_not_dismisses hX ht t)
  exact ⟨j, q, fp, hq, hqs, hb, hw, hWord⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0MaxReadback
