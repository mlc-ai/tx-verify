-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0MaxReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MaxTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingPairHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxBarriers
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Lemmas.Async.ReadReuse
import Lemmas.Flow.AllocTmpl
import Lemmas.Flow.MemTmpl
import Lemmas.Flow.NthEv
import Lemmas.Order.ReadLast

@[expose] public section

/-! # The paired half-sum observed by the actual LSE read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0LseReadback

open PTX PTX.Proof PTX.Flow Wg0 Wg0BarrierCount MachineTracking
noncomputable section

private instance : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i : Nat} {d : D} {a : Acc} {values : List (Option Byte)}

private def halfSumWord (q : D) : Value :=
  if q.peak = ⊥ then b32 0 else halfSumVal q

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
include hpre hX hs

private theorem read_geometry (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    :
    a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128 ^^^ 64)) ∧ a.size = 4 ∧
      Inv P L g d := by
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_site hs hX hr.choose_spec hd
  cases o with
  | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    obtain ⟨fp, _, hk, hloc, hz, _, _⟩ := fires_lseRead hpre hsite hat hinv hcode hf
    have hfp := (Kind.rd.inj hk).1
    exact ⟨(congrArg Acc.loc hfp).trans hloc, (congrArg Acc.size hfp).trans hz, hinv⟩

omit hpre hX hs in
private theorem same_blocks {w : Nat} (hc : SameCta L w g) :
    blocksOf P L w = blocksOf P L g := by
  have h : ctaOf L w = ctaOf L g := hc.2.2
  simp only [blocksOf, eOf, ctaidY, h]

omit hpre hX hs in
private theorem sum_barrier_of_count {w j tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L w).Sound)
    (hFollow : Frame.stateAt (Machine.code P L) X w j ≠ some none)
    (he : X.IsBarrier (w, j) 9 (some 128) tag)
    (hc : ((X.tr w).take j).countP (Execution.isBarId 9) = 2 * blocksOf P L w + 1) :
    ∃ q, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .lseBar2 ∧ q.block + 1 = blocksOf P L w := by
  obtain ⟨role, _, hq, hf⟩ :=
    RingSourceSites.fired_at_followed hX hs hFollow he (by simp)
  obtain ⟨q, rfl, hbar, _, _, _⟩ := Wg0BarrierTrace.bar9_fired hpre hf rfl
  have hcount := count_at_wg0 hpre hX hs he hq
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, ⟨_, hInv⟩, _⟩ := (hs.produces (hX.thr w hg)).fired_at he hq
  rw [hc] at hcount
  refine ⟨q, hq, ?_⟩
  have hb : q.block < blocksOf P L w := hInv.blockLt
  cases hq' : q.site <;> simp only [Wg0BarrierTrace.Bar9Site, hq'] at hbar
  case lseBar2 =>
    simp only [ordinal, hq', localOrdinal] at hcount
    exact ⟨rfl, by omega⟩
  case epiBar tile =>
    have hLast := hInv.epilogueLast (by rw [hq']; rfl)
    simp only [ordinal, hq', localOrdinal] at hcount
    omega
  all_goals simp only [ordinal, hq', localOrdinal] at hcount
  all_goals omega

/-- The row-sum barrier publishes the paired lane's actual half-sum at the read address. -/
theorem actual_source_of_read (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    let w := Wg0PeerSources.partner L g
    ∃ j q fp tag, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .lseStore0 ∧ q.block = d.block ∧
      X.Writes (w, j) fp ((if q.peak = ⊥ then b32 0 else halfSumVal q).toBytes) ∧
      fp.loc = a.loc ∧ fp.size = 4 ∧ a.size = 4 ∧ baseCausality L X (w, j) (g, i) ∧
      X.IsBarrier (w, j + 1) 9 (some 128) tag ∧
      ((X.tr w).take (j + 1)).countP (Execution.isBarId 9) = 2 * blocksOf P L w + 1 ∧
      ∃ st, Frame.stateAt (Machine.code P L) X w (j + 1) = some (some (.wg0 st)) ∧
        st.site = .lseBar2 := by
  dsimp only
  let w := Wg0PeerSources.partner L g
  have he := hr.choose_spec
  have hg := Frame.lt_of_get hX he
  have hi : i < (X.tr g).length := PTX.len_of_get he
  obtain ⟨hLoc, hSize, hInv⟩ := read_geometry hpre hX hs hr hd hsite
  have hLast := hInv.epilogueLast (by rw [hsite]; rfl)
  obtain ⟨hc, hwg, htid⟩ := Wg0MaxReadback.partner_geometry hpre hg hInv.warpLt
  change SameCta L w g at hc
  change wgOf L w = 0 at hwg
  change tidOf L w % 128 = tidOf L g % 128 ^^^ 64 at htid
  have hw := hc.1
  obtain ⟨rb, r, rt, hrb, hrs, hrBlock, hR, hReadBar⟩ :=
    Wg0MaxTrace.barrier_before_sumRead hpre hX hs hg hi.le hd hsite
  have hReaderCount := count_at_wg0 hpre hX (hs g hg).machine hReadBar hR
  simp only [ordinal, hrs, localOrdinal, hrBlock] at hReaderCount
  have hEq : 2 * d.block + 3 = 2 * blocksOf P L w + 1 := by
    rw [same_blocks hc]
    omega
  rw [hEq] at hReaderCount
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
    have hlt : 2 * blocksOf P L w + 1 < ((X.tr w).take k).countP (Execution.isBarId 9) := by
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
      hc hWriteBar hReadBar hPassed hOrd hj (by omega) hi) hDismiss
  obtain ⟨s, hS, hss, hb⟩ := sum_barrier_of_count hpre hX (hs w hw).machine hFollow hWriteBar
    (hOrd.trans hReaderCount)
  obtain ⟨j, q, fp, hj, hqs, hqBlock, hQ, hWrite, hfpSize, hfpLoc⟩ :=
    Wg0MaxTrace.halfSum_before_barrier hpre hX hs hw (PTX.len_of_get hWriteBar).le hS hss
  have hCta : ctaOf L w = ctaOf L g := hc.2.2
  have hSameLoc : fp.loc = a.loc := by
    rw [hfpLoc, hLoc, htid]
    simp only [shLoc, hCta]
  have hOrder := hSources.same_ordinal_baseCausality hX (OutputPublication.shape hpre) hc
    hWriteBar hReadBar hPassed hOrd (show j < wb by omega) (show rb < i by omega) hi
  have hBlock : q.block = d.block := by
    rw [same_blocks hc] at hb
    omega
  refine ⟨j, q, fp, wt, hQ, hqs, hBlock, hWrite, hSameLoc, hfpSize, hSize, hOrder, ?_, ?_, ?_⟩
  · rwa [hj]
  · rw [hj]
    exact hOrd.trans hReaderCount
  · rw [hj]
    exact ⟨s, hS, hss⟩

/-- The half-sum producer in a globally tracked execution. -/
theorem source_of_read (ht : Frame.Tracked (Machine.code P L) X) (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    :
    let w := Wg0PeerSources.partner L g
    ∃ j q fp tag, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .lseStore0 ∧ q.block = d.block ∧
      X.Writes (w, j) fp ((if q.peak = ⊥ then b32 0 else halfSumVal q).toBytes) ∧
      fp.loc = a.loc ∧ fp.size = 4 ∧ a.size = 4 ∧ baseCausality L X (w, j) (g, i) ∧
      X.IsBarrier (w, j + 1) 9 (some 128) tag ∧
      ((X.tr w).take (j + 1)).countP (Execution.isBarId 9) = 2 * blocksOf P L w + 1 := by
  obtain ⟨j, q, fp, tag, hq, hs', hb, hw, hLoc, hSize, hi, hv, hBar, hCount, _⟩ :=
    actual_source_of_read hpre hX hs hr hd hsite (fun t _ => tracked_not_dismisses hX ht t)
  exact ⟨j, q, fp, tag, hq, hs', hb, hw, hLoc, hSize, hi, hv, hBar, hCount⟩

private theorem competing_write_order (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    {j tag k : Nat} {fp f : Acc} {bytes bs : List Byte} {other : AsyncCopy.Ref}
    (hw : X.Writes (Wg0PeerSources.partner L g, j) fp bytes) (hLoc : fp.loc = a.loc)
    (hsize : fp.size = 4) (hBar : X.IsBarrier (Wg0PeerSources.partner L g, j + 1) 9 (some 128) tag)
    (hBarrierRole : ∃ st,
      Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) (j + 1) =
        some (some (.wg0 st)) ∧ st.site = .lseBar2) (hk : k < a.size) (hm : X.MemWrites other f bs)
    (hf : f.Covers (a.loc.at k)) :
    other = .thread (Wg0PeerSources.partner L g, j) ∨
      modelCausality L X (a.loc.at k) other (.thread (Wg0PeerSources.partner L g, j)) ∨
      modelCausality L X (a.loc.at k) (.thread (g, i)) other := by
  let w := Wg0PeerSources.partner L g
  let l := a.loc.at k
  have hg := Frame.lt_of_get hX hr.choose_spec
  obtain ⟨ha, haz, hinv⟩ := read_geometry hpre hX hs hr hd hsite
  obtain ⟨hC, hwg, hTid⟩ := Wg0MaxReadback.partner_geometry hpre hg hinv.warpLt
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
    have hXor := Nat.xor_lt_two_pow (n := 7) (Nat.mod_lt (tidOf L g) (by decide : 0 < 128))
      (by decide : 64 < 2 ^ 7)
    simp only [l, Loc.at, ha, shLoc, rowMaxBase]
    rw [haz] at hk
    omega
  have hcov : fp.Covers l := by
    rw [haz] at hk
    simp only [l, hLoc, Loc.at, Acc.Covers, Loc.InRange, hsize, true_and]
    omega
  obtain ⟨s, t, rfl, hwr, hWarp, hfSize, hfLoc, _⟩ :=
    Wg0MaxWrites.actual_covered_write hpre hX hs hm hf hsh hlo hhi
  have heq : s = w := Wg0MaxReadback.word_overlap hpre hWarp hwg
    hfLoc hfpLoc hfSize hsize hf hcov
  subst s
  have hwrGet := hwr.choose_spec
  rcases lt_trichotomy t j with hBefore | rfl | hAfter
  · refine .inr (.inl (.inl (.single (.inl ?_))))
    exact po_of_overlap (.inr (.inl ⟨_, hwr, rfl⟩)) (.inr (.inl ⟨_, hw, rfl⟩))
      rfl hBefore ⟨l, hf, hcov⟩
  · exact .inl rfl
  · have hneq : t ≠ j + 1 := by
      intro h
      subst t
      have heq := congrArg Event.kind (Option.some.inj (hwrGet.symm.trans hBar))
      cases heq
    obtain ⟨st, hSt, hSite⟩ := hBarrierRole
    exact (Wg0MaxWrites.no_row_write_after_sum_bar hpre hX hs hBar hSt hSite
      (by omega) hwr hf hsh hlo hhi).elim

omit hpre hX hs in
private theorem halfSum_word_size (q : D) : (halfSumWord q).bytes = 4 := by
  unfold halfSumWord halfSumVal
  split_ifs <;> rfl

omit hpre hX hs in
private theorem halfSum_word_rebuild (q : D) :
    (rebuild 3 ((halfSumWord q).toBytes.map some)).toOption.bind
      (fun v => (valFloat .f32 v).toOption) = some (lseOwnSum q) := by
  have hFloat : rebuild 3 ((fl q.lh).toBytes.map some) = .ok (fl q.lh) :=
    rebuild_scalar (by change 0 < 4; decide) rfl
  by_cases hPeak : q.peak = ⊥ <;> cases hSum : q.sumUpd <;>
    simp [halfSumWord, halfSumVal, lseOwnSum, hPeak, hSum, rebuild_b32, hFloat,
      valFloat_z0, valFloat_fl, Except.toOption]

/-- The read takes all four bytes from the paired lane's final half-sum and decodes that value. -/
theorem actual_readback_value (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    let w := Wg0PeerSources.partner L g
    ∃ j q fp, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .lseStore0 ∧ q.block = d.block ∧
      X.Writes (w, j) fp ((if q.peak = ⊥ then b32 0 else halfSumVal q).toBytes) ∧
      fp.loc = a.loc ∧ (∀ k < 4, X.rf (.thread (g, i)) k = some (.thread (w, j))) ∧
      baseCausality L X (w, j) (g, i) ∧
      (rebuild 3 values).toOption.bind (fun v => (valFloat .f32 v).toOption) =
        some (lseOwnSum q) := by
  let w := Wg0PeerSources.partner L g
  obtain ⟨j, q, fp, tag, hq, hqs, hblock, hw, hloc, hsize, haz, hv, hbar, _, hRole⟩ :=
    actual_source_of_read hpre hX hs hr hd hsite hPrior
  let raw := (halfSumWord q).toBytes
  have hlen : raw.length = a.size := by
    simp only [raw, Value.toBytes, List.length_map, List.length_range, halfSum_word_size, haz]
  have hread : X.MemReads (.thread (g, i)) a values := .inl hr
  have hwrite : X.MemWrites (.thread (w, j)) fp raw := .inl hw
  have horder k (hk : k < a.size) other footprint bytes
      (hwr : X.MemWrites other footprint bytes) (hc : footprint.Covers (a.loc.at k)) :=
    competing_write_order hpre hX hs hr hd hsite hw hloc hsize hbar hRole hk hwr hc
  have hval := read_of_last_write hX hread hwrite hloc (hsize.trans haz.symm) hlen
    (fun _ _ => .inl hv) horder
  refine ⟨j, q, fp, hq, hqs, hblock, hw, hloc, ?_, hv, ?_⟩
  · intro k hk
    have hka : k < a.size := haz ▸ hk
    have hcov : fp.Covers (a.loc.at k) := by
      simp only [hloc, Loc.at, Acc.Covers, Loc.InRange, hsize, true_and]
      omega
    exact read_rf_of_ordered_reuse hX hread hka hwrite hcov (.inl hv) (horder k hka)
  · rw [hval]
    exact halfSum_word_rebuild q

/-- The half-sum readback in a globally tracked execution. -/
theorem readback_value (ht : Frame.Tracked (Machine.code P L) X) (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    :
    let w := Wg0PeerSources.partner L g
    ∃ j q fp, Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .lseStore0 ∧ q.block = d.block ∧
      X.Writes (w, j) fp ((if q.peak = ⊥ then b32 0 else halfSumVal q).toBytes) ∧
      fp.loc = a.loc ∧ (∀ k < 4, X.rf (.thread (g, i)) k = some (.thread (w, j))) ∧
      (rebuild 3 values).toOption.bind (fun v => (valFloat .f32 v).toOption) =
        some (lseOwnSum q) := by
  obtain ⟨j, q, fp, hq, hqs, hb, hw, hLoc, hBytes, _, hDecode⟩ :=
    actual_readback_value hpre hX hs hr hd hsite (fun t _ => tracked_not_dismisses hX ht t)
  exact ⟨j, q, fp, hq, hqs, hb, hw, hLoc, hBytes, hDecode⟩

/-- The actual sum read advances with the two halves' total when that total is well formed. -/
theorem actual_next_of_row_total {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t)
    (hTotal : ∀ j (q : D) fp,
      Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j = some (some (.wg0 q)) →
      q.site = .lseStore0 → q.block = d.block →
      X.Writes (Wg0PeerSources.partner L g, j) fp
        ((if q.peak = ⊥ then b32 0 else halfSumVal q).toBytes) →
      baseCausality L X (Wg0PeerSources.partner L g, j) (g, i) →
      RowTotal { d with li := lseOwnSum d + lseOwnSum q }) :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d' : D, Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
        d'.site = (if tidOf L g % 128 < 64 then .lseStore else .svDone) ∧ RowTotal d' := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (Frame.trace hs hX hg).fired_at he hd
  cases o with
  | none => exact .inl (composed_ending_next hf)
  | some u =>
    obtain ⟨_, _, hat, hInv, hc, hFire⟩ := Frame.fired_site_of hs hg hf
    obtain ⟨a, bytes, hk, hLoc, hSize, _, _⟩ := fires_lseRead hpre hsite hat hInv hc hFire
    have hRead : X.Reads (g, i) a bytes := by
      cases e
      exact ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hk))⟩
    obtain ⟨j, q, fp, hq, hqs, hb, hw, _, _, hBefore, hDecode⟩ :=
      actual_readback_value hpre hX hs hRead hd hsite hPrior
    let d' : D := { d with
      site := if tidOf L g % 128 < 64 then .lseStore else .svDone
      sub := 0
      li := lseOwnSum d + lseOwnSum q
      lp := lseOwnSum q }
    have hRow : RowTotal d' := hTotal j q fp hq hqs hb hw hBefore
    refine .inr ⟨d', ?_, rfl, hRow⟩
    simp [Machine.next, Wg0.next, nextSite, hsite, hk, siteLoc, hLoc, hSize,
      Site.elemBytes, hDecode, show RowTotal _ from hRow, d']

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0LseReadback
