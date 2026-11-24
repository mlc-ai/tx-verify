-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputTmemReadSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmScoreRing
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvInitialAccumulator
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0GemmTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0RescaleGainTrace
import Lemmas.Tcgen05.TcProgramOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmemLoadWaits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The previous block's PV result supplying a rescale load -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RescaleTmemReadSource

open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy Wg0 OutputTmemReadSource
open Wg1Mma (pvDest tmemO)
open PvAccumulatorSource (Issue RescaleStore)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i ld issuer : Nat} {d : D} {tile : Fin 4} {reg : Fin 64}

/-- Any rescale site has observed the QK commit of its own block. -/
theorem actual_earlier_qk_in_rescale {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site.inRescale = true) (he : X.get (g, i) = some e) :
    let m := GemmRing.qk L (ctaOf L g) (rawSlot d.block)
    ∃ w wt parity c ct scope sp rank cd, w < i ∧
      X.get (g, w) = some ⟨wt, .wait m parity true true scope⟩ ∧
      X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧ TcCommit.target sp rank = some m ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma cd)) ∧
      ctaOf L issuer = ctaOf L g ∧ cd.i = d.block ∧
      Witness L X (.async (issuer, c) (.tcNotify rank)) (g, w) := by
  dsimp only
  let cta := ctaOf L g
  let slot := rawSlot d.block
  let m := GemmRing.qk L cta slot
  have hg := Frame.lt_of_get hX he
  let trace := (hs g hg).machine.produces (hX.thr g hg)
  have hCounts := (Wg0GemmTrace.composed_in_rescale_counts hpre trace hd hsite slot).2
  change okPolls m ((X.tr g).take i) = d.block / 2 + 1 at hCounts
  obtain ⟨w, wt, parity, acq, scope, hwi, hw, hOrdinal⟩ := MbarRing.Poll.exists_nth hCounts.ge
  obtain ⟨s, hs'⟩ := FollowedPrefix.state_at hd hwi.le
  obtain ⟨⟨_, q, hSlot, _, hQSite, hQ⟩, rfl⟩ :=
    GemmRing.poll_at_followed (obj := .qkDone) hpre hX (hs g hg).machine
      (by rw [hs']; simp) hw rfl
  have hQCount := Wg0GemmTrace.composed_qk_counts hpre trace hQ hQSite
  change q.block % 2 = d.block % 2 at hSlot
  rw [hSlot] at hQCount
  change okPolls m ((X.tr g).take w) = q.block / 2 at hQCount
  have hEq : q.block = d.block := by omega
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hw hQ
  have hInv : Wg0.Inv P L g q := hInv
  obtain ⟨lane, hLane⟩ := GemmRing.softmax_thread hpre (cta := cta) rfl hInv.wg
  have hQ' : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta lane) w =
      some (some (.wg0 q)) := by rwa [← hLane]
  have hw' : X.get (GemmRing.softmax L cta lane, w) =
      some ⟨wt, .wait (GemmRing.qk L cta (rawSlot q.block)) parity true true scope⟩ := by
    rw [← hLane, hEq]
    exact hw
  obtain ⟨c, ct, sp, rank, cd, hc, hTarget, hCD, hCta, _, hb, hObs⟩ :=
    ScoreReadback.commit_of_qk_wait hpre hX hs hmma hQ' hQSite hw'
  rw [hEq] at hTarget hb
  rw [← hLane] at hObs
  exact ⟨w, wt, parity, c, ct, scope, sp, rank, cd, hwi, hw, hc, hTarget, hCD, hCta, hb, hObs⟩

theorem earlier_qk_in_rescale {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site.inRescale = true) (he : X.get (g, i) = some e) :
    let m := GemmRing.qk L (ctaOf L g) (rawSlot d.block)
    ∃ w wt parity c ct scope sp rank cd, w < i ∧
      X.get (g, w) = some ⟨wt, .wait m parity true true scope⟩ ∧
      X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧ TcCommit.target sp rank = some m ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma cd)) ∧
      ctaOf L issuer = ctaOf L g ∧ cd.i = d.block ∧
      Witness L X (.async (issuer, c) (.tcNotify rank)) (g, w) :=
  actual_earlier_qk_in_rescale hpre hX hs hmma hd hsite he

private theorem wait_before_later_pv {tag j : Nat} {q : Wg1Mma.D} {k : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hCta : ctaOf L issuer = ctaOf L g)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile) (hwait : X.get (g, i) = some ⟨tag, .tc .waitLd⟩)
    (hld : ld < i)
    (hPV : Issue L X issuer j q.i k)
    (hq : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)))
    (hqSite : q.site = .pvMma k) (hBlock : d.block ≤ q.i) :
    TcMma.WaitBefore L X .waitLd (g, ld) (issuer, j) := by
  have hg := Frame.lt_of_get hX hwait
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hwait hd
  have hInv : Wg0.Inv P L g d := hInv
  obtain ⟨lane, hLane⟩ := GemmRing.softmax_thread hpre hCta.symm hInv.wg
  obtain ⟨a, atag, ha, hA, hBase⟩ :=
    PvProbabilitySource.actual_publication_before_pv hpre hX hs hPV.choose_spec hq hqSite lane
  rw [← hLane] at ha hBase hA
  let m := GemmRing.score L (ctaOf L issuer) (rawSlot q.i)
  let trace := (hs g hg).machine.produces (hX.thr g hg)
  have hArr := (Wg0GemmTrace.composed_in_rescale_counts hpre trace hd
    (by rw [hsite]; rfl) (rawSlot q.i)).1
  rw [← hCta] at hArr
  change arrivals m ((X.tr g).take i) = (d.block + (1 - q.i % 2)) / 2 at hArr
  change arrivals m ((X.tr g).take a) = q.i / 2 at hA
  have hge := PTX.MbarRing.arrival_index_ge ha (by simp [arrivesOn, sourceArrive, m]) hA
    (show arrivals m ((X.tr g).take i) ≤ q.i / 2 by rw [hArr]; omega)
  have hi : i < a := by
    by_contra! h
    have heq : i = a := by omega
    rw [← heq] at ha
    cases congrArg Event.kind (Option.some.inj (hwait.symm.trans ha))
  have hWaitBefore : baseCausality L X (g, i) (g, a) :=
    TcMma.baseCausality_of_tc_po hwait rfl hi (PTX.len_of_get ha)
  exact ⟨(g, i), ⟨tag, hwait⟩, rfl, hld, .inl (hWaitBefore.trans hBase)⟩

private theorem store_same_lane_tile {j t : Nat} {q : Wg0.D} {k : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hLane : tidOf L g < 128)
    (hstore : RescaleStore P L X t j (outputCell L g tile reg) q k) :
    t = g ∧ k = tile := by
  obtain ⟨hc, hl, hcol⟩ := PvInitialAccumulator.rescale_coordinates hpre hX hs hstore
  have hCell := outputCell_eq hpre hLane tile reg
  rw [hCell] at hc hl hcol
  change ctaOf L g = ctaOf L t at hc
  change tidOf L g = tidOf L t at hl
  change (64 * tile.val + reg.val) / 64 = k.val at hcol
  have hTile : k = tile := Fin.ext (by have := reg.isLt; omega)
  have htEq : t = g := by
    rw [tidOf_eq hpre, tidOf_eq hpre] at hl
    change g / L.block = t / L.block at hc
    rw [hpre.block] at hc
    omega
  exact ⟨htEq, hTile⟩

/-- Each word retained by a rescale wait reads the preceding block's last PV issue in its half. -/
theorem actual_previous_source_at_wait {tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile) (hwait : X.get (g, i) = some ⟨tag, .tc .waitLd⟩)
    (reg : Fin 64) :
    ∃ (ld src c ct : Nat) (sp : TcCommit.Spec) (rank : Fin 16),
      ld + 1 = i ∧ src < c ∧ X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧
      rank ∈ X.tcNotified (issuer, c) ∧
      Frame.stateAt (Machine.code P L) X issuer src =
        some (some (.mma ⟨.pvMma (lastIssue tile), d.block - 1⟩)) ∧
      Issue L X issuer src (d.block - 1) (lastIssue tile) ∧
      X.TLd (g, ld) (64 * tile.val) d.rescaleWords .s32x32b ∧ d.rescaleWords.length = 64 ∧
      TcMma.LoadCell L X (g, ld) reg.val (outputCell L g tile reg) ∧
      TcMma.ReadSource L X .ld (issuer, src) (g, ld) (outputCell L g tile reg) := by
  have hLen : i ≤ (X.tr g).length := (PTX.len_of_get hwait).le
  have hPos := Wg0RescaleGainTrace.rescale_block_pos hLen hd (by rw [hsite]; rfl)
  obtain ⟨ld, old, hIdx, hOld, hOldSite, _, hLoad, hWords⟩ :=
    Wg0RescaleGainTrace.load_before_wait hpre hX hs hLen hd hsite
  obtain ⟨w, wt, parity, c, ct, scope, sp, rank, cd, hwi, hw, hc, hTarget, hCD, hCta, hb, hObs⟩ :=
    actual_earlier_qk_in_rescale hpre hX hs hmma hd (by rw [hsite]; rfl) hwait
  obtain ⟨src, hSrcLt, hSrc, hIssue⟩ := PvInitialAccumulator.actual_prior_block_issue_before
    hpre hX hs hc hCD (hb.symm ▸ hPos) (lastIssue tile)
  rw [hb] at hSrc hIssue
  have hwLd : w < ld := by
    have hne : w ≠ ld := by
      rintro rfl
      cases congrArg Event.kind (Option.some.inj (hw.symm.trans hLoad.choose_spec))
    omega
  have hDone := done_before_of_observed hX hIssue hSrcLt hc hTarget hw hObs hCta hwLd hLoad
  have hReg : reg.val < d.rescaleWords.length := hWords.symm ▸ reg.isLt
  have hLoadCell : TcMma.LoadCell L X (g, ld) reg.val (outputCell L g tile reg) :=
    ⟨_, _, _, hLoad, hReg, rfl⟩
  have hLive : TcMma.SourceLive L X (issuer, src) (g, ld) (outputCell L g tile reg) :=
    ScoreLifetime.sourceLive_of_actual_load_wait hpre hX hs hLoadCell hd
      (by rw [hsite]; rfl) (by omega) hwait
  obtain ⟨_, _, _, _, hOldInv, _, _⟩ := Frame.fired_site hs hX hLoad.choose_spec hOld
  have hLane : tidOf L g < 128 := by
    have h := (show Wg0.Inv P L g old from hOldInv).warpLt
    unfold warpOf at h
    omega
  have hCell := outputCell_eq hpre hLane tile reg
  have hWrite := output_cell_written hpre hLane hCta tile reg hIssue
  have hCol : (outputCell L g tile reg).column < 256 := by
    rw [hCell]
    have := tile.isLt
    have := reg.isLt
    change 64 * tile.val + reg.val < 256
    omega
  have hColHalf : (outputCell L g tile reg).column / 128 = tile.val / 2 := by
    rw [hCell]
    have := reg.isLt
    change (64 * tile.val + reg.val) / 128 = tile.val / 2
    omega
  have hneq : (issuer, src) ≠ (g, ld) := by
    intro h
    obtain ⟨_, he⟩ := hIssue
    rw [h] at he
    cases congrArg Event.kind (Option.some.inj (he.symm.trans hLoad.choose_spec))
  refine ⟨ld, src, c, ct, sp, rank, hIdx, hSrcLt, hc, (hObs.waitObserves_tcNotify hw).1, hSrc,
    hIssue, hLoad, hWords, hLoadCell, ⟨hneq, .inl hWrite, .inl (.inl hDone), ?_, hLive⟩⟩
  rintro ⟨t, j⟩ hother
  obtain ⟨hOwner, hRole⟩ := PvAccumulatorSource.actual_output_writer hpre hX hs hCol hother
  have hCt : ctaOf L t = ctaOf L g := hOwner.symm.trans (congrArg TcMma.Cell.cta hCell)
  rcases hRole with hm | hr
  · obtain ⟨q, k, hq, hqSite, hQIssue, hHalf⟩ := hm
    have heq := hmma t j q hCt hq (by rw [hqSite]; simp)
    subst t
    by_cases hLater : d.block ≤ q.i
    · exact .inr (.inr (.inl (wait_before_later_pv hpre hX hs hCta hd hsite hwait
        (by omega) hQIssue hq hqSite hLater)))
    · have hSameHalf : k.val % 2 = (lastIssue tile).val % 2 := by
        rw [lastIssue_half, ← hColHalf, hHalf]
      have hJ := actual_prior_pv_index hpre hX hs (show q.i ≤ d.block - 1 by omega)
        hQIssue hIssue hq hqSite hSrc hSameHalf
      rcases Nat.eq_or_lt_of_le hJ with rfl | hJ
      · exact .inl rfl
      · refine .inr (.inl (.inl (TcMma.Before.of_mma_po hQIssue hIssue
          (Frame.lt_of_get hX hQIssue.choose_spec) rfl hJ ?_)))
        exact ⟨congrArg (fun n => tmemO + 128 * n) hSameHalf, rfl, rfl, rfl, rfl⟩
  · obtain ⟨k, words, hStore, hStoreCell, _, hTid, hTile⟩ := hr
    rw [hCell] at hTid hTile
    change tidOf L g = tidOf L t at hTid
    change (64 * tile.val + reg.val) / 64 = k.val at hTile
    have htEq : t = g := by
      rw [tidOf_eq hpre, tidOf_eq hpre] at hTid
      change t / L.block = g / L.block at hCt
      rw [hpre.block] at hCt
      omega
    have hkEq : k = tile := Fin.ext (by have := reg.isLt; omega)
    subst t k
    have hGet := hStore.choose_spec
    have hjLen : j < (X.tr g).length := PTX.len_of_get hGet
    have hNe : j ≠ i := by
      rintro rfl
      cases congrArg Event.kind (Option.some.inj (hGet.symm.trans hwait))
    rcases Nat.lt_or_gt_of_ne hNe with hBefore | hAfter
    · obtain ⟨s, hs'⟩ := FollowedPrefix.state_at hd hBefore.le
      obtain ⟨q, k, hStore⟩ := PvAccumulatorSource.followed_output_store hpre hX hs
        (by rw [hs']; simp) hStore hStoreCell
      obtain ⟨_, hk⟩ := store_same_lane_tile hpre hX hs hLane hStore
      subst k
      obtain ⟨_, _, _, _, hDInv, _, _⟩ := Frame.fired_site hs hX hwait hd
      obtain ⟨_, _, _, _, hQInv, _, _⟩ :=
        Frame.fired_site hs hX hStore.store.choose_spec hStore.state
      have hDN := (show Inv P L g d from hDInv).blockLt
      have hQN := (show Inv P L g q from hQInv).blockLt
      have hdSub := (show Inv P L g d from hDInv).subLt
      have hqSub := (show Inv P L g q from hQInv).subLt
      rw [hsite] at hdSub
      rw [hStore.site] at hqSub
      change d.sub < 1 at hdSub
      change q.sub < 1 at hqSub
      have hg := Frame.lt_of_get hX hwait
      have hRank := Wg0ProbabilityUnique.actual_rank_strict_of_counted hpre hX
        (hs g hg).machine hStore.store.choose_spec rfl hLen hStore.state hd hBefore
      simp only [Bound.rank, Bound.wg0Rank, Bound.wg0Block, Bound.wg0Ordinal,
        hStore.site, hsite] at hRank
      have hTileLt := tile.isLt
      have hBlock : q.block ≤ d.block - 1 := by omega
      exact .inr (.inl (PvAccumulatorSource.actual_earlier_rescale hpre hX hs hIssue hSrc
        rfl hStore hCta.symm hBlock))
    · have hBase : baseCausality L X (g, i) (g, j) :=
        TcMma.baseCausality_of_tc_po hwait rfl hAfter hjLen
      exact .inr (.inr (.inl ⟨(g, i), ⟨tag, hwait⟩, rfl, by omega, .inl hBase⟩))

/-- Later PV issues force the actual rescale-load wait through the consumer's score arrival. -/
theorem rescale_read_before_later_pv {j : Nat} {q : Wg1Mma.D} {k : Fin 8} {words : List Value}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hCta : ctaOf L issuer = ctaOf L g)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleLoad tile)
    (hload : X.TLd (g, i) (64 * tile.val) words .s32x32b)
    (hPV : Issue L X issuer j q.i k)
    (hq : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)))
    (hqSite : q.site = .pvMma k) (hBlock : d.block ≤ q.i) :
    TcMma.WaitBefore L X .waitLd (g, i) (issuer, j) := by
  have hGet := hload.choose_spec
  have hg := Frame.lt_of_get hX hGet
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hGet hd
  have hInv : Wg0.Inv P L g d := hInv
  obtain ⟨lane, hLane⟩ := GemmRing.softmax_thread hpre hCta.symm hInv.wg
  obtain ⟨a, r, atag, ha, haState, haSite, haBlock, hBase⟩ :=
    PvProbabilitySource.publication_before_pv hpre hX (fun g hg => (hs g hg).machine)
      ht hPV.choose_spec hq hqSite lane
  rw [← hLane] at ha hBase haState
  let m := GemmRing.score L (ctaOf L issuer) (rawSlot q.i)
  let trace := (hs g hg).machine.produces (hX.thr g hg)
  have hArr := (Wg0GemmTrace.composed_in_rescale_counts hpre trace hd
    (by rw [hsite]; rfl) (rawSlot q.i)).1
  rw [← hCta] at hArr
  change arrivals m ((X.tr g).take i) = (d.block + (1 - q.i % 2)) / 2 at hArr
  have hA := (Wg0GemmTrace.composed_score_counts hpre trace haState haSite).1
  rw [← hCta, haBlock] at hA
  change arrivals m ((X.tr g).take a) = q.i / 2 at hA
  have hge := PTX.MbarRing.arrival_index_ge ha (by simp [arrivesOn, sourceArrive, m]) hA
    (show arrivals m ((X.tr g).take i) ≤ q.i / 2 by rw [hArr]; omega)
  have hlt : i < a := by
    by_contra! hn
    have heq : a = i := by omega
    rw [heq] at ha
    cases congrArg Event.kind (Option.some.inj (hGet.symm.trans ha))
  obtain ⟨wt, hWaitLt, hw⟩ := TmemLoadWaits.rescale_wait_before_later_state
    hpre hX hs hload hd hsite hlt ha haState (by simp [haSite])
  have hWaitBefore : baseCausality L X (g, i + 1) (g, a) :=
    TcMma.baseCausality_of_tc_po hw rfl hWaitLt (PTX.len_of_get ha)
  exact ⟨(g, i + 1), ⟨wt, hw⟩, rfl, Nat.lt_succ_self i, .inl (hWaitBefore.trans hBase)⟩

/-- A rescale store overwriting a load's cell follows that lane's actual matching load wait. -/
theorem rescale_read_before_later_store {j t : Nat} {q : Wg0.D} {k : Fin 4} {words : List Value}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleLoad tile)
    (hload : X.TLd (g, i) (64 * tile.val) words .s32x32b)
    (hLane : tidOf L g < 128)
    (hstore : RescaleStore P L X t j (outputCell L g tile reg) q k)
    (hBlock : d.block ≤ q.block) :
    TcMma.WaitBefore L X .waitLd (g, i) (t, j) := by
  obtain ⟨htEq, hkEq⟩ := store_same_lane_tile hpre hX hs hLane hstore
  subst t k
  have hLoad := hload.choose_spec
  have hg := Frame.lt_of_get hX hLoad
  have hGet := hstore.store.choose_spec
  have hlt : i < j := by
    by_contra! h
    have hne : j ≠ i := by
      rintro rfl
      cases congrArg Event.kind (Option.some.inj (hGet.symm.trans hLoad))
    obtain ⟨_, _, _, _, hDInv, _, _⟩ := Frame.fired_site hs hX hLoad hd
    obtain ⟨_, _, _, _, hQInv, _, _⟩ := Frame.fired_site hs hX hGet hstore.state
    have hDN := (show Inv P L g d from hDInv).blockLt
    have hQN := (show Inv P L g q from hQInv).blockLt
    have hdSub := (show Inv P L g d from hDInv).subLt
    have hqSub := (show Inv P L g q from hQInv).subLt
    rw [hsite] at hdSub
    rw [hstore.site] at hqSub
    change d.sub < 1 at hdSub
    change q.sub < 1 at hqSub
    have hr := Wg0ProbabilityUnique.rank_strict_of_counted hpre hX (hs g hg).machine ht
      hGet rfl (PTX.len_of_get hLoad).le hstore.state hd (by omega)
    simp only [Bound.rank, Bound.wg0Rank, Bound.wg0Block, Bound.wg0Ordinal,
      hstore.site, hsite] at hr
    have hTileLt := tile.isLt
    omega
  obtain ⟨wt, hWaitLt, hw⟩ := TmemLoadWaits.rescale_wait_before_later_state
    hpre hX hs hload hd hsite hlt hGet hstore.state (by simp [hstore.site])
  exact ⟨(g, i + 1), ⟨wt, hw⟩, rfl, Nat.lt_succ_self i,
    .inl (TcMma.baseCausality_of_tc_po hw rfl hWaitLt (PTX.len_of_get hGet))⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RescaleTmemReadSource
