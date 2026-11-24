-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingHandoffs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawRelease
public import Lemmas.Async.AsyncMBarrier
public import Lemmas.Order.OrderWaits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantFence
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

@[expose] public section

/-! # Memory order for a raw-buffer read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing

open PTX AsyncCopy MBarrier PTX.Flow PTX.MbarRing

variable {P : Params}

/-- A gather of this or an older use of the same slot is visible to the raw reader through
that generation's actual acquire on the same dequantizer thread. -/
theorem gather_at_generation_with_acquires {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta g j row col byte generation : Nat} {lane : Fin 128} {e : Event} {d : Wg2.D} {l : Loc}
    (k : Fin 16) (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (hAcquires : GatherAcquires L X cta g)
    (hgc : ctaOf L g = cta) (he : X.get (consumer L cta lane, j) = some e)
    (hst : Frame.stateAt (Machine.code P L) X (consumer L cta lane) j = some (some (.wg2 d)))
    (hd : Wg2RawTrace.RawAccess d.site) (hGeneration : generation ≤ d.block / 2) :
    let slot := rawSlot d.block
    let m := ready L cta slot
    let issue := (g, nthEv X (issuesTo m) g (16 * generation + k.val))
    let part := Part.write (.load row col byte)
    AsyncCovers X issue part l →
      modelCausality L X l (.async issue part) (.thread (consumer L cta lane, j)) := by
  intro slot m issue part hCover
  let h := consumer L cta lane
  have hhc : ctaOf L h = cta := by
    have hlane := lane.isLt
    simp only [h, consumer, ctaOf, hpre.block]
    omega
  have hh := Frame.lt_of_get hX he
  have hj : j < (X.tr h).length := PTX.len_of_get he
  obtain ⟨_, hCnt⟩ := Wg2RawTrace.composed_raw_access_counts hpre
    ((hs h hh).produces (hX.thr h hh)) hst hd
  rw [hhc] at hCnt
  change PTX.Flow.okPolls m ((X.tr h).take j) = d.block / 2 + 1 at hCnt
  obtain ⟨i, site, parity, acq, scope, hBefore, hGet, hUses⟩ :=
    MbarRing.Poll.exists_nth (show generation + 1 ≤ _ by rw [hCnt]; omega)
  have hObs := hAcquires k hGet rfl
  change AsyncObserved X (g, nthEv X (issuesTo m) g
    (16 * PTX.Flow.okPolls m ((X.tr h).take i) + k.val)) (.notify .load) (h, i) true .cta at hObs
  rw [hUses] at hObs
  change AsyncObserved X issue (.notify .load) (h, i) true .cta at hObs
  have hWrite : AsyncObserved X issue part (h, i) true .cta := hObs
  obtain ⟨o, a, _, ⟨_, hIssue⟩, _, _⟩ := hObs.tensor
  have hg : g < L.threads := Frame.lt_of_get hX hIssue
  have hscope := Unit.Gate.scopesMeet ⟨hg, hh, hgc.trans hhc.symm⟩ .cluster .cta
  have hpo : po X (h, i) (h, j) :=
    po_of_source_not_access rfl hBefore hj (by rw [hGet]; rfl)
  exact ⟨hCover, (h, i), .inr ⟨.cta, hWrite, hscope⟩, .inl (.single (.inl hpo))⟩


/-- A gather of this or an older use of the same slot is visible to the raw reader through
that generation's actual acquire on the same dequantizer thread. -/
theorem gather_at_generation_before_raw_access {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta g j row col byte generation : Nat} {lane : Fin 128} {e : Event} {d : Wg2.D} {l : Loc}
    (k : Fin 16) (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : Issuer P L X cta g) (hgc : ctaOf L g = cta) (he : X.get (consumer L cta lane, j) = some e)
    (hst : Frame.stateAt (Machine.code P L) X (consumer L cta lane) j = some (some (.wg2 d)))
    (hd : Wg2RawTrace.RawAccess d.site) (hGeneration : generation ≤ d.block / 2) :
    let slot := rawSlot d.block
    let m := ready L cta slot
    let issue := (g, nthEv X (issuesTo m) g (16 * generation + k.val))
    let part := Part.write (.load row col byte)
    AsyncCovers X issue part l →
      modelCausality L X l (.async issue part) (.thread (consumer L cta lane, j)) :=
  gather_at_generation_with_acquires k hpre hX hs
    (fun tile he hk => gather_acquired tile hpre hX hs ht hp he hk) hgc he hst hd hGeneration

/-- A raw read precedes a later gather into the same buffer through the dequantizer's proxy
fence and the free-barrier handoff. -/
theorem raw_access_before_reuse {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta g j i row col byte : Nat} {lane : Fin 128} {e f : Event} {d : Wg2.D} {t : Wg1Tma.D}
    {l : Loc} {k : Fin 16} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : Issuer P L X cta g) (hgc : ctaOf L g = cta) (he : X.get (consumer L cta lane, j) = some e)
    (hf : X.get (g, i) = some f)
    (hst : Frame.stateAt (Machine.code P L) X (consumer L cta lane) j = some (some (.wg2 d)))
    (hT : Frame.stateAt (Machine.code P L) X g i = some (some (.tma t)))
    (hd : Wg2RawTrace.RawAccess d.site) (htma : t.site = .issue k)
    (hSlot : d.block % 2 = t.block % 2) (hUse : d.block / 2 < t.block / 2)
    (hspace : l.space = .shared) (hloc : l.cta = cta)
    (hCover : AsyncCovers X (g, i) (.write (.load row col byte)) l) :
    modelCausality L X l (.thread (consumer L cta lane, j))
      (.async (g, i) (.write (.load row col byte))) := by
  let h := consumer L cta lane
  let slot := rawSlot d.block
  let m := free L cta slot
  let u := d.block / 2
  have hhc : ctaOf L h = cta := by
    have hlane := lane.isLt
    simp only [h, consumer, ctaOf, hpre.block]
    omega
  have hh := Frame.lt_of_get hX he
  have hg := Frame.lt_of_get hX hf
  have hi : i < (X.tr g).length := PTX.len_of_get hf
  have hPoll := TmaRawTrace.composed_gather_reuse_count hpre
    ((hs g hg).produces (hX.thr g hg)) hT htma
  rw [hgc, ← hSlot] at hPoll
  change PTX.Flow.okPolls m ((X.tr g).take i) = t.block / 2 + 1 at hPoll
  obtain ⟨iw, wp, q, acq, scope, hw, hwGet, hwUse⟩ :=
    MbarRing.Poll.exists_nth (show (u + 1) + 1 ≤ PTX.Flow.okPolls m ((X.tr g).take i) from
      by rw [hPoll]; unfold u; omega)
  have hSync := free_release_sync lane hpre hX hs ht hp hwGet rfl hwUse
  let release := Unit.it X m (consumer L cta) lane u
  change MbarRing.Syncs L X release (g, iw) m at hSync
  obtain ⟨rs, hRel, as, hObs, hScopes⟩ := hSync
  obtain ⟨tx, count, site, hGetRelease⟩ := hRel
  let ir := release.2
  have hGet : X.get (h, ir) = some ⟨site, .arrive m tx count true rs⟩ := hGetRelease
  have hrl := Frame.lt_of_get hX hGet
  obtain ⟨_, _, _, _, _, state, _, hSite, hState⟩ :=
    release_source hpre hX (hs h hrl) ht hGet rfl
  obtain ⟨jf, fence, ready, df, hrf, hFenceGet, hFenceKind, hReady, hF, hReadyState, hFenceState⟩ :=
    Wg2RawRelease.fence_before_free hX (hs h hh) hGet hState hSite
  have hReadCounts := (Wg2RawTrace.composed_raw_access_counts hpre
    ((hs h hh).produces (hX.thr h hh)) hst hd).1
  rw [hhc] at hReadCounts
  change PTX.Flow.arrivals m ((X.tr h).take j) = u at hReadCounts
  have hArrival : arrivesOn m ⟨site, .arrive m tx count true rs⟩ = true := by
    simp [arrivesOn, sourceArrive]
  have hArrCount := (nthEv_spec_of_get (p := arrivesOn m) hGet).2
  change PTX.Flow.arrivals m ((X.tr h).take ir) = u at hArrCount
  have hjr := arrival_index_ge hGet hArrival hArrCount hReadCounts.le
  have hNoRead (s : Wg2.Site)
      (ha : s = .fence ∨ s = .ready ∨ s = .free)
      (hEq : d.site = s) : False := by
    rcases hd with ⟨r, z, h⟩ | ⟨r, z, h⟩
    all_goals
      rcases ha with rfl | rfl | rfl
      all_goals rw [h] at hEq
      all_goals cases hEq
  have hjf : j < jf := by
    by_contra hNo
    rcases (show j = jf ∨ j = jf + 1 ∨ j = ir by omega) with h | h | h
    · rw [h, hFenceState] at hst
      exact hNoRead _ (.inl hF) (congrArg Wg2.D.site
        (Machine.ThreadD.wg2.inj (Option.some.inj (Option.some.inj hst))).symm)
    · rw [h, hReadyState] at hst
      exact hNoRead _ (.inr (.inl hReady)) (congrArg Wg2.D.site
        (Machine.ThreadD.wg2.inj (Option.some.inj (Option.some.inj hst))).symm)
    · rw [h, hState] at hst
      exact hNoRead _ (.inr (.inr hSite)) (congrArg Wg2.D.site
        (Machine.ThreadD.wg2.inj (Option.some.inj (Option.some.inj hst))).symm)
  have hFlen : jf < (X.tr h).length := PTX.len_of_get hFenceGet
  have hpo : po X (h, j) (h, jf) := by
    refine ⟨rfl, hjf, hFlen, fun hSame => ?_⟩
    have hall := hSame.1
    change ((X.get (h, jf)).bind Event.acc).isSome = true at hall
    obtain ⟨tag, kind⟩ := fence
    change kind = .fenceProxy (.async (some (.shared .cta))) none at hFenceKind
    rw [hFenceGet, hFenceKind] at hall
    cases hall
  have hfenceBefore : baseCausality L X (h, jf) (g, i) :=
    Staging.baseCausality_of_handoff ⟨tx, count, site, hGetRelease⟩ hObs hScopes
      ⟨rfl, by change jf ≤ ir; omega⟩ ⟨rfl, hw, hi⟩
  have hFence : X.IsProxyFence (h, jf) (.async (some (.shared .cta))) none := by
    obtain ⟨tag, kind⟩ := fence
    refine ⟨tag, ?_⟩
    change kind = .fenceProxy (.async (some (.shared .cta))) none at hFenceKind
    rw [hFenceGet, hFenceKind]
  exact ⟨hCover, .inl ⟨(h, jf), some (.shared .cta), none, hFence, hh,
    ⟨hspace, hloc.trans hhc.symm⟩, ⟨hh, hg, congrArg L.clusterOfCta (hhc.trans hgc.symm)⟩,
    .single (.inl hpo), hfenceBefore⟩⟩

/-- The actual proxy fence and free-slot release order a read before any later reuse. -/
theorem actual_raw_access_before_reuse {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta g j i row col byte : Nat} {lane : Fin 128} {e f : Event} {d : Wg2.D} {t : Wg1Tma.D}
    {l : Loc} {k : Fin 16} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hp : Issuer P L X cta g)
    (hgc : ctaOf L g = cta) (he : X.get (consumer L cta lane, j) = some e)
    (hf : X.get (g, i) = some f) (hAccess : e.acc.isSome = true)
    (hst : Frame.stateAt (Machine.code P L) X (consumer L cta lane) j = some (some (.wg2 d)))
    (hT : Frame.stateAt (Machine.code P L) X g i = some (some (.tma t)))
    (hd : Wg2RawTrace.RawAccess d.site) (htma : t.site = .issue k)
    (hSlot : d.block % 2 = t.block % 2) (hUse : d.block / 2 < t.block / 2)
    (hspace : l.space = .shared) (hloc : l.cta = cta)
    (hCover : AsyncCovers X (g, i) (.write (.load row col byte)) l) :
    modelCausality L X l (.thread (consumer L cta lane, j))
      (.async (g, i) (.write (.load row col byte))) := by
  let h := consumer L cta lane
  let slot := rawSlot d.block
  let m := free L cta slot
  let u := d.block / 2
  have hhc : ctaOf L h = cta := by
    have hlane := lane.isLt
    simp only [h, consumer, ctaOf, hpre.block]
    omega
  have hh := Frame.lt_of_get hX he
  have hg := Frame.lt_of_get hX hf
  have hi : i < (X.tr g).length := PTX.len_of_get hf
  have hPoll := TmaRawTrace.composed_gather_reuse_count hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hT htma
  rw [hgc, ← hSlot] at hPoll
  change PTX.Flow.okPolls m ((X.tr g).take i) = t.block / 2 + 1 at hPoll
  obtain ⟨iw, wp, q, acq, scope, hw, hwGet, hwUse⟩ :=
    MbarRing.Poll.exists_nth (show (u + 1) + 1 ≤ PTX.Flow.okPolls m ((X.tr g).take i) from
      by rw [hPoll]; unfold u; omega)
  have hWarp := RingRoleGeometry.of_trace hX hg (hs g hg).machine hT
  have hSync := actual_free_release_sync lane hpre hX hs hWarp hp hgc hwGet rfl hwUse
  let release := Unit.it X m (consumer L cta) lane u
  change MbarRing.Syncs L X release (g, iw) m at hSync
  obtain ⟨rs, hRel, as, hObs, hScopes⟩ := hSync
  obtain ⟨tx, count, site, hGetRelease⟩ := hRel
  let ir := release.2
  have hGet : X.get (h, ir) = some ⟨site, .arrive m tx count true rs⟩ := hGetRelease
  obtain ⟨jf, middle, fence, hRF, hMiddle, hNoAccess, hFenceGet, hFenceKind⟩ :=
    MachineTracking.actual_raw_release_fence hpre hX hs hGet rfl
  have hReadCounts := (Wg2RawTrace.composed_raw_access_counts hpre
    ((hs h hh).machine.produces (hX.thr h hh)) hst hd).1
  rw [hhc] at hReadCounts
  change PTX.Flow.arrivals m ((X.tr h).take j) = u at hReadCounts
  have hArrival : arrivesOn m ⟨site, .arrive m tx count true rs⟩ = true := by
    simp [arrivesOn, sourceArrive]
  have hArrCount := (nthEv_spec_of_get (p := arrivesOn m) hGet).2
  change PTX.Flow.arrivals m ((X.tr h).take ir) = u at hArrCount
  have hjr := arrival_index_ge hGet hArrival hArrCount hReadCounts.le
  have hjf : j < jf := by
    by_contra hNo
    have hRead (event : Event) (hSame : X.get (h, j) = some event)
        (ha : event.acc = none) : False := by
      have heq := Option.some.inj (he.symm.trans hSame)
      rw [heq, ha] at hAccess
      cases hAccess
    rcases (show j = jf ∨ j = jf + 1 ∨ j = ir by omega) with heq | heq | heq
    · apply hRead fence (heq.symm ▸ hFenceGet)
      obtain ⟨tag, kind⟩ := fence
      change kind = _ at hFenceKind
      subst kind
      rfl
    · exact hRead middle (heq.symm ▸ hMiddle) hNoAccess
    · exact hRead _ (heq.symm ▸ hGet) rfl
  have hFlen : jf < (X.tr h).length := PTX.len_of_get hFenceGet
  have hpo : po X (h, j) (h, jf) := by
    refine ⟨rfl, hjf, hFlen, fun hSame => ?_⟩
    have hall := hSame.1
    change ((X.get (h, jf)).bind Event.acc).isSome = true at hall
    obtain ⟨tag, kind⟩ := fence
    change kind = .fenceProxy (.async (some (.shared .cta))) none at hFenceKind
    rw [hFenceGet, hFenceKind] at hall
    cases hall
  have hfenceBefore : baseCausality L X (h, jf) (g, i) :=
    Staging.baseCausality_of_handoff ⟨tx, count, site, hGetRelease⟩ hObs hScopes
      ⟨rfl, by change jf ≤ ir; omega⟩ ⟨rfl, hw, hi⟩
  have hFence : X.IsProxyFence (h, jf) (.async (some (.shared .cta))) none := by
    obtain ⟨tag, kind⟩ := fence
    refine ⟨tag, ?_⟩
    change kind = .fenceProxy (.async (some (.shared .cta))) none at hFenceKind
    rw [hFenceGet, hFenceKind]
  exact ⟨hCover, .inl ⟨(h, jf), some (.shared .cta), none, hFence, hh,
    ⟨hspace, hloc.trans hhc.symm⟩, ⟨hh, hg, congrArg L.clusterOfCta (hhc.trans hgc.symm)⟩,
    .single (.inl hpo), hfenceBefore⟩⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing
