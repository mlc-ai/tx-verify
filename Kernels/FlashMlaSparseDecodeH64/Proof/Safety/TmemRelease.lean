-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemAllocation
public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemAsyncRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmemLoadWaits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0RescaleHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources

@[expose] public section

/-! # All tensor-memory accesses finish before any release of their allocation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Tmem.Pair Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem data_wait_before_dealloc {g i h j tag base n : Nat} {group : CtaGroup} {e : Event}
    {d : Wg0.D} {wait : TcKind} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hNotExit : d.site ≠ .exit)
    (hCta : ctaOf L g = ctaOf L h)
    (hDealloc : X.get (h, j) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩)
    (hWait : ∀ close ctag, X.get (g, close) = some ⟨ctag, .bar 12 none .sync⟩ →
      ∃ w wtag q, i < w ∧ X.get (g, w) = some ⟨wtag, .tc wait⟩ ∧
        Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
        q.site ≠ .everyone ∧ q.site ≠ .exit) :
    TcMma.WaitBefore L X wait (g, i) (h, j) := by
  have hScope : SameCta L g h := ⟨Frame.lt_of_get hX he, Frame.lt_of_get hX hDealloc, hCta⟩
  obtain ⟨b, bt, _, hb, hBar, _, _⟩ :=
    ScoreReleaseTrace.barrier_before_dealloc hpre hX hs ht hDealloc
  have hj : j < (X.tr h).length := PTX.len_of_get hDealloc
  have hpass : b + 1 < (X.tr h).length := by omega
  have hExitClose : (∃ n tag, X.get (g, n) = some ⟨tag, .exit⟩) →
      ∃ n tag, X.get (g, n) = some ⟨tag, .bar 12 none .sync⟩ := by
    rintro ⟨n, tag, hx⟩
    exact ScoreClosingGate.closing_of_exited_wg0_lane hpre hX hs ht hd hNotExit he hx
  obtain ⟨close, ctag, hClose⟩ := ScoreLifetime.closing_member hpre hX hs
    hScope hBar hpass hExitClose
  obtain ⟨w, wtag, q, hiw, hWait, hq, hn, hqx⟩ := hWait close ctag hClose
  have hord := ScoreLifetime.elapsed_closing_order hpre hX hs ht hScope hq hn hqx
    (PTX.len_of_get hWait).le hBar hpass (show b < j by omega) hj hExitClose
  exact ⟨(g, w), ⟨wtag, hWait⟩, rfl, hiw, .inl hord⟩

private theorem load_before_dealloc {g i h j tag base n address : Nat} {words : List Value}
    {shape : TcShape} {group : CtaGroup} (hload : X.TLd (g, i) address words shape)
    (hCta : ctaOf L g = ctaOf L h)
    (hDealloc : X.get (h, j) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    TcMma.WaitBefore L X .waitLd (g, i) (h, j) := by
  have he := hload.choose_spec
  obtain ⟨d, hd, _, hsite⟩ :=
    TcCollectiveSites.load_fields hpre hX (hs g (Frame.lt_of_get hX he)).machine ht hload
  have hn : d.site ≠ .exit := by
    rcases hsite with ⟨_, _, he, _, _⟩ | ⟨_, he | he, _, _⟩ <;> simp [he]
  exact data_wait_before_dealloc hpre hX hs ht he hd hn hCta hDealloc
    (fun _ _ hbar => TmemLoadWaits.load_wait_of_closing hpre hX hs ht hbar hload)

private theorem store_before_dealloc {g i h j tag base n address : Nat} {words : List Value}
    {shape : TcShape} {group : CtaGroup} (hstore : X.TSt (g, i) address words shape)
    (hCta : ctaOf L g = ctaOf L h)
    (hDealloc : X.get (h, j) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    TcMma.WaitBefore L X .waitSt (g, i) (h, j) := by
  obtain ⟨tag', he⟩ := hstore
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, hd, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  have hw := Wg0ScoreSources.writer_fields hpre hg hf (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  rcases hw with ⟨d, tile, rfl, hSite, hk⟩ | ⟨_, _, _, _, hk⟩ |
    ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩
  · obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hk)
    have hn : d.site ≠ .exit := by simp [hSite]
    apply data_wait_before_dealloc hpre hX hs ht he hd hn hCta hDealloc
    intro close ctag hClose
    have hBefore := ScoreClosingGate.wg0_before_closing hpre hX hs ht hClose hd
      (by simp [hSite]) hn (PTX.len_of_get he).le
    have hLen : i + 1 < (X.tr g).length :=
      Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hBefore) (PTX.len_of_get hClose)
    obtain ⟨wt, q, hWait, hq, hQ⟩ :=
      Wg0RescaleHistory.wait_next_state hpre hX hs hd hSite ⟨tag', he⟩ hLen
    exact ⟨i + 1, wt, q, Nat.lt_succ_self i, hWait, hq, by simp [hQ], by simp [hQ]⟩
  all_goals cases hk

/-- A tensor-memory load finishes before every release of its covering allocation. -/
theorem tmem_load_source_live {e source : EvId} {j : Nat} {cell : TcMma.Cell}
    (hload : TcMma.LoadCell L X e j cell) :
    TcMma.SourceLive L X source e cell := by
  obtain ⟨g, i⟩ := e
  have hOwner := TcMma.LoadCell.owner hload
  obtain ⟨a, words, shape, hl, _, _⟩ := hload
  rintro c r hr hCover ⟨h, k⟩ hRelease
  obtain ⟨hHome, tag, group, base, count, he⟩ := ScoreLifetime.release_source hX hr hRelease
  obtain ⟨_, _, _, hCTA, _, _, _⟩ := hCover
  have hCta : ctaOf L g = ctaOf L h := hOwner.symm.trans (hCTA.trans hHome.symm)
  refine .inl ⟨fun _ => load_before_dealloc hpre hX hs ht hl hCta he, ?_, ?_⟩
  · rintro ⟨_, _, _, _, hw⟩
    rw [hl.choose_spec] at hw
    cases hw
  · rintro (⟨_, _, _, _, _, ha⟩ | ⟨_, _, ha⟩ | ⟨_, _, ha⟩) <;>
      rw [hl.choose_spec] at ha <;> cases ha

/-- All represented accesses are covered and complete before every release of their allocation. -/
theorem no_tmem_access_unsafe :
    ¬ Tmem.Pair.AccessUnsafe L X := by
  intro hunsafe
  apply hunsafe
  rintro ⟨g, i⟩ cell hAccess
  obtain ⟨hOwner, hAlloc⟩ := tmem_access_owner_and_allocation hpre hX hs ht hAccess
  refine ⟨hAlloc, ?_⟩
  rintro c r hr hCover ⟨h, j⟩ hRelease
  obtain ⟨hHome, tag, group, base, count, he⟩ := ScoreLifetime.release_source hX hr hRelease
  obtain ⟨_, _, _, hCTA, _, _, _⟩ := hCover
  have hCta : ctaOf L g = ctaOf L h := hOwner.symm.trans (hCTA.trans hHome.symm)
  exact .inl ⟨fun ⟨_, _, _, hl⟩ => load_before_dealloc hpre hX hs ht hl hCta he,
    fun ⟨_, _, _, hw⟩ => store_before_dealloc hpre hX hs ht hw hCta he,
    fun hi => tc_async_before_dealloc hpre hX hs ht hi hCta he⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
