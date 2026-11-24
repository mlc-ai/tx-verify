-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.TcDataOrder
public import Lemmas.Step.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcPositions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Clc.ClcExecution
import Lemmas.Step.CtaBarNamed
import Lemmas.Step.WarpLanes

public section

/-! # Warp participants of a blocked Tensor Memory data collective -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem data_needs {i : EvId} {tag : Nat} {k : TcKind}
    (he : X.get i = some ⟨tag, .tc k⟩) (hk : isTcColl ⟨tag, .tc k⟩ = true)
    (hn : ∀ grp dst req, k ≠ .resource grp dst req) :
    Needs L X i = tcNeeds L X i := by
  cases k <;> first
    | exact (hn _ _ _ rfl).elim
    | (solve | simp [Needs, he, KindNeeds])
    | cases hk

/-- A Tensor Memory data collective releases once all of its warp has issued the same
ordinal. Otherwise a lane of the warp is pending before that ordinal. -/
theorem tc_data_release_or_missing (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    {g tag : Nat} {k : TcKind} (he : X.get (g, (X.tr g).length - 1) = some ⟨tag, .tc k⟩)
    (hk : isTcColl ⟨tag, .tc k⟩ = true) (hn : ∀ grp dst req, k ≠ .resource grp dst req) :
    PTX.Step.Released L X g ∨
      ∃ other, SameWarp L g other ∧ Frame.Pending L X other ∧
        (X.tr other).countP isTcColl ≤ ((X.tr g).take ((X.tr g).length - 1)).countP isTcColl := by
  let pos := (X.tr g).length - 1
  let n := ((X.tr g).take pos).countP isTcColl
  have hg := Frame.lt_of_get hX he
  have hRank : X.TcK (g, pos) n := ⟨⟨_, he, hk⟩, rfl⟩
  classical
  by_cases hAll : ∀ other, SameWarp L g other → n < (X.tr other).countP isTcColl
  · refine .inl ⟨fun _ _ _ _ => ?_⟩
    intro need hm
    rw [data_needs he hk hn] at hm
    obtain ⟨other, hMem, rfl⟩ := List.mem_map.mp hm
    obtain ⟨lane, hLane, rfl⟩ := List.mem_map.mp hMem
    have hl : lane < 32 := lt_of_lt_of_le (List.mem_range.mp hLane) (min_le_left ..)
    have hw : SameWarp L g (warpLane L g lane) := by
      apply (PTX.Step.sameWarp_lane _ hg hl).1
      rw [hpre.block]
    obtain ⟨j, e, hget, hc, hord⟩ := PTX.NamedBar.exists_ordinal isTcColl
      (X.tr (warpLane L g lane)) (hAll _ hw)
    exact ⟨.thread (warpLane L g lane, j), ⟨e, hget⟩, j, rfl, ⟨⟨e, hget, hc⟩, hord⟩⟩
  · push Not at hAll
    obtain ⟨other, hw, hCount⟩ := hAll
    refine .inr ⟨other, hw, ⟨hw.1.2.1, ?_, ?_⟩, hCount⟩
    · rintro ⟨_, _, hCan⟩
      obtain ⟨i, sp, tg, _, hi, _⟩ := hX.clc.canceled_has_issue hCan
      exact GlobalWrites.no_clc (i := i) (s := sp) (tg := tg) hX hi
    · intro t hLast
      have he' : X.get (other, (X.tr other).length - 1) = some ⟨t, .exit⟩ := by
        change (X.tr other)[(X.tr other).length - 1]? = _
        rwa [← List.getLast?_eq_getElem?]
      exact TcCollectiveTrace.not_exited_short hpre hX hs ht hw hRank ⟨⟨t, he'⟩, hCount⟩

private theorem data_successor {g : Nat} {d : Wg0.D} {q : Machine.ThreadD} {e : Event}
    (hSite : TcCollectiveSites.DataSite d.site)
    (hn : Machine.next P L g (.wg0 d) e = some (some q)) :
    ∃ d', q = .wg0 d' ∧ Wg0.next P L g d e = some (some d') := by
  simp only [Machine.next] at hn
  split at hn
  · rename_i d' h
    cases hn
    exact ⟨d', rfl, h⟩
  · split at hn
    · rename_i h
      rcases h with ho | ho <;> rw [ho] at hSite <;> cases hSite
    · cases hn
  · cases hn

/-- A waiting Tensor Memory data lane releases, or its warp has a pending lane of lower
dependency priority. A live tail records the successor of each dispatched data instruction. -/
theorem tc_data_release_or_earlier (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hub : ¬ HasUb X)
    (hLive : ∀ g, Frame.Pending L X g →
      ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    {g tag : Nat} {k : TcKind} (hp : Frame.Pending L X g)
    (he : X.get (g, (X.tr g).length - 1) = some ⟨tag, .tc k⟩)
    (hk : isTcColl ⟨tag, .tc k⟩ = true) (hn : ∀ grp dst req, k ≠ .resource grp dst req) :
    ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)) ∧
      (PTX.Step.Released L X g ∨
        ∃ other q, SameWarp L g other ∧ Frame.Pending L X other ∧
          Frame.stateAt (Machine.code P L) X other (X.tr other).length = some (some q) ∧
          priority P L other q < priority P L g (.wg0 d)) := by
  have hg := hp.1
  have hSound := (hs g hg).machine
  obtain ⟨p, _, hP, hf⟩ := RingSourceSites.fired_from_trace hX hSound ht he (by simp)
  have hSource : ∃ d, p = .wg0 d ∧ TcCollectiveSites.DataSite d.site := by
    rcases TcCollectiveSites.of_fired hpre hf hk with h | ⟨grp, dst, req, hkind, _⟩
    · exact h
    · exact (hn grp dst req (Kind.tc.inj hkind)).elim
  obtain ⟨before, rfl, hSite⟩ := hSource
  obtain ⟨q, hQ⟩ := hLive g hp
  have hLen : (X.tr g).length - 1 < (X.tr g).length := PTX.len_of_get he
  have hIndex : (X.tr g).length - 1 + 1 = (X.tr g).length := by omega
  have hNext := hQ
  rw [← hIndex, Frame.stateAt_succ he, hP, Option.bind_some] at hNext
  obtain ⟨d, rfl, hWgNext⟩ := data_successor hSite hNext
  have hAfter := softmax_after_data_priority hSite hWgNext
  refine ⟨d, hQ, ?_⟩
  rcases tc_data_release_or_missing hpre hX hs ht he hk hn with
    hRelease | ⟨other, hw, hPending, hMissing⟩
  · exact .inl hRelease
  obtain ⟨peer, hPeer⟩ := hLive other hPending
  refine .inr ⟨other, peer, hw, hPending, hPeer, ?_⟩
  have hi : Wg0.Inv P L g before := (Exists.choose_spec hf).1.2
  have hWarp : warpOf L g = warpOf L other := by
    simpa only [warpOf, tidOf_eq hpre, hpre.block] using hw.2
  have hwg : wgOf L other = 0 := by
    have hW := hi.warpLt
    rw [hWarp] at hW
    unfold warpOf at hW
    unfold wgOf
    omega
  have hRow : ctaidY L g = ctaidY L other := by simp only [ctaidY, ctaOf, hw.1.2.2]
  have hSetup : TcPrologueRank.setup L g = TcPrologueRank.setup L other := by
    simp only [TcPrologueRank.setup, hWarp]
  have hVote := Wg0TcSchedule.same_warp (X := X) hw
  obtain ⟨hSched, hCount⟩ := Wg0TcTrace.rank_at hpre hX hSound hg hLen.le hP
  rcases Wg0OutputVisits.softmax_state_cases hX hPending.1 (hs other hPending.1).machine
      hwg hPeer with ⟨s, rfl⟩ | ⟨softmax, rfl⟩ | rfl
  · exact (prologue_before_data_priority hSite).trans hAfter
  · obtain ⟨_, hRun⟩ := Frame.run_some hX hub hPending
    obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hPending.1 hRun hPeer
    obtain ⟨hs', hc'⟩ := Wg0TcTrace.rank_at hpre hX (hs other hPending.1).machine
      hPending.1 (Nat.le_refl _) hPeer
    rw [List.take_length] at hc'
    rw [hSetup, hVote] at hCount
    rw [hVote] at hSched
    rw [hCount, hc'] at hMissing
    have hR := Nat.le_of_add_le_add_left hMissing
    exact lt_of_le_of_lt (softmax_before_data_priority hRow hi hInv hSite hSched hs' hR) hAfter
  · obtain ⟨commit, _, e, cd, _, he', _, hCd, hCsite, _, _⟩ :=
      Wg0OutputVisits.commitBeforeDone hX hPending.1 (hs other hPending.1).machine hwg hPeer
    have hcLen : commit ≤ (X.tr other).length := (PTX.len_of_get he').le
    obtain ⟨hs', hc'⟩ := Wg0TcTrace.rank_at hpre hX (hs other hPending.1).machine
      hPending.1 hcLen hCd
    obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he' hCd
    have hLast := (show Wg0.Inv P L other cd from hInv).epilogueLast (by rw [hCsite]; rfl)
    have hFinish := Wg0TcPositions.finished_data hs' (.inl hCsite) hLast
    have hBlock : before.block < Wg0.blocksOf P L other := by
      have hb := hi.blockLt
      simpa only [Wg0.blocksOf, Wg0.eOf, hRow] using hb
    rw [hVote] at hSched hCount
    have hBefore := Wg0TcPositions.before_final hSched hSite hi.rescaleArm hBlock
    have hMono := (List.take_sublist commit (X.tr other)).countP_le (p := isTcColl)
    rw [hc', hFinish] at hMono
    rw [hCount, hSetup] at hMissing
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
