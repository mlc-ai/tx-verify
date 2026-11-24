-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.SoftmaxNamedOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputPublication
public import Lemmas.Step.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Interface.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Clc.ClcExecution
import Lemmas.Flow.NthEv
import Lemmas.Step.CtaBarFinishExit

public section

/-! # Missing participants of a named softmax barrier -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0)
include hpre

private theorem observed_ord_le (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    {g i tag : Nat} (he : X.IsBarrier (g, i) 9 (some 128) tag) :
    ((X.tr g).take i).countP (Execution.isBarId 9) ≤ 2 * Wg0.blocksOf P L g + 5 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hd, hSite, _, _, _⟩ := Wg0BarrierTrace.bar9_at hpre hX (hs g hg).machine ht he rfl
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  have hLt := (show Wg0.Inv P L g d from hInv).blockLt
  rw [Wg0BarrierCount.count_at_wg0 hpre hX (hs g hg).machine he hd]
  cases h : d.site <;> simp only [Wg0BarrierTrace.Bar9Site, h] at hSite
  all_goals
    simp only [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, h]
    try omega

private theorem count_after_done (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) {g i : Nat} (hg : g < L.threads)
    (hwg : wgOf L g = 0) (hd : Frame.stateAt (Machine.code P L) X g i = some (some .done)) :
    2 * Wg0.blocksOf P L g + 6 ≤ (X.tr g).countP (Execution.isBarId 9) := by
  have hSound := (hs g hg).machine
  obtain ⟨j, _, d, e, hst, hSite, he', hkind⟩ :=
    Wg0OutputVisits.barrierBeforeDone hpre hX hg hSound hwg hd 3
  have hCount := Wg0BarrierCount.epiOrdinal hpre hX hSound he' hst hSite
  have hTick : Execution.isBarId 9 e = true := by simp [Execution.isBarId, hkind]
  have hMono := countP_take_mono (Execution.isBarId 9) (X.tr g) (i := j + 1)
    (j := (X.tr g).length) (PTX.len_of_get he')
  rw [countP_take_succ he' hTick, hCount, List.take_length] at hMono
  exact hMono

omit hpre in
private theorem wf_same_trace_bar_history :
    Assumption.WfCtaHistory (L := L) (K := kernel) (mem0 := mem0) Assumptions.all := by
  intro Y c suffix hY
  exact Interface.all_wf_effects hY (Y.le_withCtaHistory c ⟨suffix, rfl⟩) rfl rfl rfl

/-- When all participating warps are in the softmax warpgroup and an exited lane has supplied
the requested generation, a blocked named arrival can release or identify a missing pending lane. -/
theorem named_release_or_missing (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hNoFault : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y)
    {g tag id : Nat} {count : Option Nat} {warps : Finset Nat}
    (hShape : PTX.NamedBar.Shape L count warps id)
    (hSources : PTX.NamedBar.Sources L X count warps id) (hSoftmax : ∀ w ∈ warps, w < 4)
    (he : X.IsBarrier (g, (X.tr g).length - 1) id count tag)
    (hExited : ∀ other, SameCta L g other → other % L.block / 32 ∈ warps →
      wgOf L other = 0 → ∀ i et, X.get (other, i) = some ⟨et, .exit⟩ →
      ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) <
        (X.tr other).countP (Execution.isBarId id)) :
    let n := ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)
    (∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g) ∨
      ∃ other, SameCta L g other ∧ other % L.block / 32 ∈ warps ∧
        wgOf L other = 0 ∧ Frame.Pending L X other ∧
        (X.tr other).countP (Execution.isBarId id) ≤ n := by
  let n := ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)
  let cta := g / L.block
  let present (lane : Nat) :=
    ∃ j t mode, X.get (cta * L.block + lane, j) = some ⟨t, .bar id count mode⟩ ∧
      ((X.tr (cta * L.block + lane)).take j).countP (Execution.isBarId id) = n
  classical
  have hg := Frame.lt_of_get hmax.1 he
  have hCta := PTX.NamedBar.cta_lt hg
  have hPresent (lane : Nat) (hCount : n < (X.tr (cta * L.block + lane)).countP
      (Execution.isBarId id)) : present lane := by
    obtain ⟨j, ev, hget, hid, hOrd⟩ := PTX.NamedBar.exists_ordinal
      (Execution.isBarId id) (X.tr (cta * L.block + lane)) hCount
    obtain ⟨t, c, mode, rfl⟩ := PTX.NamedBar.isBarId_form hid
    have hEvent : X.get (cta * L.block + lane, j) = some ⟨t, .bar id c mode⟩ := hget
    have hLane := Frame.lt_of_get hmax.1 hEvent
    have hCountArg := (hSources (cta * L.block + lane, j) t c ⟨mode, hEvent⟩ hLane).2
    exact ⟨j, t, mode, hCountArg ▸ hEvent, hOrd⟩
  by_cases hall : ∀ lane < L.block, lane / 32 ∈ warps → present lane
  · exact .inl (PTX.NamedBar.sync_release_of_wf hmax wf_same_trace_bar_history hNoFault
      hShape hSources hg he hall)
  · push Not at hall
    obtain ⟨lane, hLane, hMember, hMissing⟩ := hall
    let other := cta * L.block + lane
    have hOther := PTX.NamedBar.cta_thread_lt hCta hLane
    have hGeo : other / L.block = cta := by
      change (cta * L.block + lane) / L.block = cta
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hLane),
        Nat.div_eq_of_lt hLane, Nat.zero_add]
    have hLocal : other % L.block = lane := by
      change (cta * L.block + lane) % L.block = lane
      rw [Nat.add_comm, Nat.mul_comm cta L.block, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hLane]
    have hWg : wgOf L other = 0 := by
      have hPart := hSoftmax _ hMember
      have hlt : lane < 128 := by omega
      unfold wgOf
      rw [tidOf_eq hpre, ← hpre.block, hLocal, Nat.div_eq_of_lt hlt]
    have hSame : SameCta L g other := ⟨hg, hOther, hGeo.symm⟩
    have hPart : other % L.block / 32 ∈ warps := hLocal.symm ▸ hMember
    refine .inr ⟨other, hSame, hPart, hWg, ⟨hOther, ?_, ?_⟩, ?_⟩
    · rintro ⟨_, _, hC⟩
      obtain ⟨i, s, tg, _, hIssue, _⟩ := hmax.1.clc.canceled_has_issue hC
      exact GlobalWrites.no_clc (i := i) (s := s) (tg := tg) hmax.1 hIssue
    · intro et hLast
      have hExit : X.get (other, (X.tr other).length - 1) = some ⟨et, .exit⟩ := by
        change (X.tr other)[(X.tr other).length - 1]? = _
        rwa [← List.getLast?_eq_getElem?]
      exact hMissing (hPresent lane (hExited other hSame hPart hWg _ et hExit))
    · exact Nat.le_of_not_gt (fun hn => hMissing (hPresent lane hn))

/-- A last barrier-9 arrival either releases with the same traces or identifies a pending
softmax lane with too few arrivals to supply that generation. Exited lanes already supplied
every generation the waiting lane could have reached. -/
theorem bar9_release_or_missing (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hNoFault : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y) {g tag : Nat}
    (he : X.IsBarrier (g, (X.tr g).length - 1) 9 (some 128) tag) :
    let n := ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 9)
    (∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g) ∨
      ∃ other, SameCta L g other ∧ wgOf L other = 0 ∧ Frame.Pending L X other ∧
        (X.tr other).countP (Execution.isBarId 9) ≤ n := by
  have hExit other (hSame : SameCta L g other)
      (_ : other % L.block / 32 ∈ OutputPublication.stagingWarps)
      (hWg : wgOf L other = 0) i et (he' : X.get (other, i) = some ⟨et, .exit⟩) :
      ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 9) <
        (X.tr other).countP (Execution.isBarId 9) := by
    have hg := Frame.lt_of_get hmax.1 he'
    have hDone := Wg0OutputVisits.doneAtExit hmax.1 (hs other hg).machine ht hWg he' rfl
    have hPast := count_after_done hpre hmax.1 hs hg hWg hDone
    have hAtMost := observed_ord_le hpre hmax.1 hs ht he
    have hRow : Wg0.blocksOf P L other = Wg0.blocksOf P L g := by
      simp only [Wg0.blocksOf, Wg0.eOf, ctaidY, ctaOf, hSame.2.2]
    rw [hRow] at hPast
    exact lt_of_le_of_lt hAtMost hPast
  rcases named_release_or_missing hpre hmax hNoFault (OutputPublication.shape hpre)
    (OutputPublication.sources hpre hmax.1 (fun g hg => (hs g hg).machine) ht)
    (fun _ hw => Finset.mem_range.mp hw) he hExit with h | ⟨o, hc, _, hw, hp, ho⟩
  · exact .inl h
  · exact .inr ⟨o, hc, hw, hp, ho⟩

/-- A blocked barrier-9 lane either releases with unchanged traces, or one of its missing
participants is pending at a strictly earlier dependency priority. -/
theorem bar9_release_or_earlier (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X)
    (hNoFault : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y)
    (hLive : ∀ g, Frame.Pending L X g →
      ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d)) {g tag : Nat}
    (he : X.IsBarrier (g, (X.tr g).length - 1) 9 (some 128) tag) :
    ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)) ∧
      ((∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g) ∨
        ∃ other q, SameCta L g other ∧ Frame.Pending L X other ∧
          Frame.stateAt (Machine.code P L) X other (X.tr other).length = some (some q) ∧
          priority P L other q < priority P L g (.wg0 d)) := by
  have hg := Frame.lt_of_get hmax.1 he
  obtain ⟨earlier, hState, hSite, _, _, _⟩ :=
    Wg0BarrierTrace.bar9_at hpre hmax.1 (hs g hg).machine ht he rfl
  obtain ⟨d, hStep, hAfter⟩ := softmax_after_bar9_priority (P := P) (L := L)
    (g := g) (e := ⟨tag, .bar 9 (some 128) .sync⟩) hSite rfl
  have hLen : (X.tr g).length - 1 < (X.tr g).length := PTX.len_of_get he
  have hIndex : (X.tr g).length - 1 + 1 = (X.tr g).length := by omega
  have hTarget : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.wg0 d)) := by
    rw [← hIndex, Frame.stateAt_succ he, hState, Option.bind_some]
    change Machine.next P L g (.wg0 earlier) _ = _
    simp only [Machine.next, hStep]
    rfl
  refine ⟨d, hTarget, ?_⟩
  rcases bar9_release_or_missing hpre hmax hs ht hNoFault he with
    hReleased | ⟨other, hCta, hwg, hp, hCount⟩
  · exact .inl hReleased
  obtain ⟨q, hQ⟩ := hLive other hp
  refine .inr ⟨other, q, hCta, hp, hQ, ?_⟩
  obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.fired_site hs hmax.1 he hState
  have hSource : Wg0.Inv P L g earlier := hi
  have hRow : ctaidY L g = ctaidY L other := by simp only [ctaidY, ctaOf, hCta.2.2]
  rcases Wg0OutputVisits.softmax_state_cases hmax.1 hp.1 (hs other hp.1).machine hwg hQ with
    ⟨s, rfl⟩ | ⟨peer, rfl⟩ | rfl
  · exact (prologue_before_bar9_priority hSite).trans hAfter
  · obtain ⟨t, hRun⟩ := Frame.run_some hmax.1 hub hp
    obtain ⟨_, _, _, _, hI, _, _⟩ := Frame.end_at hs hp.1 hRun hQ
    have hPeer : Wg0.Inv P L other peer := hI
    rw [Wg0BarrierCount.count_at_wg0_tail hpre hmax.1 (hs other hp.1).machine hp.1 hQ,
      Wg0BarrierCount.count_at_wg0 hpre hmax.1 (hs g hg).machine he hState] at hCount
    exact lt_of_le_of_lt (softmax_before_bar9_priority hRow hSource hPeer hSite hCount) hAfter
  · have hSeen := count_after_done hpre hmax.1 hs hp.1 hwg hQ
    have hAtMost := observed_ord_le hpre hmax.1 hs ht he
    simp only [Wg0.blocksOf, Wg0.eOf, hRow] at hAtMost
    simp only [Wg0.blocksOf, Wg0.eOf] at hSeen
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
