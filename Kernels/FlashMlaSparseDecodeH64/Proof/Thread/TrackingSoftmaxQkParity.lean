-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxMaskWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxPvWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteRegs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantInputs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0GemmTrace

@[expose] public section

/-! # Actual successful QK waits alternate in each slot -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof Protocol Protocol.GemmRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i cta : Nat}
variable {slot : Fin 2} {e : Event}

/-- Every dismissed softmax lane has already entered its first mask acquire. -/
theorem mask_anchor_after_dismissal
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hDismiss : Frame.stateAt (Machine.code P L) X g i = some none) :
    ∃ start ≤ i, ∃ d : Wg0.D, d.site = .maskReady ∧ d.block = 0 ∧
      Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 d)) := by
  have hg := Frame.lt_of_get hX he
  have hWg : wgOf L g = 0 := by
    by_contra hn
    exact tracked_nonsoftmax_wg hpre hX hs hn i hDismiss
  obtain ⟨j, hj, d, f, hf, hState, hNext⟩ := prior_dismissal (PTX.len_of_get he).le hDismiss
  have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
  cases dismissal_is_consumer hpre hX hs hf hState hNext with
  | wg0 d =>
    obtain ⟨start, hLe, hAnchor⟩ := dismissed_wg0_first_mask_ready hpre hX hs hf hState hNext
    exact ⟨start, by omega, hAnchor⟩
  | wg2 d => change wgOf L g = 2 at hRole; omega

private theorem selected_suffix_from_mask {start : Nat} {initial : Wg0.D}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hLe : start ≤ i) (hSite : initial.site = .maskReady)
    (hAnchor : Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 initial))) :
    ∃ t o, initial.block < Wg0.blocksOf P L g ∧
      AtVector t 264 (softmaxMaskFacts L initial.block (Wg0.blocksOf P L g)) t.sub t.acc ∧
      Run kernel Assumptions.all L g t
        ((((X.tr g).drop start).take (i - start)) ++ e :: (X.tr g).drop (i + 1)) o := by
  let events := (X.tr g).drop start
  let k := i - start
  have hGet : events[k]? = some e := by
    change ((X.tr g).drop start)[i - start]? = _
    rw [List.getElem?_drop, Nat.add_sub_of_le hLe]
    exact he
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hAnchor
    (List.ne_nil_of_mem (List.mem_of_getElem? hGet))
  have hAt := softmax_mask_entry_facts hSite (show (Wg0.code P L g).AtD initial t from hGood.1)
  have hBlock := (show Wg0.Inv P L g initial from hGood.2).blockLt
  have hShort : k < events.length := (List.getElem?_eq_some_iff.mp hGet).1
  have hSplit : events = events.take k ++ e :: (X.tr g).drop (i + 1) := by
    have hDrop := List.drop_eq_getElem_cons hShort
    rw [(List.getElem?_eq_some_iff.mp hGet).2] at hDrop
    have hTail : events.drop (k + 1) = (X.tr g).drop (i + 1) := by
      dsimp only [events]
      rw [List.drop_drop, show start + (k + 1) = i + 1 by dsimp [k]; omega]
    rw [← hTail, ← hDrop]
    exact (List.take_append_drop ..).symm
  change Run kernel Assumptions.all L g t events o at hRun
  rw [hSplit] at hRun
  exact ⟨t, o, hBlock, hAt, hRun⟩

/-- The actual successful PV wait before an output operation names its last block. -/
theorem actual_pv_acquire_before_output {start : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hBefore : start ≤ i) (hLater : 1184 < e.pc)
    (hSite : d.site = .maskReady)
    (hState : Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 d))) :
    let block := Wg0.blocksOf P L g - 1
    ∃ w < i, start ≤ w ∧ ∃ sc, X.get (g, w) = some
      ⟨1184, .wait (Object.svDone.loc L (ctaOf L g) (rawSlot block))
        (block / 2 % 2) true true sc⟩ := by
  obtain ⟨t, o, hBlock, hAt, hRun⟩ := selected_suffix_from_mask hX hs he hBefore hSite hState
  have hg := Frame.lt_of_get hX he
  have hTotal : Wg0.blocksOf P L g < 2 ^ 31 := by
    have h := (Wg0.blocksOf_word_bounds hpre (Wg1Mma.batchOf_lt hpre hg)).2
    omega
  obtain ⟨j, hj, sc, hGet⟩ := pv_acquire_before_output_in_run hpre hBlock hTotal hAt hLater hRun
  simp only [List.length_take] at hj
  have hj' : j < i - start := by omega
  rw [List.getElem?_take_of_lt hj', List.getElem?_drop] at hGet
  exact ⟨start + j, by omega, Nat.le_add_right _ _, sc, hGet⟩

private theorem softmax_poll_sites (hSite : e.pc ∈ Flow.mbarWait.toList)
    (hRegion : softmaxWriteRegion e.pc) :
    e.pc = 264 ∨ e.pc = 272 ∨ e.pc = 1184 := by
  have hList : Flow.mbarWait.toList =
      [264, 272, 1184, 1931, 1983, 2012, 2107, 2205, 2209, 2234, 2245, 2446, 2534,
        2644, 2677, 2684] := by decide +kernel
  rw [hList] at hSite
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  unfold softmaxWriteRegion at hRegion
  omega

/-- A dismissed softmax lane only polls the mask ring, QK ring, and final PV slot. -/
theorem dismissed_softmax_wait_range {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .wait m p ok acq sc)
    (hDismiss : Frame.stateAt (Machine.code P L) X g i = some none) :
    (L.sharedBase + 222840 ≤ m.addr ∧ m.addr < L.sharedBase + 222872) ∨
      (e.pc = 272 ∧ L.sharedBase + 222904 ≤ m.addr) ∨ L.sharedBase + 222936 ≤ m.addr := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨start, hLe, initial, hSite, _, hAnchor⟩ :=
    mask_anchor_after_dismissal hpre hX hs he hDismiss
  obtain ⟨t, o, hBlock, hAt, hRun⟩ := selected_suffix_from_mask hX hs he hLe hSite hAnchor
  have hTotal : Wg0.blocksOf P L g < 2 ^ 31 := by
    have h := (Wg0.blocksOf_word_bounds hpre (Wg1Mma.batchOf_lt hpre hg)).2
    omega
  have hRegion := run_in_control_region softmax_write_region_closed
    (show softmaxWriteRegion t.pc from hAt.1.symm ▸ by decide)
    hRun e (List.mem_append_right _ List.mem_cons_self)
  rcases softmax_poll_sites (RingSourceSites.actual_wait_pc hX he hk) hRegion with h | h | h
  · obtain ⟨visit, _, hMask⟩ := mask_wait_in_trace hpre hBlock hTotal hAt h hRun
    have hAddr := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans hMask)).1
    change m.addr = L.sharedBase + (222840 + 8 * (visit % 4)) at hAddr
    exact .inl ⟨by omega, by omega⟩
  · obtain ⟨_, _, _, hEvent⟩ := softmax_qk_poll_in_trace 0 hpre hBlock hTotal hAt h hRun
    have hAddr := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans hEvent)).1
    exact .inr (.inl ⟨h, by simp only at hAddr; omega⟩)
  · have hLoc := (pv_wait_shape_in_trace hpre hBlock hTotal hAt h hk hRun).1
    have hAddr := congrArg Loc.addr hLoc
    change m.addr = L.sharedBase + (222936 + 8 * ((Wg0.blocksOf P L g - 1) % 2)) at hAddr
    exact .inr (.inr (by omega))

private theorem qk_wait_site {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hk : e.kind = .wait (Object.qkDone.loc L cta slot) p ok acq sc) :
    e.pc = 272 := by
  have hg := Frame.lt_of_get hX he
  by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
  · rcases dismissed_softmax_wait_range hpre hX hs he hk hDismiss with h | ⟨hPc, _⟩ | h
    · change _ ∧ L.sharedBase + (222904 + 8 * slot.val) < _ at h
      omega
    · exact hPc
    · change _ ≤ L.sharedBase + (222904 + 8 * slot.val) at h
      have := slot.isLt
      omega
  · obtain ⟨⟨_, d, _, _, hSite, hState⟩, _⟩ :=
      poll_at_followed hpre hX (hs g hg).machine hDismiss he hk
    have hTag := Frame.event_pc hs hX he hState
    change e.pc = d.site.pc at hTag
    rw [hTag, hSite]
    rfl

/-- A successful actual QK acquire has the phase of its lane's earlier acquires on that slot. -/
theorem actual_qk_alternates {tag p : Nat} {acq : Bool} {sc : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .wait (Object.qkDone.loc L cta slot) p true acq sc⟩) :
    p % 2 = Flow.okPolls (Object.qkDone.loc L cta slot) ((X.tr g).take i) % 2 := by
  let qk := Object.qkDone.loc L cta slot
  have hg := Frame.lt_of_get hX he
  by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨start, hLe, initial, hSite, hFirst, hAnchor⟩ :=
      mask_anchor_after_dismissal hpre hX hs he hDismiss
    obtain ⟨t, o, hBlock, hAt, hRun⟩ := selected_suffix_from_mask hX hs he hLe hSite hAnchor
    have hTotal : Wg0.blocksOf P L g < 2 ^ 31 := by
      have h := (Wg0.blocksOf_word_bounds hpre (Wg1Mma.batchOf_lt hpre hg)).2
      omega
    let before := ((X.tr g).drop start).take (i - start)
    let visit := before.countP isProbabilityPublication
    have hTag : tag = 272 := qk_wait_site hpre hX hs he rfl
    obtain ⟨hCount, ok, scope, hk⟩ :=
      softmax_qk_poll_in_trace slot hpre hBlock hTotal hAt hTag hRun
    rw [hFirst, Nat.zero_add] at hCount hk
    change Kind.wait qk p true acq sc = _ at hk
    obtain ⟨hLoc, hp, _, _, _⟩ := Kind.wait.inj hk
    have hc : ctaOf L g = cta := (congrArg Loc.cta hLoc).symm
    have hSlot : slot.val = visit % 2 := by
      have hAddr := congrArg Loc.addr hLoc
      change L.sharedBase + (222904 + 8 * slot.val) =
        L.sharedBase + (222904 + 8 * (visit % 2)) at hAddr
      omega
    change p = visit / 2 % 2 at hp
    have hZero := Wg0GemmTrace.qk_successes_at_first_mask hpre slot
      ((hs g hg).machine.produces (hX.thr g hg)) hAnchor hSite hFirst
    rw [hc] at hZero hCount
    have hEq : before.countP (okPoll qk) = before.countP (successfulQkPoll qk) := by
      apply List.countP_congr
      intro f hf
      constructor
      · intro hPoll
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hf)
        have hEvent : X.get (g, start + j) = some f := by
          change (X.tr g)[start + j]? = _
          simpa only [List.getElem?_drop] using hj
        have hKind : ∃ parity acq scope, f.kind = .wait qk parity true acq scope := by
          unfold okPoll sourceWaitSuccess at hPoll
          split at hPoll
          · rename_i loc parity acq scope hKind
            exact ⟨parity, acq, scope, of_decide_eq_true hPoll ▸ hKind⟩
          · cases hPoll
        obtain ⟨parity, acq, scope, hKind⟩ := hKind
        have hfTag := qk_wait_site hpre hX hs hEvent hKind
        simp [successfulQkPoll, hfTag, hPoll]
      · intro hf
        exact (Bool.and_eq_true_iff.mp hf).2
    have hTake : (X.tr g).take i = (X.tr g).take start ++ before := by
      dsimp only [before]
      rw [← List.take_add, Nat.add_sub_of_le hLe]
    change ((X.tr g).take start).countP (okPoll qk) = 0 at hZero
    change before.countP (successfulQkPoll qk) =
      (visit + (1 - slot.val)) / 2 - (0 + (1 - slot.val)) / 2 at hCount
    change p % 2 = Flow.okPolls qk ((X.tr g).take i) % 2
    rw [hTake, Flow.okPolls, List.countP_append, hZero, Nat.zero_add, hEq, hCount]
    have := slot.isLt
    omega
  · obtain ⟨⟨hc, d, hb, hp, hSite, hState⟩, _⟩ :=
      poll_at_followed hpre hX (hs g hg).machine hDismiss he rfl
    have hCount := Wg0GemmTrace.composed_qk_counts hpre
      ((hs g hg).machine.produces (hX.thr g hg)) hState hSite
    rw [hc, hb] at hCount
    change p % 2 = Flow.okPolls qk ((X.tr g).take i) % 2
    change Flow.okPolls qk ((X.tr g).take i) = d.block / 2 at hCount
    rw [hp, hCount, Nat.mod_mod]

/-- A successful native QK poll on a softmax lane is an acquire. -/
theorem actual_qk_wait_is_acquire {tag p : Nat} {acq : Bool} {sc : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hWg : wgOf L g = 0)
    (he : X.get (g, i) = some ⟨tag, .wait (Object.qkDone.loc L cta slot) p true acq sc⟩) :
    acq = true := by
  have hTag := qk_wait_site hpre hX hs he rfl
  obtain ⟨block, hKind⟩ := actual_softmax_qk_wait hpre hX hs he hWg hTag rfl
  exact (Kind.wait.inj hKind).2.2.2.1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
