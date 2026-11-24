-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingClosing
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Lemmas.Flow.NthEv

@[expose] public section

/-! # Actual named-barrier visits of an exiting softmax lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def pairSite (e : Event) : Bool := e.pc == 475

set_option maxRecDepth 100000 in
private theorem pair_window : stableRegisterWindow 2991 264 475 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem loop_window : stableRegisterWindow 2991 264 1122 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem body_bar_window : stableRegisterWindow 2991 264 569 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem lse_first_window : stableRegisterWindow 2991 1147 1154 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem lse_second_window : stableRegisterWindow 2991 1147 1156 = true := by
  decide +kernel

private theorem window_last_in_prefix {t : TState} {e : Event} {r low high : Nat}
    {before tail : List Event} {o : Option TState}
    (hWindow : stableRegisterWindow r low high = true)
    (hStart : inRegisterWindow low high t.pc) (hTag : high < e.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ f ∈ before, f.pc = high := by
  by_contra! hNone
  exact (not_le_of_gt hTag) (event_before_window_exit hWindow hStart hNone hRun)

private theorem lse_bar9_in_prefix {t : TState} {e : Event}
    {before tail : List Event} {o : Option TState}
    (hStart : t.pc = 1147) (hTag : 1156 < e.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    2 ≤ before.countP softmaxBodyBar9 := by
  obtain ⟨f, hf, hFirst⟩ := window_last_in_prefix lse_first_window
    (by change 1147 ≤ t.pc ∧ t.pc ≤ 1154; omega) (by omega) hRun
  obtain ⟨k, hk, hSecond⟩ := window_last_in_prefix lse_second_window
    (by change 1147 ≤ t.pc ∧ t.pc ≤ 1156; omega) hTag hRun
  have hNe : f ≠ k := by
    intro he
    rw [he, hSecond] at hFirst
    cases hFirst
  rw [List.countP_eq_length_filter]
  exact List.Nodup.length_le_of_subset (l₁ := [f, k]) (by simp [hNe]) (by
    intro x h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_filter.mpr ⟨hf, by simp [softmaxBodyBar9, hFirst]⟩
    · obtain rfl := List.mem_singleton.mp h
      exact List.mem_filter.mpr ⟨hk, by simp [softmaxBodyBar9, hSecond]⟩)

private theorem counts_before_epilogue {t : TState} {block total : Nat} {e : Event}
    {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : 1156 < e.pc) (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    total - block ≤ before.countP pairSite ∧
      2 * (total - block) + 1 ≤ before.countP softmaxBodyBar9 := by
  let seen := before.takeWhile (!isProbabilityPublication ·)
  let later := before.dropWhile (!isProbabilityPublication ·)
  have hSplit : before = seen ++ later := List.takeWhile_append_dropWhile.symm
  have hPrefix (f : Event) (hf : f ∈ seen) : f.pc ≠ 1122 := by
    have h := List.all_eq_true.mp List.all_takeWhile f hf
    exact (show f.pc ≠ Wg0.Site.soReady.pc by
      simpa [isProbabilityPublication, Bool.not_eq_true'] using h)
  cases hLater : later with
  | nil =>
    have hBefore : before = seen := by simpa only [hLater, List.append_nil] using hSplit
    have hEnd := event_before_window_exit loop_window
      (show inRegisterWindow 264 1122 t.pc by rw [hAt.1]; decide)
      (fun f hf => hPrefix f (hBefore ▸ hf)) hRun
    omega
  | cons pub remaining =>
    have hHead := List.head?_dropWhile_not (!isProbabilityPublication ·) before
    change before.dropWhile (!isProbabilityPublication ·) = pub :: remaining at hLater
    rw [hLater] at hHead
    have hPub : pub.pc = Wg0.Site.soReady.pc := by simpa [isProbabilityPublication] using hHead
    change before = seen ++ before.dropWhile (!isProbabilityPublication ·) at hSplit
    rw [hLater] at hSplit
    have hTrace : before ++ e :: tail = seen ++ pub :: (remaining ++ e :: tail) := by
      rw [hSplit, List.append_assoc, List.cons_append]
    rw [hTrace] at hRun
    have hPair : 0 < seen.countP pairSite := by
      obtain ⟨f, hf, hTag⟩ := window_last_in_prefix pair_window
        (show inRegisterWindow 264 475 t.pc by rw [hAt.1]; decide)
        (show 475 < pub.pc by rw [hPub]; decide) hRun
      exact List.countP_pos_iff.mpr ⟨f, hf, by simp [pairSite, hTag]⟩
    have hBar : 0 < seen.countP softmaxBodyBar9 := by
      obtain ⟨f, hf, hTag⟩ := window_last_in_prefix body_bar_window
        (show inRegisterWindow 264 569 t.pc by rw [hAt.1]; decide)
        (show 569 < pub.pc by rw [hPub]; decide) hRun
      exact List.countP_pos_iff.mpr ⟨f, hf, by simp [softmaxBodyBar9, hTag]⟩
    have hFacts : Holds t.regs (softmaxLoopFacts block total) := hAt.2.2.2.2.2.2.2.2
    obtain ⟨u, hu, hRegs, hPubRun⟩ := softmax_loop_facts_at_publication
      (by rw [hAt.1]; decide) (by rw [hAt.1]; decide) hFacts hPub hPrefix hRun
    by_cases hMore : block + 1 < total
    · have hNonempty : remaining ≠ [] := by
        intro hNil
        rw [hNil] at hPubRun
        obtain ⟨v, hLocal, hv, hRun'⟩ :=
          softmax_next_head_after_publication hMore hLimit hu hRegs hPubRun (by simp)
        have hFirst := softmax_opening_event_bound hv.1 (after_softmax_local_prefix hLocal hRun')
        omega
      obtain ⟨opening, rest, rfl⟩ := List.exists_cons_of_ne_nil hNonempty
      have hOpening : softmaxBodyBar9 opening = true := by
        obtain ⟨v, hv, hV, hOpen⟩ := softmax_next_head_after_publication hMore hLimit hu hRegs
          hPubRun (by simp)
        have hp := head_barrier_tag hV.1 (after_softmax_local_prefix hv hOpen) (by simp)
        simp [softmaxBodyBar9, hp]
      obtain ⟨poll, after, hEq⟩ := List.exists_cons_of_ne_nil
        (show rest ++ e :: tail ≠ [] by simp)
      rw [List.cons_append, hEq] at hPubRun
      obtain ⟨v, hv, hRest⟩ :=
        softmax_next_mask_after_publication hpre hMore hLimit hu hRegs hPubRun
      rw [← hEq] at hRest
      obtain ⟨hPairs, hBars⟩ := counts_before_epilogue hpre hMore hLimit hv hTag hRest
      rw [hSplit]
      constructor
      · rw [List.countP_append, List.countP_cons, List.countP_cons]
        omega
      · rw [List.countP_append, List.countP_cons, List.countP_cons, hOpening, ite_eq_left rfl]
        omega
    · have hFinal : total = block + 1 := by omega
      have hLimit' : block + 1 < 2 ^ 31 := by omega
      rw [hFinal] at hRegs
      obtain ⟨v, hv, hPc, hTail⟩ :=
        softmax_final_head_after_publication hLimit' hu hRegs hPubRun (by simp)
      have hSuffix : Run kernel Assumptions.all L g v (remaining ++ e :: tail) o := by
        obtain ⟨head, suffix, he⟩ := List.exists_cons_of_ne_nil
          (show remaining ++ e :: tail ≠ [] by simp)
        rw [he] at hTail ⊢
        exact after_softmax_local_prefix hv hTail
      have hBars := lse_bar9_in_prefix hPc hTag hSuffix
      rw [hSplit]
      constructor
      · rw [List.countP_append]
        omega
      · rw [List.countP_append, List.countP_cons]
        omega
termination_by before.length
decreasing_by
  simp only [hSplit, List.length_append, List.length_cons]
  omega

/-- An exiting softmax lane has covered every loop barrier and the LSE handoff. -/
theorem barrier_counts_before_softmax_exit {closing tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hwg : wgOf L g = 0) (he : X.get (g, closing) = some ⟨tag, .exit⟩) :
    Wg0.blocksOf P L g ≤
      ((X.tr g).take closing).countP (Execution.isBarId (10 + warpOf L g % 2)) ∧
    2 * Wg0.blocksOf P L g + 2 ≤ ((X.tr g).take closing).countP (Execution.isBarId 9) := by
  obtain ⟨start, hBefore, hAnchor⟩ := first_mask_of_softmax_exit hpre hX hs hwg he
  let events := (X.tr g).drop start
  let k := closing - start
  have hGet : events[k]? = some ⟨tag, .exit⟩ := by
    change ((X.tr g).drop start)[closing - start]? = _
    rw [List.getElem?_drop, Nat.add_sub_of_le hBefore]
    exact he
  obtain ⟨d, hd, hFirst, hState⟩ := hAnchor
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hState
    (List.ne_nil_of_mem (List.mem_of_getElem? hGet))
  have hAt := softmax_mask_entry_facts hd (show (Wg0.code P L g).AtD d t from hGood.1)
  have hBlock := (show Wg0.Inv P L g d from hGood.2).blockLt
  have hTotal : Wg0.blocksOf P L g < 2 ^ 31 := by
    have h := (Wg0.blocksOf_word_bounds hpre (Wg1Mma.batchOf_lt hpre hg)).2
    omega
  have hCut : events = events.take k ++ ⟨tag, .exit⟩ :: events.drop (k + 1) := by
    have hDrop := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hGet).1
    rw [(List.getElem?_eq_some_iff.mp hGet).2] at hDrop
    rw [← hDrop]
    exact (List.take_append_drop ..).symm
  change Run kernel Assumptions.all L g t events o at hRun
  rw [hCut] at hRun
  have hTag := actual_exit_tag hX he
  obtain ⟨hPairs, hBars⟩ := counts_before_epilogue hpre hBlock hTotal hAt
    (show 1156 < tag by omega) hRun
  rw [hFirst, Nat.sub_zero] at hPairs hBars
  have count_mono (p q : Event → Bool)
      (hImpl : ∀ j f, start ≤ j → X.get (g, j) = some f → j + 1 < (X.tr g).length →
        p f = true → q f = true) : (events.take k).countP p ≤ (events.take k).countP q := by
    apply List.countP_mono_left
    intro f hf hSite
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hf
    have hjk : j < k :=
      lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hj).1 (by simp)
    rw [List.getElem?_take_of_lt hjk] at hj
    have hEvent : X.get (g, start + j) = some f := by
      change (X.tr g)[start + j]? = _
      simpa only [events, List.getElem?_drop] using hj
    have hLater : start + j + 1 < (X.tr g).length := by
      have hout : closing < (X.tr g).length := PTX.len_of_get he
      dsimp only [k] at hjk
      omega
    exact hImpl _ _ (Nat.le_add_right ..) hEvent hLater hSite
  let p := Execution.isBarId (10 + warpOf L g % 2)
  have hSubsetPair := count_mono pairSite p (fun j f hLe hEvent hLater hSite => by
    have hKind := softmax_pair_at_site hpre hX hs ⟨d, hd, hFirst, hState⟩ hLe
      hEvent (by simpa [pairSite] using hSite) hLater
    simp [p, Execution.isBarId, hKind])
  have hSubsetBar := count_mono softmaxBodyBar9 (Execution.isBarId 9)
    (fun j f hLe hEvent hLater hSite => by
      have hKind := softmax_bar9_at_site hpre hX hs ⟨d, hd, hFirst, hState⟩ hLe hEvent hSite hLater
      simp [Execution.isBarId, hKind])
  have hTake : (X.tr g).take closing = (X.tr g).take start ++ events.take k := by
    dsimp only [events, k]
    rw [← List.take_add, Nat.add_sub_of_le hBefore]
  rw [hTake]
  constructor
  · rw [List.countP_append]
    change _ ≤ _ + (events.take k).countP p
    omega
  · have hLen : start < (X.tr g).length := hBefore.trans_lt (PTX.len_of_get he)
    have hStart : X.get (g, start) = some ((X.tr g)[start]'hLen) :=
      List.getElem?_eq_getElem hLen
    have hOpening := Wg0BarrierCount.count_at_wg0 hpre hX (hs g hg).machine hStart hState
    rw [Wg0BarrierCount.ordinal, hd] at hOpening
    change ((X.tr g).take start).countP (Execution.isBarId 9) = 2 * d.block + 1 at hOpening
    rw [List.countP_append, hOpening]
    omega

/-- Every block has an actual pair-barrier arrival in an exiting softmax lane. -/
theorem pair_count_before_softmax_exit {closing tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hwg : wgOf L g = 0) (he : X.get (g, closing) = some ⟨tag, .exit⟩) :
    Wg0.blocksOf P L g ≤
      ((X.tr g).take closing).countP (Execution.isBarId (10 + warpOf L g % 2)) :=
  (barrier_counts_before_softmax_exit hpre hX hs hwg he).1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
