-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingClosing
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkControl

@[expose] public section

/-! # Every QK slot use is acquired before the softmax closing gate -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame Protocol.GemmRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

set_option maxRecDepth 100000 in
private theorem loop_window : stableRegisterWindow 2991 264 1122 = true := by
  decide +kernel

private theorem exact_qk_count_to_epilogue {t : TState} {block total : Nat} {e : Event}
    {before tail : List Event} {o : Option TState} (slot : Fin 2)
    (hpre : Pre P L mem0) (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : 1122 < e.pc) (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    before.countP (successfulQkPoll (Object.qkDone.loc L (ctaOf L g) slot)) =
      (total + (1 - slot.val)) / 2 - (block + (1 - slot.val)) / 2 := by
  let qk := Object.qkDone.loc L (ctaOf L g) slot
  let seen := before.takeWhile (!isProbabilityPublication ·)
  let later := before.dropWhile (!isProbabilityPublication ·)
  have hSplit : before = seen ++ later := List.takeWhile_append_dropWhile.symm
  have hPrefix : ∀ f ∈ seen, f.pc ≠ 1122 := by
    intro f hf
    have h := List.all_eq_true.mp List.all_takeWhile f hf
    exact (show f.pc ≠ Wg0.Site.soReady.pc by
      simpa [isProbabilityPublication, Bool.not_eq_true'] using h)
  cases hLater : later with
  | nil =>
    have hBefore : before = seen := by simpa only [hLater, List.append_nil] using hSplit
    obtain ⟨_, _, _, hFirst, hLast, _, hLocal, hFire⟩ :=
      register_at_event_in_window loop_window Flow.code_1121 rfl hAt.1.ge
        (hAt.1 ▸ by decide) (fun f hf => hPrefix f (hBefore ▸ hf)) hRun
    have hRegion := local_path_in_register_window loop_window ⟨hFirst, hLast.le⟩ hLocal
    rw [← estep_source_pc hFire] at hRegion
    exact (not_le_of_gt hTag hRegion.2).elim
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
    have hThis := softmax_qk_count_in_round (m := qk) hpre hAt hPub hPrefix hRun
    have hOne :
        (if qk = ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩ then 1 else 0) =
          (block + 1 + (1 - slot.val)) / 2 - (block + (1 - slot.val)) / 2 := by
      have hEq : qk = ⟨.shared, ctaOf L g, L.sharedBase + (222904 + 8 * (block % 2))⟩ ↔
          slot.val = block % 2 := by
        simp only [qk, Object.loc, Object.base, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
        omega
      simp only [hEq]
      have := slot.isLt
      split <;> omega
    rw [hOne] at hThis
    have hFacts : Holds t.regs (softmaxLoopFacts block total) := hAt.2.2.2.2.2.2.2.2
    obtain ⟨u, hu, hRegs, hPubRun⟩ := softmax_loop_facts_at_publication
      (by rw [hAt.1]; decide) (by rw [hAt.1]; decide) hFacts hPub hPrefix hRun
    have hNotPub : successfulQkPoll qk pub = false := by
      have hp : pub.pc = 1122 := hPub
      simp [successfulQkPoll, hp]
    change before.countP (successfulQkPoll qk) = _
    by_cases hMore : block + 1 < total
    · have hNonempty : remaining ≠ [] := by
        intro hNil
        rw [hNil] at hPubRun
        obtain ⟨v, hLocal, hv, hRun'⟩ :=
          softmax_next_head_after_publication hMore hLimit hu hRegs hPubRun (by simp)
        have hFirst := softmax_opening_event_bound hv.1 (after_softmax_local_prefix hLocal hRun')
        omega
      obtain ⟨opening, rest, rfl⟩ := List.exists_cons_of_ne_nil hNonempty
      have hOpening : opening.pc ≤ 256 := by
        obtain ⟨v, hv, hV, hOpen⟩ := softmax_next_head_after_publication hMore hLimit hu hRegs
          hPubRun (by simp)
        exact softmax_opening_event_bound hV.1 (after_softmax_local_prefix hv hOpen)
      obtain ⟨poll, after, hEq⟩ := List.exists_cons_of_ne_nil
        (show rest ++ e :: tail ≠ [] by simp)
      rw [List.cons_append, hEq] at hPubRun
      obtain ⟨v, hv, hRest⟩ :=
        softmax_next_mask_after_publication hpre hMore hLimit hu hRegs hPubRun
      rw [← hEq] at hRest
      have hRec := exact_qk_count_to_epilogue slot hpre hMore hLimit hv hTag hRest
      have hOpen : successfulQkPoll qk opening = false := by
        simp [successfulQkPoll, show opening.pc ≠ 272 from by omega]
      rw [hSplit, List.countP_append, hThis]
      simp only [List.countP_cons, hNotPub, hOpen, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      change rest.countP (successfulQkPoll qk) = _ at hRec
      rw [hRec]
      omega
    · have hFinal : total = block + 1 := by omega
      subst total
      have hZero : remaining.countP (successfulQkPoll qk) = 0 := by
        apply List.countP_eq_zero.mpr
        intro f hf
        have hLo := event_after_final_publication_lower hLimit hu hRegs hPubRun
          (List.mem_append_left _ hf)
        simp [successfulQkPoll, show f.pc ≠ 272 from by omega]
      rw [hSplit, List.countP_append, hThis]
      simp [hNotPub, hZero]
termination_by before.length
decreasing_by
  simp only [hSplit, List.length_append, List.length_cons]
  omega

/-- A softmax lane in its epilogue has acquired every QK use of the slot in its CTA. -/
theorem actual_qk_count_in_epilogue {start closing : Nat} {e : Event} (slot : Fin 2)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hAnchor : FirstMaskAnchor P L X g start) (hBefore : start ≤ closing)
    (he : X.get (g, closing) = some e) (hTag : 1122 < e.pc) :
    (Wg0.blocksOf P L g + (1 - slot.val)) / 2 ≤
      okPolls (Object.qkDone.loc L (ctaOf L g) slot) ((X.tr g).take closing) := by
  let events := (X.tr g).drop start
  let k := closing - start
  let qk := Object.qkDone.loc L (ctaOf L g) slot
  have hGet : events[k]? = some e := by
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
  have hCut : events = events.take k ++ e :: events.drop (k + 1) := by
    have hDrop := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hGet).1
    rw [(List.getElem?_eq_some_iff.mp hGet).2] at hDrop
    rw [← hDrop]
    exact (List.take_append_drop ..).symm
  change Run kernel Assumptions.all L g t events o at hRun
  rw [hCut] at hRun
  have hCount := exact_qk_count_to_epilogue slot hpre hBlock hTotal hAt hTag hRun
  have hOffset : (d.block + (1 - slot.val)) / 2 = 0 := by rw [hFirst]; omega
  rw [hOffset, Nat.sub_zero] at hCount
  have hSubset :
      (events.take k).countP (successfulQkPoll qk) ≤ (events.take k).countP (okPoll qk) :=
    List.countP_mono_left (fun f _ h => (Bool.and_eq_true_iff.mp h).2)
  have hTake : (X.tr g).take closing = (X.tr g).take start ++ events.take k := by
    dsimp only [events, k]
    rw [← List.take_add, Nat.add_sub_of_le hBefore]
  change _ ≤ okPolls qk ((X.tr g).take closing)
  rw [hTake, Flow.okPolls, List.countP_append]
  change (events.take k).countP (successfulQkPoll qk) = _ at hCount
  omega

/-- A softmax closing lane has acquired every QK use of the slot in its CTA. -/
theorem actual_qk_count_before_gate {start closing : Nat} (slot : Fin 2)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hAnchor : FirstMaskAnchor P L X g start) (hBefore : start ≤ closing)
    (he : X.get (g, closing) = some ⟨1835, .bar 12 none .sync⟩) :
    (Wg0.blocksOf P L g + (1 - slot.val)) / 2 ≤
      okPolls (Object.qkDone.loc L (ctaOf L g) slot) ((X.tr g).take closing) :=
  actual_qk_count_in_epilogue slot hpre hX hs hAnchor hBefore he (by decide)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
