-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterWindow

@[expose] public section

/-! # Mask poll addresses in actual softmax rounds -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxRecDepth 100000 in
private theorem after_mask_window : stableRegisterWindow 2953 272 1122 = true := by
  decide +kernel

private theorem mask_wait_in_round {t : TState} {block total : Nat} {e : Event}
    {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = 264) (hNoPub : ∀ f ∈ before, f.pc ≠ 1122)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ ok, e.kind = .wait
      ⟨.shared, ctaOf L g, L.sharedBase + (222840 + 8 * (block % 4))⟩
      (block / 4 % 2) ok true .cta := by
  induction before generalizing t with
  | nil =>
    have hOut := mask_poll_template (g := g) hpre hAt
    cases hRun with
    | step hTau hStep _ =>
      rw [stop_unique hTau .refl (stops_of_estep hStep) ⟨_, hOut⟩] at hStep
      obtain ⟨m, hm, hf⟩ := hStep
      rw [hOut] at hm
      cases hm
      obtain ⟨ok, he, _⟩ := hf
      exact ⟨ok, congrArg Event.kind he⟩
    | last hTau hStep =>
      rw [stop_unique hTau .refl (stops_of_estep hStep) ⟨_, hOut⟩] at hStep
      obtain ⟨m, hm, hf⟩ := hStep
      rw [hOut] at hm
      cases hm
      obtain ⟨_, _, hState⟩ := hf
      cases hState
  | cons f before ih =>
    have hTail : before ++ e :: tail ≠ [] := by simp
    obtain ⟨ok, _, hRest⟩ := softmax_mask_poll_from_run hpre hAt hRun hTail
    change Run kernel Assumptions.all L g _ (before ++ e :: tail) o at hRest
    obtain ⟨front, after, hEq⟩ := List.exists_cons_of_ne_nil hTail
    rw [hEq] at hRest
    have hPrefix (f : Event) (hf : f ∈ before) : f.pc ≠ 1122 :=
      hNoPub f (List.mem_cons_of_mem _ hf)
    cases ok with
    | false =>
      obtain ⟨u, hu, hU⟩ := retry_mask_poll hAt
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      exact ih hU hPrefix hSuffix
    | true =>
      obtain ⟨u, hu, hU⟩ := softmax_qk_setup hpre hAt
      have hSuffix := after_softmax_local_prefix hu hRest
      rw [← hEq] at hSuffix
      obtain ⟨v, _, _, hFirst, hLast, _, hLocal, hFire⟩ :=
        register_at_event_in_window after_mask_window Flow.code_1121 rfl hU.1.ge
          (hU.1 ▸ by decide) hPrefix hSuffix
      have hRegion := local_path_in_register_window after_mask_window ⟨hFirst, hLast.le⟩ hLocal
      rw [← estep_source_pc hFire, hTag] at hRegion
      exact ((by decide : ¬ inRegisterWindow 272 1122 264) hRegion).elim

/-- A mask poll after the first loop entry reads the mask ring of its current block. -/
theorem mask_wait_in_trace {t : TState} {block total : Nat} {e : Event}
    {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = 264) (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ visit ok, e.kind = .wait
      ⟨.shared, ctaOf L g, L.sharedBase + (222840 + 8 * (visit % 4))⟩
      (visit / 4 % 2) ok true .cta := by
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
    exact ⟨block, mask_wait_in_round hpre hAt hTag (fun f hf => hPrefix f (hBefore ▸ hf)) hRun⟩
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
        rw [hTag] at hFirst
        omega
      obtain ⟨opening, rest, rfl⟩ := List.exists_cons_of_ne_nil hNonempty
      obtain ⟨poll, after, hEq⟩ := List.exists_cons_of_ne_nil
        (show rest ++ e :: tail ≠ [] by simp)
      rw [List.cons_append, hEq] at hPubRun
      obtain ⟨v, hv, hRest⟩ :=
        softmax_next_mask_after_publication hpre hMore hLimit hu hRegs hPubRun
      rw [← hEq] at hRest
      exact mask_wait_in_trace hpre hMore hLimit hv hTag hRest
    · have hFinal : total = block + 1 := by omega
      subst total
      have hNo := event_after_final_publication_lower hLimit hu hRegs hPubRun
        (List.mem_append_right remaining List.mem_cons_self)
      rw [hTag] at hNo
      omega
termination_by before.length
decreasing_by
  simp only [hSplit, List.length_append, List.length_cons]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
