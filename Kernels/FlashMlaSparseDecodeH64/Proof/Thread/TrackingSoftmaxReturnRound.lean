-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxMaskControl

@[expose] public section

/-! # A mask slot is returned only once per concrete softmax block -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxRecDepth 100000 in
private theorem post_return_window : stableRegisterWindow 2883 572 1122 = true := by
  decide +kernel

/-- A softmax lane has to publish between two of its slot releases. -/
theorem no_second_return_before_publication {t : TState} {first second : Event}
    {before between tail : List Event} {o : Option TState}
    (hStart : first.pc = Wg0.Site.validFree.pc) (hEnd : second.pc = Wg0.Site.validFree.pc)
    (hBefore : ∀ f ∈ between, f.pc ≠ Wg0.Site.soReady.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ first :: (between ++ second :: tail)) o) :
    False := by
  obtain ⟨v, _, hSuffix⟩ := run_split_nonempty hRun (by simp)
  generalize hList : first :: (between ++ second :: tail) = events at hSuffix
  cases hSuffix with
  | nil => cases hList
  | @step _ src _ _ _ _ hTau hStep hRest =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hList
    have hp := (estep_source_pc hStep).symm.trans hStart
    change _ = 571 at hp
    have hc := Flow.code_571
    rw [← hp] at hc
    obtain ⟨rfl, _⟩ := softmax_unit_arrival_return hc hStep
    have hPc : (PTX.next src).pc = 572 := by
      change src.pc + 1 = 572
      rw [hp]
    obtain ⟨q, r, _, hLo, hHi, _, hLocal, hFired⟩ :=
      register_at_event_in_window post_return_window Flow.code_1121 rfl
        (by rw [hPc]) (by simpa only [hPc] using (by decide : 572 < 1122)) hBefore hRest
    have hBounds := local_path_in_register_window post_return_window ⟨hLo, hHi.le⟩ hLocal
    have hTag := estep_source_pc hFired
    rw [hEnd] at hTag
    have hLower : 572 ≤ r.pc := hBounds.1
    change 571 = r.pc at hTag
    omega
  | last =>
    have hNil := (List.cons.inj hList).2
    simp at hNil

/-- A chosen return before the block's probability publication releases the same slot
as its preceding successful acquire. The returned index is in the exact trace prefix. -/
theorem softmax_return_before_publication {block total : Nat} {t : TState} {e : Event}
    {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = Wg0.Site.validFree.pc)
    (hBefore : ∀ f ∈ before, f.pc ≠ Wg0.Site.soReady.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validFreeOff (block % 4)⟩
        0 1 true .cta ∧
      ∃ j < before.length, (before ++ e :: tail)[j]? = some
        ⟨264, .wait ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validReadyOff (block % 4)⟩
          (block / 4 % 2) true true .cta⟩ := by
  have hNoEarlier : ∀ f ∈ before, f.pc ≠ Wg0.Site.validFree.pc := by
    intro f hf hFirst
    obtain ⟨pre, between, hList⟩ := List.mem_iff_append.mp hf
    have hWithin : ∀ a ∈ between, a.pc ≠ Wg0.Site.soReady.pc := by
      intro a ha
      apply hBefore a
      rw [hList]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
    rw [hList, List.append_assoc, List.cons_append] at hRun
    exact no_second_return_before_publication hFirst hTag hWithin hRun
  have h477 : t.regs 477 = some (b32 (L.sharedBase + 8 * (block % 4))) :=
    hAt.2.2.2.2.2.2.1
  let slot : Fin 4 := ⟨block % 4, Nat.mod_lt _ (by decide)⟩
  have hSlot := softmax_return_in_register_window hpre slot
    (by rw [hAt.1]; decide) (by rw [hAt.1]; decide) h477 hTag hNoEarlier hRun
  have he : (before ++ e :: tail)[before.length]? = some e := by simp
  exact ⟨hSlot, successful_softmax_mask_poll_before_return hpre hAt hRun he hTag⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
