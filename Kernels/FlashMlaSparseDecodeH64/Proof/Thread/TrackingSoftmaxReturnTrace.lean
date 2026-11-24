-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnRound
import Lemmas.Protocol.ClusterTrace

@[expose] public section

/-! # The block and preceding acquire of any actual softmax slot return -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Identify the publication that closes the current softmax loop block. -/
def isProbabilityPublication (e : Event) : Bool := e.pc == Wg0.Site.soReady.pc

/-- The block of a concrete mask release is determined by the preceding probability
publications. The preceding successful acquire belongs to exactly that slot use. -/
theorem softmax_return_in_trace {block total : Nat} {t : TState} {e : Event}
    {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = Wg0.Site.validFree.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ visit, visit = block + before.countP isProbabilityPublication ∧ visit < total ∧
      e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validFreeOff (visit % 4)⟩
        0 1 true .cta ∧
      ∃ j < before.length, (before ++ e :: tail)[j]? = some
        ⟨264, .wait ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validReadyOff (visit % 4)⟩
          (visit / 4 % 2) true true .cta⟩ ∧
        ∀ b, block ≤ b → b < visit → ∃ k < j, ∃ r, before[k]? = some r ∧
          r.pc = Wg0.Site.validFree.pc ∧
          b = block + (before.take k).countP isProbabilityPublication := by
  let seen := before.takeWhile (!isProbabilityPublication ·)
  let later := before.dropWhile (!isProbabilityPublication ·)
  have hSplit : before = seen ++ later := List.takeWhile_append_dropWhile.symm
  have hPrefix : ∀ f ∈ seen, f.pc ≠ Wg0.Site.soReady.pc := by
    intro f hf
    have h := List.all_eq_true.mp List.all_takeWhile f hf
    simpa [isProbabilityPublication, Bool.not_eq_true'] using h
  cases hLater : later with
  | nil =>
    have hEq : before = seen := by simpa only [hLater, List.append_nil] using hSplit
    have hNone : ∀ f ∈ before, f.pc ≠ Wg0.Site.soReady.pc := by rwa [hEq]
    have hCount : before.countP isProbabilityPublication = 0 := by
      apply List.countP_eq_zero.mpr
      intro f hf
      have h := hNone f hf
      simpa [isProbabilityPublication] using h
    obtain ⟨hRelease, hAcquire⟩ := softmax_return_before_publication hpre hAt hTag hNone hRun
    obtain ⟨j, hJ, hPoll⟩ := hAcquire
    exact ⟨block, by rw [hCount, Nat.add_zero], hBlock, hRelease, j, hJ, hPoll,
      fun _ h₀ h₁ => (Nat.not_lt_of_ge h₀ h₁).elim⟩
  | cons pub remaining =>
    have hHead := List.head?_dropWhile_not (!isProbabilityPublication ·) before
    have hCut : before.dropWhile (!isProbabilityPublication ·) = pub :: remaining := hLater
    rw [hCut] at hHead
    have hPub : pub.pc = Wg0.Site.soReady.pc := by simpa [isProbabilityPublication] using hHead
    rw [hLater] at hSplit
    have hTrace : before ++ e :: tail = seen ++ pub :: (remaining ++ e :: tail) := by
      rw [hSplit, List.append_assoc, List.cons_append]
    have hRun' : Run kernel Assumptions.all L g t (seen ++ pub :: (remaining ++ e :: tail)) o :=
      hTrace ▸ hRun
    have hFacts : Holds t.regs (softmaxLoopFacts block total) := hAt.2.2.2.2.2.2.2.2
    obtain ⟨u, hu, hRegs, hPublication⟩ :=
      softmax_loop_facts_at_publication (by rw [hAt.1]; decide) (by rw [hAt.1]; decide)
        hFacts hPub hPrefix hRun'
    by_cases hMore : block + 1 < total
    · have hNonempty : remaining ≠ [] := by
        intro hNil
        rw [hNil] at hPublication
        obtain ⟨next, hLocal, hAt, hRest⟩ :=
          softmax_next_head_after_publication hMore hLimit hu hRegs hPublication (by simp)
        have hBound := softmax_opening_event_bound hAt.1 (after_softmax_local_prefix hLocal hRest)
        rw [hTag] at hBound
        exact (by decide : ¬ Wg0.Site.validFree.pc ≤ 256) hBound
      obtain ⟨opening, mid, rfl⟩ := List.exists_cons_of_ne_nil hNonempty
      have hBody : ∃ v, AtVector v 264 (softmaxMaskFacts L (block + 1) total) v.sub v.acc ∧
          Run kernel Assumptions.all L g v (mid ++ e :: tail) o := by
        obtain ⟨poll, rest, hReady⟩ := List.exists_cons_of_ne_nil
          (show mid ++ e :: tail ≠ [] by simp)
        rw [List.cons_append, hReady] at hPublication
        rw [hReady]
        exact softmax_next_mask_after_publication hpre hMore hLimit hu hRegs hPublication
      obtain ⟨v, hv, hRest⟩ := hBody
      obtain ⟨visit, hVisit, hIn, hRelease, j, hj, hGet, hVisits⟩ :=
        softmax_return_in_trace hpre hMore hLimit hv hTag hRest
      have hBeforePub : seen.countP isProbabilityPublication = 0 := by
        apply List.countP_eq_zero.mpr
        intro f hf
        simpa [isProbabilityPublication] using hPrefix f hf
      have hOpening : isProbabilityPublication opening = false := by
        by_cases hO : isProbabilityPublication opening = false
        · exact hO
        exfalso
        have hTrue : isProbabilityPublication opening = true := Bool.eq_true_of_not_eq_false hO
        have hNo : opening.pc ≤ 256 := by
          obtain ⟨start, hLocal, hAt', hRun'⟩ :=
            softmax_next_head_after_publication hMore hLimit hu hRegs hPublication (by simp)
          exact softmax_opening_event_bound hAt'.1 (after_softmax_local_prefix hLocal hRun')
        have hEq : opening.pc = Wg0.Site.soReady.pc := by
          simpa [isProbabilityPublication] using hTrue
        change opening.pc = 1122 at hEq
        omega
      have hPubEq : isProbabilityPublication pub = true := by
        simp [isProbabilityPublication, hPub]
      have hCount : before.countP isProbabilityPublication =
          1 + mid.countP isProbabilityPublication := by
        simp [hSplit, List.countP_append, hBeforePub, hPubEq, hOpening, Nat.add_comm]
      let offset := seen.length + 2
      have hBeforeLen : before.length = offset + mid.length := by
        simp only [hSplit, offset, List.length_append, List.length_cons]
        omega
      have hTrace'' : before ++ e :: tail =
          (seen ++ [pub, opening]) ++ (mid ++ e :: tail) := by
        rw [hTrace]
        simp [List.append_assoc]
      refine ⟨visit, by omega, hIn, hRelease, offset + j, by omega, ?_, ?_⟩
      · rw [hTrace'', List.getElem?_append_right (by simp [offset])]
        simpa [offset] using hGet
      · intro b hLower hUpper
        have hBefore : before = (seen ++ [pub, opening]) ++ mid := by
          rw [hSplit]
          simp [List.append_assoc]
        have hLen : (seen ++ [pub, opening]).length = offset := by simp [offset]
        by_cases hEq : b = block
        · subst b
          obtain ⟨r, hr, hTag⟩ := mask_return_before_probability_publication hAt.1 hPub hRun'
          obtain ⟨k, hk, hEntry⟩ := List.mem_iff_getElem.mp hr
          refine ⟨k, by unfold offset at hBeforeLen; omega, r, ?_, hTag, ?_⟩
          · rw [hSplit, List.getElem?_append_left hk]
            exact List.getElem?_eq_some_iff.mpr ⟨hk, hEntry⟩
          · rw [hSplit, List.take_append_of_le_length (Nat.le_of_lt hk)]
            have hLe := PTX.ClusterTrace.countP_take_mono
              (p := isProbabilityPublication) (xs := seen) (Nat.le_of_lt hk)
            rw [List.take_of_length_le le_rfl, hBeforePub] at hLe
            omega
        · obtain ⟨k, hk, r, hEntry, hTag, hBlockCount⟩ := hVisits b (by omega) hUpper
          refine ⟨offset + k, by omega, r, ?_, hTag, ?_⟩
          · rw [hBefore, List.getElem?_append_right (by rw [hLen]; omega), hLen,
              Nat.add_sub_cancel_left]
            exact hEntry
          · rw [hBefore, ← hLen, List.take_length_add_append, List.countP_append]
            have hSingle : (seen ++ [pub, opening]).countP isProbabilityPublication = 1 := by
              simp [hBeforePub, hPubEq, hOpening, List.countP_append]
            omega
    · have hFinal : total = block + 1 := by omega
      subst total
      exact (no_mask_return_after_final_publication hLimit hu hRegs hPublication
        (List.mem_append_right _ (by simp)) hTag).elim
termination_by before.length
decreasing_by
  rw [hSplit, List.length_append, List.length_cons, List.length_cons]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
