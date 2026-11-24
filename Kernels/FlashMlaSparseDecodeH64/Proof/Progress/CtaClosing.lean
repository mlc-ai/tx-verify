-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.DeallocReturn
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.CtaClosingTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Clc.ClcExecution
import Lemmas.Protocol.NamedBarLedger

public section

/-! # Once the closing barrier has all its arrivals, the CTA returns -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem pending_of_no_exit (hX : Consistent L kernel Assumptions.all mem0 X)
    {g : Nat} (hg : g < L.threads) (hex : ¬ ∃ i tag, X.get (g, i) = some ⟨tag, .exit⟩) :
    Frame.Pending L X g := by
  refine ⟨hg, ?_, ?_⟩
  · rintro ⟨_, _, hcan⟩
    obtain ⟨i, sp, targets, _, hi, _⟩ := hX.clc.canceled_has_issue hcan
    exact GlobalWrites.no_clc (i := i) (s := sp) (tg := targets) hX hi
  · intro tag hlast
    exact hex ⟨(X.tr g).length - 1, tag, by
      change (X.tr g)[(X.tr g).length - 1]? = _
      rwa [← List.getLast?_eq_getElem?]⟩

private theorem no_ub {Y : Execution} (hsafe : ¬ Unsafe L kernel Assumptions.all mem0 Y) :
    ¬ HasUb Y := fun h => hsafe (.inl h)

private theorem cta_div {cta lane : Nat} (hl : lane < L.block) :
    (cta * L.block + lane) / L.block = cta := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hl), Nat.div_eq_of_lt hl,
    Nat.zero_add]

private theorem warp_of_cta_lane (hpre : Pre P L mem0) {cta lane : Nat} (hl : lane < L.block) :
    warpOf L (cta * L.block + lane) = lane / 32 := by
  unfold warpOf
  rw [hpre.block] at hl
  rw [tidOf_eq hpre, hpre.block]
  exact congrArg (· / 32) (by
    rw [Nat.add_comm, Nat.mul_comm cta 384, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl])

/-- All arrived lanes in a maximal safe prefix eventually have the actual closing deallocation
and return recorded. The theorem keeps maximality's observation history in the proof, and its
conclusion concerns the original thread traces. -/
theorem cta_exited_of_arrived (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hsafe : ∀ Y, Consistent L kernel Assumptions.all mem0 Y →
      ¬ Unsafe L kernel Assumptions.all mem0 Y)
    {cta : Nat} (hcta : cta < L.grid)
    (hArrived : ∀ lane < L.block, ∃ i tag,
      X.get (cta * L.block + lane, i) = some ⟨tag, .bar 12 none .sync⟩) :
    ∀ lane < L.block, ∃ i tag, X.get (cta * L.block + lane, i) = some ⟨tag, .exit⟩ := by
  have hNext (lane : Nat) (hl : lane < L.block) {i tag : Nat}
      (he : X.get (cta * L.block + lane, i) = some ⟨tag, .bar 12 none .sync⟩) :
      i + 1 < (X.tr (cta * L.block + lane)).length := by
    let g := cta * L.block + lane
    have hg := PTX.NamedBar.cta_thread_lt hcta hl
    have hlt : i < (X.tr g).length := PTX.len_of_get he
    by_contra hn
    change ¬ (i + 1 < (X.tr g).length) at hn
    have hi : i + 1 = (X.tr g).length := by omega
    have hLast : X.IsBarrier (g, (X.tr g).length - 1) 12 none tag := by
      have hIdx : i = (X.tr g).length - 1 := by omega
      rw [← hIdx]
      exact he
    have hNoFault (Y) (hY : Consistent L kernel Assumptions.all mem0 Y) :
        ¬ CtaBarFault L Y := fun hf => hsafe Y hY (by simp [Unsafe, hf])
    obtain ⟨Y, hMaxY, hTrace, hrel⟩ := closing_released hpre hmax hs ht hNoFault hLast (by
      intro l hL
      rw [cta_div hl]
      obtain ⟨j, t, hj⟩ := hArrived l hL
      exact ⟨j, t, hj⟩)
    have hGet : Y.get = X.get := by funext e; simp only [Execution.get, hTrace]
    have hState (d : Machine.ThreadD)
        (hd : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some d)) :
        Frame.stateAt (Machine.code P L) Y g (Y.tr g).length = some (some d) := by
      simpa [Frame.stateAt, hTrace, ← hi] using hd
    have htY : Frame.Tracked (Machine.code P L) Y := by
      intro h j hh
      simpa [Frame.stateAt, hTrace] using ht h j hh
    have hpY : Frame.Pending L Y g := by
      apply pending_of_no_exit hMaxY.1 hg
      rintro ⟨j, t, hj⟩
      have hlen := Execution.exit_last hMaxY.1 hg hj
      have hj' : j = i := by rw [hTrace, ← hi] at hlen; omega
      subst j
      rw [hGet, he] at hj
      cases hj
    rcases CtaClosingTrace.after_arrival hpre hmax.1 hs ht he with
      ⟨d, hd, hr, _⟩ | ⟨d, hd, hdSite, _⟩
    · exact return_not_pending_of_output hpre hMaxY hs htY (hsafe _ hMaxY.1)
        (no_ub (hsafe _ hMaxY.1)) hpY hrel (hState d hd) hr
    · exact dealloc_not_pending hpre hMaxY hs (no_ub (hsafe _ hMaxY.1)) hpY hrel
        (hState (.wg0 d) hd) hdSite
  have hIssued (lane : Fin 32) : ∃ i tag, X.get (cta * L.block + lane.val, i) =
      some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩ := by
    have hlt : lane.val < L.block := by have := lane.isLt; rw [hpre.block]; omega
    obtain ⟨i, tag, he⟩ := hArrived lane.val hlt
    have hNext := hNext lane.val hlt he
    have hw := warp_of_cta_lane hpre (cta := cta) hlt
    rw [Nat.div_eq_of_lt lane.isLt] at hw
    obtain ⟨e, hGet⟩ : ∃ e, X.get (cta * L.block + lane.val, i + 1) = some e :=
      ⟨_, List.getElem?_eq_getElem hNext⟩
    rcases CtaClosingTrace.after_arrival hpre hmax.1 hs ht he with
      ⟨_, _, _, hBad⟩ | ⟨d, hd, hSite, _⟩
    · exact (hBad hw).elim
    · obtain ⟨t, hD⟩ := (CtaClosingTrace.dealloc_at hpre hmax.1 hs hGet hd hSite).1
      exact ⟨i + 1, t, hD⟩
  intro lane hl
  let g := cta * L.block + lane
  obtain ⟨i, tag, he⟩ := hArrived lane hl
  have hLen : i + 1 < (X.tr g).length := hNext lane hl he
  obtain ⟨e, hGet⟩ : ∃ e, X.get (g, i + 1) = some e := ⟨_, List.getElem?_eq_getElem hLen⟩
  rcases CtaClosingTrace.after_arrival hpre hmax.1 hs ht he with
    ⟨d, hd, hReturn, _⟩ | ⟨d, hd, hSite, hw0⟩
  · obtain ⟨t, hReturnEvent⟩ := CtaClosingTrace.return_at hmax.1 hs hGet hd hReturn
    exact ⟨i + 1, t, hReturnEvent⟩
  obtain ⟨⟨t, hDealloc⟩, hDone⟩ := CtaClosingTrace.dealloc_at hpre hmax.1 hs hGet hd hSite
  by_cases hret : i + 2 < (X.tr g).length
  · have hNext : ∃ e, X.get (g, i + 2) = some e := ⟨_, List.getElem?_eq_getElem hret⟩
    obtain ⟨e, hNext⟩ := hNext
    obtain ⟨label, hExit⟩ := CtaClosingTrace.return_at hmax.1 hs hNext hDone trivial
    exact ⟨i + 2, label, hExit⟩
  by_contra hNoExit
  have hg := PTX.NamedBar.cta_thread_lt hcta hl
  have hp := pending_of_no_exit hmax.1 hg hNoExit
  have hEq : i + 2 = (X.tr g).length := by omega
  have hl32 : lane < 32 := by
    rw [warp_of_cta_lane hpre hl] at hw0
    omega
  have hc := dealloc_covered_of_issued hpre hmax hs ht hcta hIssued
    (lane := ⟨lane, hl32⟩) hDealloc
  have hi : i + 1 = (X.tr g).length - 1 := by omega
  have hrel := released_of_dealloc hmax.1 (hi ▸ hDealloc) (hi ▸ hc)
  exact return_not_pending_of_output hpre hmax hs ht (hsafe _ hmax.1)
    (no_ub (hsafe _ hmax.1)) hp hrel (d := .done) (hEq ▸ hDone) trivial

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
