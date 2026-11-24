-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantUseCounts
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ActualSuffix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

@[expose] public section

/-! # The actual dequantizer's first raw acquire starts its ring sequence -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow Protocol.RawRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem first_raw_followed {i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hWg : wgOf L g = 2)
    (he : X.get (g, i) = some e)
    (hSilent : ∀ f ∈ (X.tr g).take i, rawSignal L g f = none) :
    Frame.stateAt (Machine.code P L) X g i ≠ some none := by
  intro hDismissed
  obtain ⟨j, hj, role, f, hf, hState, hNext⟩ :=
    prior_dismissal (PTX.len_of_get he).le hDismissed
  have hg := Frame.lt_of_get hX he
  have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
  cases dismissal_is_consumer hpre hX hs hf hState hNext with
  | wg0 d =>
    change wgOf L g = 0 at hRole
    omega
  | wg2 d =>
    obtain ⟨k, hk, first, hScale, hBlock, hFirst⟩ :=
      dequant_first_scale_of_dismissal hpre hX hs hf hState hNext
    have hZero : ((X.tr g).take k).filterMap (rawSignal L g) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro r hr
      exact hSilent r (List.take_subset_take_left _ (hk.trans hj.le) hr)
    let slot : Fin 2 := 0
    have hCount := (Wg2RawTrace.composed_raw_access_counts hpre
      ((hs g hg).machine.produces (hX.thr g hg)) hFirst (.inl ⟨0, 0, hScale⟩)).2
    rw [hBlock] at hCount
    have hPoll := raw_signal_ready_count L g slot ((X.tr g).take k)
    rw [hZero] at hPoll
    change 0 = okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff (0 % 2)⟩
      ((X.tr g).take k) at hPoll
    omega

private theorem first_raw_state {i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hWg : wgOf L g = 2)
    (he : X.get (g, i) = some e) (hSignal : rawSignal L g e ≠ none)
    (hSilent : ((X.tr g).take i).filterMap (rawSignal L g) = []) :
    ∃ d : Wg2.D, d.block = 0 ∧ d.site = .rawReady ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)) := by
  have hg := Frame.lt_of_get hX he
  have hFollow := first_raw_followed hpre hX hs hWg he (List.filterMap_eq_nil_iff.mp hSilent)
  have hTrace := (hs g hg).machine.produces (hX.thr g hg)
  rcases raw_signal_has_slot hSignal with ⟨slot, p, hMark⟩ | ⟨slot, hMark⟩
  · obtain ⟨acq, scope, hk⟩ := raw_signal_acquire_iff.mp hMark
    obtain ⟨_, _, _, d, _, hSite, _, hState⟩ :=
      await_ready_source_at_followed hpre hX (hs g hg).machine hFollow he hk
    have hCount := Wg2RawTrace.composed_release_count hpre (0 : Fin 2) hTrace hState
    simp only [Wg2RawTrace.released, hSite, Fin.val_zero] at hCount
    have hZero := raw_signal_free_count L g (0 : Fin 2) ((X.tr g).take i)
    rw [hSilent] at hZero
    refine ⟨d, ?_, hSite, hState⟩
    change 0 = _ at hZero
    have hn : 0 = (d.block + (1 - 0)) / 2 := hZero.trans hCount
    omega
  · obtain ⟨tx, count, rel, scope, hk⟩ := raw_signal_release_iff.mp hMark
    obtain ⟨_, _, _, _, _, d, hSlot, hSite, hState⟩ :=
      release_source_at_followed hpre hX (hs g hg).machine hFollow he hk
    have hCount := (Wg2RawTrace.composed_raw_free_counts hpre hTrace hState hSite).2
    rw [hSlot] at hCount
    have hZero := raw_signal_ready_count L g slot ((X.tr g).take i)
    rw [hSilent] at hZero
    change 0 = _ at hZero
    omega

set_option maxRecDepth 100000 in
private theorem raw_poll_anchor {t : TState} {d : Wg2.D}
    (hGood : (Wg2.code P L g).Good (some d) t)
    (hBlock : d.block = 0) (hSite : d.site = .rawReady) :
    AtVector t 2677 (dequantPollFacts L g 0) t.sub t.acc := by
  obtain ⟨hAt, hInv⟩ := hGood
  have hPc : d.site.pc = 2677 := by rw [hSite]; rfl
  have hBuf : d.buf = 0 := hInv.bufBlock.trans (by rw [hBlock])
  have hPar : d.par = 0 := hInv.parBlock.trans (by rw [hBlock])
  refine ⟨hAt.1.trans hPc, rfl, rfl, hAt.2.2.2.1, ?_⟩
  have reg (r : Nat) (hr : r ∈ (Flow.live 2677).filter (fun r => Wg2.tracked.contains r)) :
      t.regs r = some (Wg2.valueOf P L g d r) := Wg2.AtD.regAt hAt hPc hr
  simp only [dequantPollFacts, dequantHeadFacts, dequantParityWord, Nat.zero_mod,
    Nat.zero_div, List.cons_append, List.nil_append]
  have hFacts := And.intro (reg 2458 (by decide +kernel))
    (And.intro (reg 2459 (by decide +kernel))
    (And.intro (reg 351 (by decide +kernel))
    (And.intro (reg 2789 (by decide +kernel))
    (And.intro (reg 2788 (by decide +kernel))
    (And.intro (reg 513 (by decide +kernel))
    (And.intro (reg 457 (by decide +kernel))
    (And.intro (reg 2988 (by decide +kernel)) True.intro)))))))
  simpa [Wg2.valueOf, Wg2.table, lookupLit, hBuf, hPar, sb] using hFacts

/-- Every actual dequantizer's trace has counted raw turns starting at block zero. -/
theorem actual_dequant_raw_turns
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hWg : wgOf L g = 2) :
    RawTurns 0 false ((X.tr g).filterMap (rawSignal L g)) := by
  let prior := (X.tr g).takeWhile (fun f => (rawSignal L g f).isNone)
  let rest := (X.tr g).dropWhile (fun f => (rawSignal L g f).isNone)
  have hTrace : X.tr g = prior ++ rest := List.takeWhile_append_dropWhile.symm
  have hSilent : prior.filterMap (rawSignal L g) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro f hf
    exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp List.all_takeWhile f hf)
  cases hRest : rest with
  | nil => rw [hTrace, hRest, List.append_nil, hSilent]; exact .nil _ _
  | cons e tail =>
    have hSignal : rawSignal L g e ≠ none := by
      have h := List.head?_dropWhile_not (fun f => (rawSignal L g f).isNone) (X.tr g)
      change (X.tr g).dropWhile (fun f => (rawSignal L g f).isNone) = _ at hRest
      apply Option.ne_none_iff_isSome.mpr
      simpa [hRest] using h
    rw [hRest] at hTrace
    have he : X.get (g, prior.length) = some e := by
      change (X.tr g)[prior.length]? = _
      simp [hTrace]
    have hTake : (X.tr g).take prior.length = prior := by simp [hTrace]
    obtain ⟨d, hBlock, hSite, hState⟩ :=
      first_raw_state hpre hX hs hWg he hSignal (hTake.symm ▸ hSilent)
    have hDrop : (X.tr g).drop prior.length = e :: tail := by simp [hTrace]
    have hg := Frame.lt_of_get hX he
    obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hState
      (by rw [hDrop]; simp)
    have hRole : (Wg2.code P L g).Good (some d) t := hGood
    have hAt := raw_poll_anchor hRole hBlock hSite
    have hEvents (f : Event) (hf : f ∈ (X.tr g).drop prior.length) :
        ∃ i, X.get (g, i) = some f := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf
      rw [List.getElem?_drop] at hi
      exact ⟨_, hi⟩
    have hTurns := dequant_turns_of_poll hpre hX hAt hRun hEvents
    rw [hDrop] at hTurns
    simpa only [hTrace, List.filterMap_append, hSilent, List.nil_append] using hTurns

private theorem raw_split_trace {i : Nat} {e : Event} (he : X.get (g, i) = some e) :
    X.tr g = (X.tr g).take i ++ e :: (X.tr g).drop (i + 1) := by
  have hDrop := List.drop_eq_getElem_cons (PTX.len_of_get he)
  rw [(List.getElem?_eq_some_iff.mp he).2] at hDrop
  rw [← hDrop]
  exact (List.take_append_drop ..).symm

/-- A dequantizer's successful raw-ready polls alternate by actual use of that buffer. -/
theorem actual_raw_ready_parity {i p : Nat} {slot : Fin 2} {e : Event}
    {acq : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hWg : wgOf L g = 2)
    (he : X.get (g, i) = some e)
    (hk : e.kind = .wait (ready L (ctaOf L g) slot) p true acq scope) :
    p % 2 = okPolls (ready L (ctaOf L g) slot) ((X.tr g).take i) % 2 := by
  have hTurns := actual_dequant_raw_turns hpre hX hs hWg
  have hMark := raw_signal_acquire_iff.mpr ⟨acq, scope, hk⟩
  rw [raw_split_trace he, List.filterMap_append, List.filterMap_cons, hMark] at hTurns
  have h := raw_turn_acquire_parity (slot := slot) hTurns
  rw [raw_signal_ready_count] at h
  exact h

/-- A dequantizer releases a raw slot only after its successful acquire of that use. -/
theorem actual_raw_release_counts {i tx count : Nat} {slot : Fin 2} {e : Event}
    {rel : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hWg : wgOf L g = 2)
    (he : X.get (g, i) = some e)
    (hk : e.kind = .arrive (free L (ctaOf L g) slot) tx count rel scope) :
    okPolls (ready L (ctaOf L g) slot) ((X.tr g).take i) =
      arrivals (free L (ctaOf L g) slot) ((X.tr g).take i) + 1 := by
  have hTurns := actual_dequant_raw_turns hpre hX hs hWg
  have hMark := raw_signal_release_iff.mpr ⟨tx, count, rel, scope, hk⟩
  rw [raw_split_trace he, List.filterMap_append, List.filterMap_cons, hMark] at hTurns
  have h := raw_turn_release_count (slot := slot) hTurns
  rw [raw_signal_ready_count, raw_signal_free_count] at h
  exact h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
