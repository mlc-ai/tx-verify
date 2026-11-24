-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
public import Lemmas.Flow.Final
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events

public section

/-! # Continuations of returned dequantization events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbDequant

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem lifted_next {d : Wg2.D} {e : Event}
    (h : Wg2.next P L g d e ≠ none) : Machine.next P L g (.wg2 d) e ≠ none := by
  cases he : Wg2.next P L g d e with
  | none => exact (h he).elim
  | some u =>
    cases u with
    | some u => simp [Machine.next, he]
    | none =>
      simp only [Machine.next, he]
      split <;> simp

/-- An actual returned event of the dequantizer does not kill the represented thread. -/
theorem next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) {i : Nat} {e : Event} {d : Wg2.D}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hReturns : ¬ Ends e) : Machine.next P L g (.wg2 d) e ≠ none := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
  have hf' : ∃ u, (Wg2.machine P L g).Fired (some (.inr d)) e (some u) := by
    cases o with
    | some u => exact ⟨u, hf⟩
    | none =>
      obtain ⟨_, _, hd'⟩ := hf
      exact (hReturns (fires_none_ends hd')).elim
  obtain ⟨u, hf'⟩ := hf'
  apply lifted_next
  cases h : d.site
  case lenOrig =>
    obtain ⟨_, hk, _⟩ := Wg2.fired_length_event (orig := true) h hf'
    simp only [Wg2.next, h, Wg2.nextSite, hk]
    split
    · split <;> simp
    · simp
  case lenExtra =>
    obtain ⟨_, hk, _⟩ := Wg2.fired_length_event (orig := false) h hf'
    simp only [Wg2.next, h, Wg2.nextSite, hk]
    split
    · split <;> simp
    · simp
  case qUtccp =>
    obtain ⟨_, _, _, _, hk⟩ := RingEvents.dequant_wait_object hpre (.inl h) hf
    simp [Wg2.next, h, Wg2.nextSite, hk]
  case rawReady =>
    obtain ⟨_, hk⟩ := RingEvents.rawReady_wait hpre h hf
    simp [Wg2.next, h, Wg2.nextSite, hk]
  case svDone =>
    obtain ⟨_, _, _, _, hk⟩ := RingEvents.dequant_wait_object hpre (.inr h) hf
    simp [Wg2.next, h, Wg2.nextSite, hk]
  case scale r j =>
    obtain ⟨_, _, hk, ha, hb⟩ := Wg2.fired_scale_event hpre h hf'
    simp only [Wg2.next, h, Wg2.nextSite, hk, ha, hb, true_and, ↓reduceIte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  case raw r s =>
    obtain ⟨_, _, hk, ha, hb⟩ := Wg2.fired_raw_event hpre h hf'
    simp only [Wg2.next, h, Wg2.nextSite, hk, ha, hb, Wg2.rawBytesPerThread, true_and, ↓reduceIte]
    split <;> simp
  case store r s =>
    obtain ⟨_, hk, ha, hb⟩ := Wg2.fired_store_event hpre h hf'
    simp [Wg2.next, h, Wg2.nextSite, hk, ha, hb]
  case fence =>
    obtain ⟨t, ins, o, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    have hp : d.site.pc = 3595 := by rw [h]; rfl
    change kernel.code[d.site.pc]? = some ins at hc
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_3595)
    rw [Wg2.event_fence (L := L) (g := g) (t := t)] at hf
    have hk := congrArg Event.kind hf.1
    simp [Wg2.next, h, Wg2.nextSite, hk]
  case ready =>
    have hk := RingEvents.dequantReady_arrive hpre h hf
    simp [Wg2.next, h, Wg2.nextSite, hk]
  case free =>
    have hk := RingEvents.rawFree_arrive hpre h hf
    simp [Wg2.next, h, Wg2.nextSite, hk]
  case barrier =>
    obtain ⟨t, ins, o, ha, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    have hp : d.site.pc = 3610 := by rw [h]; rfl
    change kernel.code[d.site.pc]? = some ins at hc
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_15)
    rw [Wg2.event_barrier hpre ha hp] at hf
    have hk := congrArg Event.kind hf.1
    simp [Wg2.next, h, Wg2.nextSite, hk]

/-- The waits, publications and final control events have defined templates. -/
theorem control_tmpl_ok (hpre : Pre P L mem0) {d : Wg2.D} {t : TState} {ins : Instr}
    (ha : (Machine.code P L g).AtD (.wg2 d) t) (hi : Wg2.Inv P L g d)
    (hc : kernel.code[(Machine.code P L g).pc (.wg2 d)]? = some ins)
    (hs : d.site = .qUtccp ∨ d.site = .rawReady ∨ d.site = .svDone ∨
      d.site = .fence ∨ d.site = .ready ∨ d.site = .free ∨ d.site = .barrier)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  intro hu
  let e : Event := ⟨t.pc, .ub f⟩
  have hf : (Machine.machine P L g).Fired (some (.wg2 d)) e none := by
    refine ⟨t, ⟨ha, hi⟩, ?_⟩
    change Fires t.pc (match kernel.code[(Machine.code P L g).pc (.wg2 d)]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) e none
    rw [hc]
    change Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e none
    rw [hu]
    exact ⟨rfl, rfl⟩
  change kernel.code[d.site.pc]? = some ins at hc
  rcases hs with h | h | h | h | h | h | h
  · obtain ⟨_, _, _, _, hk⟩ := RingEvents.dequant_wait_object hpre (.inl h) hf
    cases hk
  · obtain ⟨_, hk⟩ := RingEvents.rawReady_wait hpre h hf
    cases hk
  · obtain ⟨_, _, _, _, hk⟩ := RingEvents.dequant_wait_object hpre (.inr h) hf
    cases hk
  · have hp : d.site.pc = 3595 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_3595)
    rw [Wg2.event_fence (L := L) (g := g) (t := t)] at hu
    cases hu
  · cases RingEvents.dequantReady_arrive hpre h hf
  · cases RingEvents.rawFree_arrive hpre h hf
  · have hp : d.site.pc = 3610 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_15)
    rw [Wg2.event_barrier hpre ha hp] at hu
    cases hu

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbDequant
