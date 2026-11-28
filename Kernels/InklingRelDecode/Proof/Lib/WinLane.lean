-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.WinSet
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Lemmas.Kernel.PostEvent
public import Lemmas.Execution.EventFrameSource
public import Lemmas.Execution.TraceProjection
public import Lemmas.Flow.RegionFrame

@[expose] public section

/-! # A state of a lane inside a window comes from an event at its edge

A state between two events at a position of a window `S` (`winOk S R`, a scan of the code) is
reached by local steps from the state after the last event of the lane, which is an event of
`entryEvents S`; the registers `R` are those of that state. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

theorem win_start {S R} (hf : fwdOk S R = true) (hb : enterOk S 0 = true) (h0 : inS S 0 = false)
    {u v : TState} (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v)
    (hv : inS S v.pc = true) : inS S u.pc = true ∧ ∀ r ∈ R, v.regs r = u.regs r := by
  have hu : inS S u.pc = true := by
    by_contra hn
    obtain ⟨w, -, -, e, hw⟩ := first_entry hb h (by simpa using hn) hv
    rw [e, h0] at hw
    cases hw
  exact ⟨hu, (win_keep hf h hu).2⟩

/-- **An event keeps the registers its instruction does not write.** -/
theorem estep_keeps {s t0 : TState} {e : Event}
    (hes : EStep kernel Assumptions.all L g s e (some t0)) :
    ∀ ins, kernel.code[s.pc]? = some ins → ∀ r, r ∉ EventFrame.eventWrites ins.op →
      t0.regs r = s.regs r := by
  intro ins hc r hr
  obtain ⟨ins', hc', hnl, hf⟩ := EventFrame.estep_event_source hes
  have e : ins' = ins := Option.some.inj (hc'.symm.trans hc)
  subst e
  have he : Assumptions.emuSites.contains s.pc = false := by
    cases h : Assumptions.emuSites.contains s.pc
    · rfl
    · have := List.all_eq_true.mp emu_local s.pc (by simpa using h)
      simp [hc] at this
      simp [this] at hnl
  have hloc : ∀ op u, execLocalA Assumptions.all L g s op = .ok u → LocalFrame op s u :=
    fun op u hx => execLocalA_frame rulesFrame hx (segFree he)
  exact EventFrame.callbackFrame_fires (eventTmpl_kept_at (op := ins'.op) hloc) hf r hr

/-- **The last event before a state in the window**: its position is at the window's edge, the
state after it is in the window, and the window keeps the registers `R`. -/
theorem lane_set_gen {S : List (Nat × Nat)} {R : List Nat}
    (hst : ∀ {u v : TState}, Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v →
      inS S v.pc = true → inS S u.pc = true ∧ ∀ r ∈ R, v.regs r = u.regs r)
    (h0 : inS S 0 = false) {X : Execution}
    {t : TState} (hl : Iface.LaneState L X g t) (ht : inS S t.pc = true) :
    ∃ k e t0, (X.tr g)[k]? = some e ∧ Run kernel Assumptions.all L g {} ((X.tr g).take (k + 1))
      (some t0) ∧ (∃ s, EStep kernel Assumptions.all L g s e (some t0)) ∧
      e.pc ∈ entryEvents S ∧ inS S t0.pc = true ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t ∧
      ∀ r ∈ R, t.regs r = t0.regs r := by
  obtain ⟨k, t0, hr, hrt⟩ := hl
  obtain ⟨k0, hk0, hr0⟩ : ∃ k0 ≤ (X.tr g).length,
      Run kernel Assumptions.all L g {} ((X.tr g).take k0) (some t0) := by
    by_cases h : k ≤ (X.tr g).length
    · exact ⟨k, h, hr⟩
    · refine ⟨_, le_rfl, ?_⟩
      rw [List.take_length]
      rwa [List.take_of_length_le (by omega)] at hr
  obtain ⟨hin, hkeep⟩ := hst hrt ht
  cases k0 with
  | zero =>
    rw [List.take_zero] at hr0
    cases hr0
    exact absurd hin (by simp [h0])
  | succ k' =>
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k']? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hr1 := hr0
    rw [List.take_add_one, he, Option.toList_some] at hr0
    obtain ⟨u, s, -, -, hes⟩ := Run.unsnoc _ e hr0
    obtain ⟨ins, hc, hnl, -⟩ := EventFrame.estep_event_source hes
    have hp := post_pc hes
    have hpe := EventFrame.estep_source_pc hes
    refine ⟨k', e, t0, he, hr1, ⟨s, hes⟩, ?_, hin, hrt, hkeep⟩
    rw [hpe]
    have hdis : inS S s.pc = true ∨ inS S (s.pc + 1) = true := by
      have : t0.pc = s.pc ∨ t0.pc = s.pc + 1 := by omega
      rcases this with h | h <;> rw [h] at hin
      · exact .inl hin
      · exact .inr hin
    simpa [entryEvents] using mem_eventsOf (S := S) (n := 0) (k := s.pc) hc (by simpa using hnl)
      (by simpa using hdis)

/-- **The last event before a state in the window** (the scan `winOk`). -/
theorem lane_set {S R} (hf : fwdOk S R = true) (hb : enterOk S 0 = true)
    (h0 : inS S 0 = false) {X : Execution}
    {t : TState} (hl : Iface.LaneState L X g t) (ht : inS S t.pc = true) :
    ∃ k e t0, (X.tr g)[k]? = some e ∧ Run kernel Assumptions.all L g {} ((X.tr g).take (k + 1))
      (some t0) ∧ (∃ s, EStep kernel Assumptions.all L g s e (some t0)) ∧
      e.pc ∈ entryEvents S ∧ inS S t0.pc = true ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t ∧
      ∀ r ∈ R, t.regs r = t0.regs r :=
  lane_set_gen (fun h hv => win_start hf hb h0 h hv) h0 hl ht

end PTX.Kernels.InklingRelDecode.Proof.Lib
