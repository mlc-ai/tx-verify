-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Flow.TcTmpl

public section

/-! # Defined softmax loop waits, fences and arrivals -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0

open PTX PTX.Proof PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- Softmax bulk, Tensor Memory and proxy control events with fixed operands. -/
@[expose] def LoopPlain : Wg0.Site → Prop
  | .bulkWait | .fenceLoad | .scoreWait | .fenceBefore | .rescaleFence
  | .rescaleWait _ | .rescaleWaitSt _ | .rescaleFenceB | .soFence => True
  | _ => False

/-- Mbarrier operations in the softmax loop. -/
@[expose] def LoopMbar : Wg0.Site → Prop
  | .lastStore | .maskReady | .qkDone | .validFree | .soReady => True
  | _ => False

private theorem rescaleWait_code (j : Fin 4) :
    kernel.code[(Site.rescaleWait j).pc]? = some ⟨none, .tcWaitLd⟩ := by
  fin_cases j <;> kernel_rfl

private theorem rescaleWaitSt_code (j : Fin 4) :
    kernel.code[(Site.rescaleWaitSt j).pc]? = some ⟨none, .tcWaitSt⟩ := by
  fin_cases j <;> kernel_rfl

private theorem waitLd_template (hpre : Pre P L mem0) (t : TState) :
    eventTmpl Assumptions.all L g t .tcWaitLd = .tc .waitLd (PTX.next t) :=
  tc_waitLd (g := g) (by rw [hpre.block])

private theorem waitSt_template (hpre : Pre P L mem0) (t : TState) :
    eventTmpl Assumptions.all L g t .tcWaitSt = .tc .waitSt (PTX.next t) := by
  simp [eventTmpl, tcTmpl, hpre.block, ofExec, pure, Except.pure]

private def PlainKind (s : Wg0.Site) (kind : Kind) : Prop :=
  match s with
  | .bulkWait => kind = .bulkWait .read 0
  | .fenceLoad | .rescaleFence => kind = .tc .fenceAfter
  | .fenceBefore | .rescaleFenceB => kind = .tc .fenceBefore
  | .scoreWait | .rescaleWait _ => kind = .tc .waitLd
  | .rescaleWaitSt _ => kind = .tc .waitSt
  | .soFence => kind = .fenceProxy (.async (some (.shared .cta))) none
  | _ => False

private theorem plain_fires (hpre : Pre P L mem0) {t : TState} {ins : Instr}
    {pc : Nat} {e : Event} {o : Option TState} {s : Wg0.Site}
    (hc : kernel.code[s.pc]? = some ins) (hs : LoopPlain s)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    PlainKind s e.kind := by
  cases s <;> simp only [LoopPlain] at hs
  case bulkWait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_198)
    exact congrArg Event.kind hf.1
  case fenceLoad =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_275)
    exact congrArg Event.kind hf.1
  case scoreWait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_286)
    rw [waitLd_template (g := g) hpre t] at hf
    exact congrArg Event.kind hf.1
  case fenceBefore =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_287)
    exact congrArg Event.kind hf.1
  case rescaleFence =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_711)
    exact congrArg Event.kind hf.1
  case rescaleWait j =>
    obtain rfl := Option.some.inj (hc.symm.trans (rescaleWait_code j))
    rw [waitLd_template (g := g) hpre t] at hf
    exact congrArg Event.kind hf.1
  case rescaleWaitSt j =>
    obtain rfl := Option.some.inj (hc.symm.trans (rescaleWaitSt_code j))
    rw [waitSt_template (g := g) hpre t] at hf
    exact congrArg Event.kind hf.1
  case rescaleFenceB =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1119)
    exact congrArg Event.kind hf.1
  case soFence =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1120)
    exact congrArg Event.kind hf.1

private theorem mbar_fires (hpre : Pre P L mem0) {d : D} {e : Event} {o : Option TState}
    (hMbar : LoopMbar d.site)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o) :
    match d.site with
    | .lastStore | .validFree | .soReady => ∃ a n k r s, e.kind = .arrive a n k r s
    | .maskReady | .qkDone => ∃ a n k r s, e.kind = .wait a n k r s
    | _ => False := by
  cases h : d.site <;> simp only [h, LoopMbar] at hMbar
  case lastStore => exact ⟨_, _, _, _, _, RingEvents.lastStore_arrive hpre h hf⟩
  case validFree => exact ⟨_, _, _, _, _, RingEvents.maskFree_arrive hpre h hf⟩
  case soReady => exact ⟨_, _, _, _, _, RingEvents.scores_arrive hpre h hf⟩
  case maskReady =>
    obtain ⟨_, hk⟩ := RingEvents.maskReady_wait hpre h hf
    exact ⟨_, _, _, _, _, hk⟩
  case qkDone =>
    obtain ⟨_, _, hk⟩ := RingEvents.gemmDone_wait_exact hpre (.inl h) hf
    exact ⟨_, _, _, _, _, hk⟩

set_option maxRecDepth 100000 in
/-- All softmax loop waits, fences and Mbarrier arrivals have defined templates. -/
theorem loop_control_tmpl_ok (hpre : Pre P L mem0)
    {d : D} {t : TState} {ins : Instr} (ha : (Wg0.code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hLoop : LoopPlain d.site ∨ LoopMbar d.site) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  intro hu
  let e : Event := ⟨t.pc, .ub f⟩
  have hf : Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e none := by
    rw [hu]
    exact ⟨rfl, rfl⟩
  rcases hLoop with hPlain | hMbar
  · have hk := plain_fires hpre hc hPlain hf
    cases h : d.site <;> simp only [h, LoopPlain] at hPlain <;>
      simp only [h, PlainKind] at hk <;> cases hk
  · have hm : (Machine.machine P L g).Fired (some (.wg0 d)) e none := by
      refine ⟨t, ⟨ha, hi⟩, ?_⟩
      change Fires t.pc (match kernel.code[d.site.pc]? with
        | some ins => eventTmpl Assumptions.all L g t ins.op
        | none => .ub .pcOutOfRange) e none
      rwa [hc]
    have hk := mbar_fires hpre hMbar hm
    cases h : d.site <;> simp only [h, LoopMbar] at hMbar <;>
      rw [h] at hk <;> obtain ⟨_, _, _, _, _, hk⟩ := hk <;> cases hk

set_option maxRecDepth 100000 in
/-- Actual softmax loop control events preserve the machine's represented successor. -/
theorem loop_control_next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {i : Nat} {e : Event} {d : D} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hLoop : LoopPlain d.site ∨ LoopMbar d.site) : Machine.next P L g (.wg0 d) e ≠ none := by
  rcases hLoop with hPlain | hMbar
  · obtain ⟨_, _, _, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    change kernel.code[d.site.pc]? = some _ at hc
    have hk := plain_fires hpre hc hPlain hf
    cases h : d.site <;> simp only [h, LoopPlain] at hPlain <;>
      simp only [h, PlainKind] at hk <;> simp [Machine.next, Wg0.next, nextSite, h, hk]
    all_goals
      split
      · simp
      · simp
      · contradiction
  · have hg := Frame.lt_of_get hX he
    obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
    have hk := mbar_fires hpre hMbar hf
    cases h : d.site <;> simp only [h, LoopMbar] at hMbar <;>
      rw [h] at hk <;> obtain ⟨_, _, _, _, _, hk⟩ := hk <;>
      simp [Machine.next, Wg0.next, nextSite, h, hk, waitStep]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0
