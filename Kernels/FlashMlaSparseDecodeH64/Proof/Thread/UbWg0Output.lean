-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Flow.TcTmpl

public section

/-! # Live softmax events from the final PV wait through output release -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0

open PTX PTX.Proof PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The output path after computing LSE, including the CTA's release controls. -/
@[expose] def OutputSite : Wg0.Site → Prop
  | .svDone | .fenceEpilogue | .oLoad _ | .oWait _ | .oStage _ _ | .stageFence _
  | .epiBar _ | .elect _ | .tmaStore _ | .commit | .everyone | .exit => True
  | _ => False

/-- All final output sites have defined event templates. -/
theorem output_tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads)
    {d : D} {t : TState} {ins : Instr} (ha : (Wg0.code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) (hOutput : OutputSite d.site) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hq : qOf L g < P.s_q := Wg1Mma.queryOf_lt hpre hg
  have he : eOf L g < P.b := Wg1Mma.eOf_lt_b hpre
  have ub_fires (h : eventTmpl Assumptions.all L g t ins.op = .ub f) :
      (Machine.machine P L g).Fired (some (.wg0 d)) ⟨t.pc, .ub f⟩ none := by
    refine ⟨t, ⟨ha, hi⟩, ?_⟩
    change Fires t.pc (match kernel.code[d.site.pc]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) ⟨t.pc, .ub f⟩ none
    rw [hc]
    change Fires t.pc (eventTmpl Assumptions.all L g t ins.op) ⟨t.pc, .ub f⟩ none
    rw [h]
    exact ⟨rfl, rfl⟩
  cases h : d.site <;> simp only [h, OutputSite] at hOutput
  case svDone =>
    intro hu
    obtain ⟨_, _, hk⟩ := RingEvents.gemmDone_wait_exact hpre (.inr h) (ub_fires hu)
    cases hk
  case fenceEpilogue =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1187)
    exact plainOk_tmpl hb rfl f
  case oLoad j =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (outputLoad_code j))
    rw [event_oLoad hpre ha h]
    intro hk
    cases hk
  case oWait j =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (outputWait_code j))
    exact plainOk_tmpl hb rfl f
  case oStage j k =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (stage_code j k))
    rw [event_oStage hpre hg ha hi h]
    intro hk
    cases hk
  case stageFence j =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (stageFence_code j))
    exact plainOk_tmpl hb rfl f
  case epiBar j =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (epiBar_code j))
    rw [event_epiBar hpre ha h]
    intro hk
    cases hk
  case elect j =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (election_code j))
    have hv := reg_value ha (r := electionMask j) (by rw [h]; fin_cases j <;> decide +kernel)
    have hr : t.regs (electionMask j) = some (b32 4294967295) := by
      fin_cases j <;> exact hv
    exact elect_ok hr f
  case tmaStore j =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (outputTma_code j))
    intro hu
    have hf : Fires t.pc (eventTmpl Assumptions.all L g t (outputTmaOp j))
        ⟨t.pc, .ub f⟩ none := by
      rw [hu]
      exact ⟨rfl, rfl⟩
    cases fires_tmaOutput hpre ha h hi.warpLt hq he hf
  case commit =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1832)
    exact plainOk_tmpl hb rfl f
  case everyone =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1835)
    rw [event_everyone hpre ha h]
    intro hk
    cases hk
  case exit =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
    rw [event_exit hpre ha h]
    intro hk
    cases hk

private theorem lifted_next {d : D} {e : Event}
    (h : Wg0.next P L g d e ≠ none) : Machine.next P L g (.wg0 d) e ≠ none := by
  cases he : Wg0.next P L g d e with
  | none => exact (h he).elim
  | some u =>
    cases u with
    | some u => simp [Machine.next, he]
    | none =>
      simp only [Machine.next, he]
      split <;> simp

/-- Every actual returned event on the output path preserves the thread representation. -/
theorem output_next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) {i : Nat} {e : Event} {d : D}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hOutput : OutputSite d.site) (hReturns : ¬ Ends e) :
    Machine.next P L g (.wg0 d) e ≠ none := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hFired⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
  have hReturning : ∃ u, (Wg0.code P L g).toMachine.Fired (some d) e (some u) := by
    cases o with
    | none =>
      obtain ⟨_, _, hf⟩ := hFired
      exact (hReturns (fires_none_ends hf)).elim
    | some u => exact ⟨u, hFired⟩
  obtain ⟨u, hFire⟩ := hReturning
  apply lifted_next
  cases h : d.site <;> simp only [h, OutputSite] at hOutput
  case svDone =>
    obtain ⟨_, _, hk⟩ := RingEvents.gemmDone_wait_exact hpre (.inr h) hFired
    simp [Wg0.next, nextSite, h, hk, waitStep]
  case fenceEpilogue =>
    obtain ⟨_, ins, _, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    change kernel.code[d.site.pc]? = some ins at hc
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1187)
    have hk : e.kind = .tc .fenceAfter := congrArg Event.kind hf.1
    simp [Wg0.next, nextSite, h, hk]
  case oLoad j =>
    obtain ⟨words, _, hk⟩ := fired_outputLoad hpre h hFire
    simp [Wg0.next, nextSite, h, hk]
  case oWait j =>
    obtain ⟨t, ins, _, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    change kernel.code[d.site.pc]? = some ins at hc
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (outputWait_code j))
    have hm : eventTmpl Assumptions.all L g t .tcWaitLd = .tc .waitLd (PTX.next t) :=
      tc_waitLd (L := L) (g := g) (t := t) (by rw [hpre.block])
    rw [hm] at hf
    have hk : e.kind = .tc .waitLd := congrArg Event.kind hf.1
    simp only [Wg0.next, nextSite, h, hk]
    split <;> simp
  case oStage j k =>
    obtain ⟨_, hk, _, _⟩ := fired_stageOutput hpre hg h hFire
    by_cases hk' : k.val + 1 < 8 <;> simp only [Wg0.next, nextSite, h, hk', ↓reduceDIte,
      writeStep, hk] <;> split_ifs <;> simp
  case stageFence j =>
    simp [Wg0.next, nextSite, h, fired_stageFence h hFire]
  case epiBar j =>
    simp [Wg0.next, nextSite, h, fired_outputBarrier hpre h hFire]
  case elect j =>
    obtain ⟨_, leader, hk⟩ := fired_outputElection h hFire
    by_cases hl : leader = laneOf L g <;> simp [Wg0.next, nextSite, h, hk, hl]
  case tmaStore j =>
    have hq : qOf L g < P.s_q := Wg1Mma.queryOf_lt hpre hg
    have he' : eOf L g < P.b := Wg1Mma.eOf_lt_b hpre
    simp [Wg0.next, nextSite, h, fired_outputTile hpre h hq he' hFire]
  case commit => simp [Wg0.next, nextSite, h, fired_outputCommit h hFire]
  case everyone =>
    simp only [Wg0.next, nextSite, h, fired_outputEveryone hpre h hFire]
    split <;> simp
  case exit =>
    obtain ⟨_, ins, _, ha, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    change kernel.code[d.site.pc]? = some ins at hc
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
    rw [event_exit hpre ha h] at hf
    simp [Wg0.next, nextSite, h, congrArg Event.kind hf.1]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0
