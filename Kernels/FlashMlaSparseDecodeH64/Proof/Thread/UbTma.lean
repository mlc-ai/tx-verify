-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
public import Lemmas.Flow.Final
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Lemmas.Flow.Next
import Lemmas.Flow.UbStop
import Lemmas.Tensor.TensorMulticast

public section

/-! # Continuations of returned KV producer events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbTma

open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem lifted_next {d : Wg1Tma.D} {e : Event}
    (h : Wg1Tma.next P L g d e ≠ none) : Machine.next P L g (.tma d) e ≠ none := by
  cases he : Wg1Tma.next P L g d e with
  | none => exact (h he).elim
  | some u =>
    cases u with
    | some u => simp [Machine.next, he]
    | none =>
      simp only [Machine.next, he]
      split
      · simp
      · split <;> simp

private theorem nc_kind {t u : TState} {base dst pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mem
      { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, nc := true,
        addr := ⟨.reg base 64, 0⟩, dsts := [some dst] })) e (some u)) :
    ∃ a bs, e.kind = .nc a bs := by
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := base) (w := 64)
    rfl rfl rfl rfl rfl] at hf
  change Fires pc (loadTmpl Assumptions.all L g t .global true 32 [dst] base 0) e (some u)
    at hf
  unfold loadTmpl at hf
  split at hf
  · cases hf.2
  · simp only [ite_true] at hf
    split at hf
    · obtain ⟨bs, _, hk, _⟩ := hf
      exact ⟨_, bs, congrArg Event.kind hk⟩
    · cases hf.2

/-- Returned events in the actual KV producer keep a machine state: a coordinate read returns
the published word, whose bytes rebuild. -/
theorem next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) {i : Nat} {e : Event} {d : Wg1Tma.D}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hReturns : ¬ Ends e) : Machine.next P L g (.tma d) e ≠ none := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hFired⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
  obtain ⟨t, ins, o, ha, hi, hc, hf⟩ := Frame.fired_site hs hX he hd
  change kernel.code[d.site.pc]? = some ins at hc
  cases o with
  | none => exact (hReturns (fires_none_ends hf)).elim
  | some u =>
    apply lifted_next
    cases h : d.site
    case elect =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_7)
      obtain ⟨_, _, leader, hEvent, _⟩ := fires_elect hf
      rw [hEvent]
      simp only [Wg1Tma.next, h]
      split
      · split <;> simp
      · simp
    case lenOrig =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_17)
      obtain ⟨_, _, hk⟩ := nc_kind hf
      simp only [Wg1Tma.next, h, hk]
      split
      · split <;> simp
      · simp
    case lenExtra =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_18)
      obtain ⟨_, _, hk⟩ := nc_kind hf
      simp only [Wg1Tma.next, h, hk]
      split
      · split <;> simp
      · simp
    case waitQ =>
      obtain ⟨_, _, _, hk⟩ := RingEvents.tmaEntry_wait hpre (.inl h) hFired
      simp [Wg1Tma.next, h, hk]
    case waitLast =>
      obtain ⟨_, _, _, hk⟩ := RingEvents.tmaEntry_wait hpre (.inr h) hFired
      simp [Wg1Tma.next, h, hk]
    case waitCoord =>
      obtain ⟨_, hk⟩ := RingEvents.validReady_wait hpre h hFired
      simp [Wg1Tma.next, h, hk]
    case waitFree =>
      obtain ⟨_, hk⟩ := RingEvents.rawFree_wait hpre h hFired
      simp [Wg1Tma.next, h, hk]
    case coord k j =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans (Wg1Tma.coordLoad_code k j))
      obtain ⟨_, hk, _⟩ := Wg1Tma.fires_coord hpre h ha hi hf
      obtain ⟨a, bs, hk', hr⟩ := MachineTracking.actual_coordinate_value hpre hX hs he hd h
      rw [hk] at hk' ⊢
      obtain ⟨rfl, rfl⟩ := Kind.rd.inj hk'
      simp [Wg1Tma.next, h, hr]
    case issue k =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans (Wg1Tma.issueInstr_code k))
      change Fires d.site.pc (tensorTmpl L g t (Wg1Tma.issueInstr k).op) e (some u) at hf
      unfold Wg1Tma.issueInstr at hf
      rcases tensorTmpl_cpTensor_cases with ⟨_, hTemplate⟩ | ⟨_, _, _, hTemplate, _, _⟩
      · rw [hTemplate] at hf
        cases hf.2
      · rw [hTemplate] at hf
        rw [hf.1]
        simp only [Wg1Tma.next, h]
        split <;> simp
    case rawReady =>
      have hk := RingEvents.rawReady_expectTx hpre h hFired
      simp only [Wg1Tma.next, h, hk]
      split <;> simp
    case coordFree =>
      have hk := RingEvents.validFree_arrive hpre h hFired
      simp only [Wg1Tma.next, h, hk]
      split <;> simp
    case barrier =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_12)
      obtain ⟨h790, h791⟩ := Wg1Tma.barrier_regs P L g h ha
      rw [Wg1Tma.fires_bar_12 h790 h791 hpre.block] at hf
      rw [hf.1]
      simp [Wg1Tma.next, h]
    case exit =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
      cases hf.2

private theorem length_tmpl_ok {t : TState} {base dst addr : Nat}
    (hsub : t.sub = 0) (hReg : t.regs base = some (b64 addr)) (hFit : addr < 2 ^ 64)
    (hAlign : addr % 4 = 0) (hNc : Assumptions.all.any (·.ncLoads t.pc) = true) (f : Fault) :
    eventTmpl Assumptions.all L g t (.mem
      { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, nc := true,
        addr := ⟨.reg base 64, 0⟩, dsts := [some dst] }) ≠ .ub f := by
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := base) (w := 64)
    rfl rfl rfl rfl rfl]
  change loadTmpl Assumptions.all L g t .global true 32 [dst] base 0 ≠ _
  rw [loadTmpl_global_nc hsub hReg hFit (by decide) hAlign hNc]
  intro he
  cases he

/-- The actual KV producer's templates outside its gather issues are defined. -/
theorem control_tmpl_ok (hpre : Pre P L mem0) {d : Wg1Tma.D} {t : TState} {ins : Instr}
    (ha : (Machine.code P L g).AtD (.tma d) t) (hi : Wg1Tma.Inv P L g d)
    (hc : kernel.code[(Machine.code P L g).pc (.tma d)]? = some ins)
    (hissue : ∀ k, d.site ≠ .issue k)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  intro hu
  let e : Event := ⟨t.pc, .ub f⟩
  have hf : (Machine.machine P L g).Fired (some (.tma d)) e none := by
    refine ⟨t, ⟨ha, hi⟩, ?_⟩
    change Fires t.pc (match kernel.code[(Machine.code P L g).pc (.tma d)]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) e none
    rw [hc]
    change Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e none
    rw [hu]
    exact ⟨rfl, rfl⟩
  change (Wg1Tma.code P L g).AtD d t at ha
  change kernel.code[d.site.pc]? = some ins at hc
  cases h : d.site
  case lenOrig =>
    have hp : d.site.pc = 2181 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_17)
    have hsub : t.sub = 0 := by rw [ha.2.1, Wg1Tma.code_sub, h]; rfl
    have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
      rw [show t.pc = d.site.pc from ha.1, hp]
      decide +kernel
    have hReg : t.regs 3045 =
        some (b64 ((Thread.paramWord L 80 8 + 4 * Thread.ctaidY L g) % 2 ^ 64)) :=
      Wg1Tma.atD_regAt ha hp (by decide +kernel)
    exact length_tmpl_ok hsub hReg (Nat.mod_lt _ (by decide))
      (Thread.paramAddr_mod4 (Thread.paramWord_80_mod4 hpre) g) hn f hu
  case lenExtra =>
    have hp : d.site.pc = 2191 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_18)
    have hsub : t.sub = 0 := by rw [ha.2.1, Wg1Tma.code_sub, h]; rfl
    have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
      rw [show t.pc = d.site.pc from ha.1, hp]
      decide +kernel
    have hReg : t.regs 3047 =
        some (b64 ((Thread.paramWord L 144 8 + 4 * Thread.ctaidY L g) % 2 ^ 64)) :=
      Wg1Tma.atD_regAt ha hp (by decide +kernel)
    exact length_tmpl_ok hsub hReg (Nat.mod_lt _ (by decide))
      (Thread.paramAddr_mod4 (Thread.paramWord_144_mod4 hpre) g) hn f hu
  case issue k => exact hissue k h
  case elect =>
    have hp : d.site.pc = 2165 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_7)
    have hr : t.regs 663 = some (b32 4294967295) :=
      Wg1Tma.atD_regAt ha hp (by decide +kernel)
    exact elect_ok hr f hu
  case waitQ =>
    obtain ⟨_, _, _, hk⟩ := RingEvents.tmaEntry_wait hpre (.inl h) hf
    cases hk
  case waitLast =>
    obtain ⟨_, _, _, hk⟩ := RingEvents.tmaEntry_wait hpre (.inr h) hf
    cases hk
  case waitCoord =>
    obtain ⟨_, hk⟩ := RingEvents.validReady_wait hpre h hf
    cases hk
  case waitFree =>
    obtain ⟨_, hk⟩ := RingEvents.rawFree_wait hpre h hf
    cases hk
  case coord k j =>
    have hCode := hc
    rw [h] at hCode
    obtain rfl := Option.some.inj (hCode.symm.trans (Wg1Tma.coordLoad_code k j))
    have hFires : Fires d.site.pc (eventTmpl Assumptions.all L g t (.mem (Wg1Tma.coordLoad k)))
        e none := by
      have hp : t.pc = d.site.pc := ha.1
      rw [hu, ← hp]
      exact ⟨rfl, rfl⟩
    obtain ⟨_, _, hnext⟩ := Wg1Tma.fires_coord hpre h ha hi hFires
    cases hnext
  case rawReady => cases RingEvents.rawReady_expectTx hpre h hf
  case coordFree => cases RingEvents.validFree_arrive hpre h hf
  case barrier =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_12)
    obtain ⟨h790, h791⟩ := Wg1Tma.barrier_regs P L g h ha
    rw [Wg1Tma.fires_bar_12 h790 h791 hpre.block] at hu
    cases hu
  case exit =>
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    cases hu

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbTma
