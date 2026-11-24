-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Inputs

public section

/-! # Live softmax input events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0

open PTX PTX.Proof PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def inputAccess (ty : DType) (base dst : Nat) : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := ty, nc := true,
    addr := ⟨.reg base 64, 0⟩, dsts := [some dst] }

private theorem nc_template {t : TState} {base dst addr : Nat} {ty : DType}
    (hWidth : ty.width = 32) (hRule : (inputAccess ty base dst).rule = some .threadAccess)
    (hSub : t.sub = 0) (hReg : t.regs base = some (b64 addr)) (hFit : addr < 2 ^ 64)
    (hAlign : addr % 4 = 0) (hNc : Assumptions.all.any (·.ncLoads t.pc) = true) :
    eventTmpl Assumptions.all L g t (.mem (inputAccess ty base dst)) =
      .readNC { loc := ⟨.global, 0, addr⟩, size := 4 } (afterLoad t [dst]) := by
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := base) (w := 64)
    hRule rfl rfl rfl rfl]
  change loadTmpl Assumptions.all L g t .global true ty.width [dst] base 0 = _
  rw [hWidth]
  exact loadTmpl_global_nc hSub hReg hFit (by decide) hAlign hNc

private theorem sink_aligned (hpre : Pre P L mem0) :
    (Thread.paramWord L 88 8 + 4 * Wg0.head L g) % 2 ^ 64 % 4 = 0 := by
  have hp : Thread.paramWord L 88 8 % 4 = 0 := by
    cases hs : P.sinkBase with
    | none =>
      change Wg0.paramWord L 88 8 % 4 = 0
      rw [paramWord_88_zero hpre hs, Nat.zero_mod]
    | some x =>
      have hb := hpre.paramSink
      rw [hs] at hb
      exact Thread.paramWord_mod4_of (fun k hk => by simpa using hb.1 k hk) hb.2.1
  rw [Nat.mod_mod_of_dvd _ (show 4 ∣ 2 ^ 64 by decide)]
  omega

/-- The optional input site reads exactly one aligned 32-bit non-coherent word. -/
theorem input_template (hpre : Pre P L mem0)
    {d : D} {t : TState} {ins : Instr} (ha : (Wg0.code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hInput : d.site = .sink ∨ d.site = .lenOrig ∨ d.site = .lenExtra) :
    ∃ a k, eventTmpl Assumptions.all L g t ins.op = .readNC a k := by
  have hSub : t.sub = 0 := by
    have hb : d.site.elems = 1 := by
      rcases hInput with h | h | h <;> rw [h] <;> rfl
    have hl := hi.subLt
    rw [hb] at hl
    have hsub : t.sub = d.sub := ha.2.1
    omega
  rcases hInput with h | h | h
  · have hp : d.site.pc = 156 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_156)
    have hReg : t.regs 3138 =
        some (b64 ((Thread.paramWord L 88 8 + 4 * Wg0.head L g) % 2 ^ 64)) :=
      reg_value ha (by rw [h]; decide +kernel)
    have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
      have hpc : t.pc = d.site.pc := ha.1
      rw [hpc, hp]
      decide +kernel
    exact ⟨_, _, nc_template rfl rfl hSub hReg (Nat.mod_lt _ (by decide)) (sink_aligned hpre) hn⟩
  · have hp : d.site.pc = 168 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_168)
    have hReg : t.regs 3140 =
        some (b64 ((Thread.paramWord L 80 8 + 4 * Wg0.eOf L g) % 2 ^ 64)) :=
      reg_value ha (by rw [h]; decide +kernel)
    have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
      have hpc : t.pc = d.site.pc := ha.1
      rw [hpc, hp]
      decide +kernel
    exact ⟨_, _, nc_template rfl rfl hSub hReg (Nat.mod_lt _ (by decide))
      (Thread.paramAddr_mod4 (Thread.paramWord_80_mod4 hpre) g) hn⟩
  · have hp : d.site.pc = 181 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_181)
    have hReg : t.regs 3142 =
        some (b64 ((Thread.paramWord L 144 8 + 4 * Wg0.eOf L g) % 2 ^ 64)) :=
      reg_value ha (by rw [h]; decide +kernel)
    have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
      have hpc : t.pc = d.site.pc := ha.1
      rw [hpc, hp]
      decide +kernel
    exact ⟨_, _, nc_template rfl rfl hSub hReg (Nat.mod_lt _ (by decide))
      (Thread.paramAddr_mod4 (Thread.paramWord_144_mod4 hpre) g) hn⟩

/-- The sink and length templates name aligned non-coherent input reads. -/
theorem input_tmpl_ok (hpre : Pre P L mem0)
    {d : D} {t : TState} {ins : Instr} (ha : (Wg0.code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hInput : d.site = .sink ∨ d.site = .lenOrig ∨ d.site = .lenExtra) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain ⟨_, _, hk⟩ := input_template hpre ha hi hc hInput
  rw [hk]
  intro he
  cases he

/-- Actual softmax input events keep a represented control state. -/
theorem input_next_live (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) {i : Nat} {e : Event} {d : D}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hInput : d.site = .sink ∨ d.site = .lenOrig ∨ d.site = .lenExtra) :
    Machine.next P L g (.wg0 d) e ≠ none := by
  obtain ⟨_, _, _, ha, hi, hc, hf⟩ := Frame.fired_site hs hX he hd
  obtain ⟨_, _, hk⟩ := input_template hpre ha hi hc hInput
  rw [hk] at hf
  obtain ⟨bs, _, hEvent, _⟩ := hf
  have hKind := congrArg Event.kind hEvent
  rcases hInput with h | h | h
  · by_cases hR : ∃ v, rebuild 3 bs = .ok v
    · obtain ⟨v, hr⟩ := hR
      cases hS : P.sink (Wg0.head L g) with
      | none => simp [Machine.next, Wg0.next, nextSite, h, hKind, hr, hS]
      | some value =>
        by_cases hm : (valFloat .f32 v).toOption = some value <;>
          simp [Machine.next, Wg0.next, nextSite, h, hKind, hr, hS, hm]
    · cases hr : rebuild 3 bs with
      | error _ => simp [Machine.next, Wg0.next, nextSite, h, hKind, hr]
      | ok v => exact (hR ⟨v, hr⟩).elim
  · cases hr : rebuild 3 bs with
    | error _ => simp [Machine.next, Wg0.next, nextSite, h, hKind, hr]
    | ok v =>
      by_cases hv : v = b32 (P.topkLen (Wg0.eOf L g)) <;>
        simp [Machine.next, Wg0.next, nextSite, h, hKind, hr, hv]
  · cases hr : rebuild 3 bs with
    | error _ => simp [Machine.next, Wg0.next, nextSite, h, hKind, hr]
    | ok v =>
      by_cases hv : v = b32 (P.extraTopkLen (Wg0.eOf L g)) ∧
          d.origLenRead = P.topkLenBase.isSome <;>
        simp [Machine.next, Wg0.next, nextSite, h, hKind, hr, hv]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0
