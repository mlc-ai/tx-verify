-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
public import Lemmas.Flow.Final
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexShuffle
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents

public section

/-! # Continuations of returned index-warp events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbIndex

open PTX PTX.Proof PTX.Flow Wg1Index

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem lifted_next {d : D} {e : Event}
    (h : Wg1Index.next P L g d e ≠ none) : Machine.next P L g (.index d) e ≠ none := by
  cases he : Wg1Index.next P L g d e with
  | none => exact (h he).elim
  | some u =>
    cases u with
    | some u => simp [Machine.next, he]
    | none =>
      simp only [Machine.next, he]
      split <;> simp

/-- The frozen pair sites use their selected index-vector operands. -/
theorem pair_code (extra first high : Bool) :
    kernel.code[(Site.pair extra first high).pc]? = some
      ⟨none, .mem (ncPair (pairOperands extra first).1
        (pairOperands extra first).2.1 (pairOperands extra first).2.2)⟩ := by
  cases extra <;> cases first
  · exact Flow.code_2429
  · exact Flow.code_2403
  · exact Flow.code_2517
  · exact Flow.code_2501

/-- Each frozen pair site uses the read-only non-coherent rule. -/
theorem pair_nc (extra first high : Bool) :
    Assumptions.all.any (·.ncLoads (Site.pair extra first high).pc) = true := by
  cases extra <;> cases first
  · exact asms_ncLoads_2429
  · exact asms_ncLoads_2403
  · exact asms_ncLoads_2517
  · exact asms_ncLoads_2501

private theorem barrier_template (hpre : Pre P L mem0) {d : D} {t : TState}
    (hp : d.site.pc = 2585) (ha : AtD P L g d t) :
    eventTmpl Assumptions.all L g t (.barSyncN (.reg 659) (.reg 660) false) =
      .bar 12 (PTX.next t) none .sync := by
  have h659 : t.regs 659 = some (b32 12) := ha.reg (by rw [hp]; decide +kernel)
  have h660 : t.regs 660 = some (b32 384) := ha.reg (by rw [hp]; decide +kernel)
  have h12 : readBits L g t 32 (.reg 659) = .ok (BitVec.ofNat 64 12) :=
    readBits_b32 h659 (by decide)
  have h384 : readBits L g t 32 (.reg 660) = .ok (BitVec.ofNat 64 384) :=
    readBits_b32 h660 (by decide)
  simp only [eventTmpl, barTmpl, h12, h384, BitVec.toNat_ofNat,
    show (12 : Nat) < 2 ^ 64 by omega, show (384 : Nat) < 2 ^ 64 by omega, Nat.mod_eq_of_lt,
    show ¬ (16 ≤ 12) by omega, ↓reduceIte, show (384 : Nat) % 32 = 0 by decide, hpre.block,
    show (BarMode.sync = BarMode.arrive) = False by decide, false_implies, true_and, or_true,
    reduceCtorEq]

/-- Returned index-warp events stay in the represented control stream. -/
theorem next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) {i : Nat} {e : Event} {d : D}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hReturns : ¬ Ends e) : Machine.next P L g (.index d) e ≠ none := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hFired⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
  obtain ⟨t, ins, o, ha, hi, hc, hf⟩ := Frame.fired_site hs hX he hd
  change kernel.code[d.site.pc]? = some ins at hc
  change AtD P L g d t at ha
  have htpc : t.pc = d.site.pc := ha.1
  cases o with
  | none => exact (hReturns (fires_none_ends hf)).elim
  | some u =>
    change Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e (some u) at hf
    apply lifted_next
    cases h : d.site
    case lenOrig =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2360)
      rw [← htpc] at hf
      have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
        rw [htpc, h]
        exact asms_ncLoads_2360
      obtain ⟨_, _, hk, _⟩ := fires_nc_load (a := ncLenOrig) rfl rfl rfl rfl rfl rfl hn hf
      rw [hk]
      simp only [Wg1Index.next, nextSite, h]
      split
      · split <;> simp
      · simp
    case lenExtra =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2365)
      rw [← htpc] at hf
      have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
        rw [htpc, h]
        exact asms_ncLoads_2365
      obtain ⟨_, _, hk, _⟩ := fires_nc_load (a := ncLenExtra) rfl rfl rfl rfl rfl rfl hn hf
      rw [hk]
      simp only [Wg1Index.next, nextSite, h]
      split
      · split <;> simp
      · simp
    case pair extra first high =>
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans (pair_code extra first high))
      rw [← htpc] at hf
      have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
        rw [htpc, h]
        exact pair_nc extra first high
      obtain ⟨_, _, hk, _⟩ := fires_nc_load (a := ncPair (pairOperands extra first).1
        (pairOperands extra first).2.1 (pairOperands extra first).2.2)
        rfl rfl rfl rfl rfl rfl hn hf
      rw [hk]
      simp only [Wg1Index.next, nextSite, h]
      split
      · split_ifs <;> simp
      · simp
    case waitFree extra =>
      obtain ⟨_, hk⟩ := RingEvents.validFree_wait hpre h hFired
      simp [Wg1Index.next, nextSite, h, hk]
    case quad1 extra =>
      obtain ⟨_, _, hk⟩ := quad1_fired_shape hpre h hFired
      rw [hk]
      simp only [Wg1Index.next, nextSite, h]
      split <;> simp
    case quad2 extra =>
      obtain ⟨_, _, hk⟩ := quad2_fired_shape hpre h hFired
      rw [hk]
      simp only [Wg1Index.next, nextSite, h]
      split <;> simp
    case coord extra high =>
      cases extra
      · obtain ⟨_, hk, hl, hz, _⟩ := fires_coord_main hpre h hi ha hc hf
        simp [Wg1Index.next, nextSite, h, hk, hl, hz]
      · obtain ⟨_, hk, hl, hz, _⟩ := fires_coord_extra hpre h hi ha hc hf
        simp [Wg1Index.next, nextSite, h, hk, hl, hz]
    case valid extra =>
      cases extra
      · obtain ⟨_, hk, hl, hz, _⟩ := fires_valid_main hpre h hi ha hc hf
        simp [Wg1Index.next, nextSite, h, hk, hl, hz]
      · obtain ⟨_, hk, hl, hz, _⟩ := fires_valid_extra hpre h hi ha hc hf
        simp [Wg1Index.next, nextSite, h, hk, hl, hz]
    case ready extra =>
      have hk := RingEvents.validReady_arrive hpre h hFired
      simp [Wg1Index.next, nextSite, h, hk]
    case barrier =>
      have hp : d.site.pc = 2585 := by rw [h]; rfl
      rw [hp] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_13)
      rw [barrier_template hpre hp ha] at hf
      rw [hf.1]
      simp [Wg1Index.next, nextSite, h]

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

/-- The index role's lengths, butterflies, synchronization and publication have defined
templates. -/
theorem control_tmpl_ok (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr}
    (ha : (Machine.code P L g).AtD (.index d) t) (hi : Inv P L g d)
    (hc : kernel.code[(Machine.code P L g).pc (.index d)]? = some ins)
    (hpair : ∀ extra first high, d.site ≠ .pair extra first high)
    (hcoord : ∀ extra high, d.site ≠ .coord extra high)
    (hvalid : ∀ extra, d.site ≠ .valid extra)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  intro hu
  let e : Event := ⟨t.pc, .ub f⟩
  have hf : (Machine.machine P L g).Fired (some (.index d)) e none := by
    refine ⟨t, ⟨ha, hi⟩, ?_⟩
    change Fires t.pc (match kernel.code[(Machine.code P L g).pc (.index d)]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) e none
    rw [hc]
    change Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e none
    rw [hu]
    exact ⟨rfl, rfl⟩
  change AtD P L g d t at ha
  change kernel.code[d.site.pc]? = some ins at hc
  cases h : d.site
  case pair extra first high => exact hpair extra first high h
  case coord extra high => exact hcoord extra high h
  case valid extra => exact hvalid extra h
  case lenOrig =>
    have hp : d.site.pc = 2360 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2360)
    have hsub : t.sub = 0 := by rw [ha.2.1, h]; rfl
    have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
      rw [ha.1, hp]
      exact asms_ncLoads_2360
    have hReg : t.regs 3023 =
        some (b64 ((Thread.paramWord L 80 8 + 4 * Thread.ctaidY L g) % 2 ^ 64)) :=
      ha.reg (by rw [hp]; decide +kernel)
    exact length_tmpl_ok hsub hReg (Nat.mod_lt _ (by decide))
      (Thread.paramAddr_mod4 (Thread.paramWord_80_mod4 hpre) g) hn f hu
  case lenExtra =>
    have hp : d.site.pc = 2365 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2365)
    have hsub : t.sub = 0 := by rw [ha.2.1, h]; rfl
    have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
      rw [ha.1, hp]
      exact asms_ncLoads_2365
    have hReg : t.regs 3025 =
        some (b64 ((Thread.paramWord L 144 8 + 4 * Thread.ctaidY L g) % 2 ^ 64)) :=
      ha.reg (by rw [hp]; decide +kernel)
    exact length_tmpl_ok hsub hReg (Nat.mod_lt _ (by decide))
      (Thread.paramAddr_mod4 (Thread.paramWord_144_mod4 hpre) g) hn f hu
  case waitFree extra =>
    obtain ⟨_, hk⟩ := RingEvents.validFree_wait hpre h hf
    cases hk
  case quad1 extra =>
    obtain ⟨_, _, hk⟩ := quad1_fired_shape hpre h hf
    have hk' := congrArg Event.kind hk
    change Kind.ub f = _ at hk'
    cases hk'
  case quad2 extra =>
    obtain ⟨_, _, hk⟩ := quad2_fired_shape hpre h hf
    have hk' := congrArg Event.kind hk
    change Kind.ub f = _ at hk'
    cases hk'
  case ready extra => cases RingEvents.validReady_arrive hpre h hf
  case barrier =>
    have hp : d.site.pc = 2585 := by rw [h]; rfl
    rw [hp] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_13)
    rw [barrier_template hpre hp ha] at hu
    cases hu

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbIndex
