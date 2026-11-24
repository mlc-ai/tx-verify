-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbDequant
public import Lemmas.Flow.UbStop
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events

public section

/-! # Valid event templates for the dequantizer's data accesses -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbDequant

open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The optional length load has its non-coherent read template. -/
theorem length_template (hpre : Pre P L mem0) {d : Wg2.D}
    {orig : Bool} {t : TState} (hd : d.site = Wg2.runtimeLenSite orig) (ha : Wg2.AtD P L g d t) :
    eventTmpl Assumptions.all L g t (.mem (Wg2.runtimeLenLoad orig)) =
      .readNC { loc := ⟨.global, 0, Wg2.runtimeLenAddr L g orig⟩, size := 4 }
        (afterLoad t [Wg2.runtimeLenDest orig]) := by
  have hb : t.regs (Wg2.runtimeLenBase orig) = some (b64 (Wg2.runtimeLenAddr L g orig)) := by
    have hmem : Wg2.runtimeLenBase orig ∈ (Flow.live d.site.pc).filter Wg2.tracked.contains := by
      rw [hd]
      cases orig <;> decide +kernel
    have hr := ha.reg hmem
    cases orig <;> simpa [Wg2.runtimeLenAddr, Wg2.runtimeLenBase, Wg2.valueOf, Wg2.table,
      PTX.Flow.lookupLit] using hr
  have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
    rw [ha.1, hd]
    cases orig <;> decide +kernel
  have hs : t.sub = 0 := by rw [ha.2.1, hd]; cases orig <;> rfl
  have hfit : Wg2.runtimeLenAddr L g orig < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hal : Wg2.runtimeLenAddr L g orig % 4 = 0 := by
    cases orig
    · exact Thread.paramAddr_mod4 (Thread.paramWord_144_mod4 hpre) g
    · exact Thread.paramAddr_mod4 (Thread.paramWord_80_mod4 hpre) g
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := Wg2.runtimeLenBase orig)
    (w := 64) rfl rfl rfl rfl rfl]
  change loadTmpl Assumptions.all L g t .global true 32 [Wg2.runtimeLenDest orig]
    (Wg2.runtimeLenBase orig) 0 = _
  exact loadTmpl_global_nc hs hb hfit (by decide) hal hn

/-- Every represented dequantizer event has a defined PTX template. -/
theorem tmpl_ok (hpre : Pre P L mem0) {d : Wg2.D} {t : TState} {ins : Instr}
    (ha : (Machine.code P L g).AtD (.wg2 d) t) (hi : Wg2.Inv P L g d)
    (hc : kernel.code[(Machine.code P L g).pc (.wg2 d)]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hcode : kernel.code[d.site.pc]? = some ins := hc
  cases hd : d.site
  case lenOrig =>
    rw [hd] at hcode
    obtain rfl := Option.some.inj (hcode.symm.trans (Wg2.runtimeLenLoad_code true))
    rw [length_template hpre (orig := true) hd ha]
    intro he
    cases he
  case lenExtra =>
    rw [hd] at hcode
    obtain rfl := Option.some.inj (hcode.symm.trans (Wg2.runtimeLenLoad_code false))
    rw [length_template hpre (orig := false) hd ha]
    intro he
    cases he
  case scale r j =>
    rw [hd] at hcode
    obtain rfl := Option.some.inj (hcode.symm.trans (Wg2.scaleLoad_code r j))
    rw [Wg2.scale_template hpre hd ha hi]
    intro he
    cases he
  case raw r s =>
    rw [hd] at hcode
    obtain rfl := Option.some.inj (hcode.symm.trans (Wg2.rawLoad_code r s))
    rw [Wg2.raw_template hpre hd ha hi]
    intro he
    cases he
  case store r s =>
    rw [hd] at hcode
    obtain rfl := Option.some.inj (hcode.symm.trans (Wg2.tileStore_code r s))
    rw [Wg2.tileStore_payload_template hpre hd ha hi]
    intro he
    cases he
  all_goals exact control_tmpl_ok hpre ha hi hc (by simp [hd]) f

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbDequant
