-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
import Kernels.InklingRelDecode.Flow.Code.Part040
import Kernels.InklingRelDecode.Flow.Code.Part044
import Lemmas.Flow.TmplOkMore
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.NoUbSites
import Lemmas.Flow.UbStop
import Lemmas.Flow.TmplOkSync
import Lemmas.Flow.UbFree
import Lemmas.Flow.StoreSharedSym
import Kernels.InklingRelDecode.Flow.Code.Part040

@[expose] public section

/-! # The epilogue's poll, shuffle, barriers and deallocation are not undefined behaviour

What the launch gives (`EpiLaunch`, from `Pre`): whole warps, and the shared window with the
`o_final` barrier and the role word inside it. A state of the epilogue holds the facts of its
control table (`AtD`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow Control

set_option maxRecDepth 100000

/-- The launch facts the epilogue's events need. -/
structure EpiLaunch (L : Launch) : Prop where
  block : L.block % 32 = 0
  align : L.sharedBase % 1024 = 0
  room : L.sharedBase + 213344 ≤ 2 ^ 32

variable {e : Entry} {L : Launch} {g : Nat} {d : D} {t : TState} {ins : Instr}

/-- A register of the facts of the site holds the table's word. -/
theorem reg_epi (h : (code e L g).AtD d t) {r : Nat} (hr : r ∈ ctlLive d.site.pc) :
    t.regs r = some (valueOf e L g d.received r) := by
  obtain ⟨-, -, -, -, hF⟩ := h
  exact holds_mem hF (mem_factsFrom hr)

/-- **The poll of `o_final` is not undefined behaviour.** -/
theorem safe_wait (hl : EpiLaunch L) (hat : (code e L g).AtD d t) (hs : d.site = .wait)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r624 := reg_epi hat (r := 624) (hs ▸ (by decide : 624 ∈ ctlLive Site.wait.pc))
  have r1760 := reg_epi hat (r := 1760) (hs ▸ (by decide : 1760 ∈ ctlLive Site.wait.pc))
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2565)
  have hv : valueOf e L g d.received 624 = b32 ((L.sharedBase + Iface.oFinal) % 2 ^ 32) := rfl
  rw [hv] at r624
  have h1 : L.sharedBase + Iface.oFinal < 2 ^ 32 := by
    have := hl.room
    unfold Iface.oFinal
    omega
  have h2 : (L.sharedBase + Iface.oFinal) % 8 = 0 := by
    have := hl.align
    unfold Iface.oFinal
    omega
  rw [Nat.mod_eq_of_lt h1] at r624
  have hm := mbarLoc_b32_ok (L := L) (g := g) r624 h1 h2
  have hz : valueOf e L g d.received 1760 = b32 0 := rfl
  rw [hz] at r1760
  exact wait_loc_ok hm (readBits_regBits (w := 32) (L := L) (g := g) r1760
    (show (b32 0).regBits = some (BitVec.ofNat 64 0) from rfl)) f

/-- **The lane shuffle is not undefined behaviour.** -/
theorem safe_shfl (hl : EpiLaunch L) (hat : (code e L g).AtD d t) (hs : d.site = .shfl)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r464 := reg_epi hat (r := 464) (hs ▸ (by decide : 464 ∈ ctlLive Site.shfl.pc))
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2603)
  have hv : valueOf e L g d.received 464 = b32 (g % L.block / 32) := rfl
  rw [hv] at r464
  exact shfl_imm_ok (p := none) (Or.inr rfl) hl.block r464 f

/-- **The barriers, the register request and the load wait are not undefined behaviour.** -/
theorem safe_plain (hl : EpiLaunch L) (hs : d.site = .join ∨ d.site = .setMax ∨ d.site = .sync1 ∨
    d.site = .sync0 ∨ d.site = .waitLd) (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  rcases hs with hs | hs | hs | hs | hs <;> rw [hs] at hc
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2846)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2847)
    exact plainOk_tmpl hl.block (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2849)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2850)
    exact barSync_imm_ok (id := 0) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2608)
    exact plainOk_tmpl hl.block (by decide) f

/-- **The deallocation is not undefined behaviour** (the allocation word is a word of integer
bits). -/
theorem safe_dealloc (hl : EpiLaunch L) (hb : e.base.regBits.isSome) (hat : (code e L g).AtD d t)
    (hs : d.site = .dealloc) (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r463 := reg_epi hat (r := 463) (hs ▸ (by decide : 463 ∈ ctlLive Site.dealloc.pc))
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2851)
  have hv : valueOf e L g d.received 463 = e.base := rfl
  rw [hv] at r463
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hb
  exact tcDealloc_imm_ok hl.block r463 hx f

/-- The wrapped address of the role word's slot of the shared window is 4-aligned. -/
theorem role_aligned (hl : EpiLaunch L) :
    wrapAddr 32 (BitVec.ofNat 64 (L.sharedBase + 0)) (213336 : Int) % (32 / 8 * 1) = 0 := by
  have h1 := hl.align
  have h2 := hl.room
  simp only [wrapAddr, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-- **The role word store is not undefined behaviour.** -/
theorem safe_roleWord (hl : EpiLaunch L) (hat : (code e L g).AtD d t) (hs : d.site = .roleWord)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hsub : t.sub = 0 := hat.2.1
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2848)
  exact stSharedSym_ok (o := 0) (w := .cta) (os := .imm 50529027) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (by simpa [DType.width] using role_aligned hl) (by simp [hsub])
    ⟨.bits 32 (truncBits 32 (BitVec.ofInt 64 50529027)), rfl, rfl⟩ f

/-- **The accumulator load is not undefined behaviour** when the received word names the warp's
lane group. -/
theorem safe_load (hl : EpiLaunch L) (hb : e.base = b32 0) (hat : (code e L g).AtD d t)
    (hs : d.site = .load) (hx : ∃ x, d.received = b32 x ∧ x % 4 = g % L.block / 32 % 4)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain ⟨x, hr, hq⟩ := hx
  have r1827 := reg_epi hat (r := 1827) (hs ▸ (by decide : 1827 ∈ ctlLive Site.load.pc))
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2607)
  have h0 : (Lib.word (b32 x)).toNat % 4 = g % L.block / 32 % 4 := by
    simp only [Lib.word, b32, Value.regBits, truncBits, Option.getD_some, BitVec.toNat_ofNat]
    omega
  set q := g % L.block / 32 % 4 with hqd
  have hq4 : q < 4 := Nat.mod_lt _ (by norm_num)
  have hv : valueOf e L g d.received 1827 = b32 (256 + q * 2 ^ 21) := by
    have e1 : Lib.addBase (b32 0) 256 = b32 256 := by simpa using Lib.addBase_bits 0 256
    have e2 : ∀ k, Lib.addBase (b32 256) k = b32 ((256 + k) % 2 ^ 32) := fun k => by
      simpa using Lib.addBase_bits 256 k
    have : valueOf e L g d.received 1827 =
        Lib.addBase (Lib.addBase e.base 256) ((Lib.word d.received).toNat % 4 * 2 ^ 21) := rfl
    rw [this, hb, e1, e2, hr, h0]
    congr 1
    omega
  rw [hv] at r1827
  have hlt : 256 + q * 2 ^ 21 < 2 ^ 32 := by omega
  have hbits : t.regs 1827 = some (.bits 32 (BitVec.ofNat 64 (256 + q * 2 ^ 21))) := r1827
  refine tcLd_word_ok hl.block (by decide) hbits ?_ ?_ f
  · simp only [BitVec.toNat_ofNat]
    omega
  · simp only [BitVec.toNat_ofNat, tcDataAddressOk, TcShape.splitOk, tmemLaneFieldOk, laneBase,
      TcShape.lanes]
    rw [Nat.mod_eq_of_lt (show 256 + q * 2 ^ 21 < 2 ^ 64 by omega)]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ← hqd]
    have hA : (256 + q * 2 ^ 21) % 2 ^ 16 = 256 := by omega
    have hB : (256 + q * 2 ^ 21) / 2 ^ 16 = q * 32 := by omega
    rw [hA, hB]
    refine ⟨by norm_num, by norm_num, Or.inr ⟨by omega, by omega⟩⟩

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
