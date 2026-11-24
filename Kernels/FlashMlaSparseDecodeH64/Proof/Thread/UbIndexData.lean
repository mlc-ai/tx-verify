-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbIndex
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexTracking
import Lemmas.Flow.Async
import Lemmas.Flow.PollFacts

public section

/-! # Defined templates for the index warp's vector read and shared writes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbIndex

open PTX PTX.Proof PTX.Flow Wg1Index

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem pair_tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads)
    {d : D} {t : TState} {extra first high : Bool} (hd : d.site = .pair extra first high)
    (ha : AtD P L g d t) (hi : Inv P L g d) (f : Fault) :
    eventTmpl Assumptions.all L g t (.mem (ncPair (pairOperands extra first).1
      (pairOperands extra first).2.1 (pairOperands extra first).2.2)) ≠ .ub f := by
  let base := (pairOperands extra first).1
  let dest := [(pairOperands extra first).2.1, (pairOperands extra first).2.2]
  obtain ⟨addr, hReg, hFit, hAlign⟩ := pair_operand_bounds hpre hg hd ha hi
  have hn : Assumptions.all.any (·.ncLoads t.pc) = true := by
    rw [ha.1, hd]
    exact pair_nc extra first high
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := base) (w := 64)
    rfl rfl rfl rfl rfl]
  change loadTmpl Assumptions.all L g t .global true 32 dest base 0 ≠ _
  have hLoc : effAddr L g t .global base 0 = .ok ⟨.global, 0, addr⟩ :=
    effAddr_global hReg hFit
  simp only [loadTmpl, hLoc, bind, Except.bind, dest, List.length_cons,
    List.length_nil, Nat.reduceAdd]
  rw [elemAcc_ok (by decide) (by simpa using hAlign)]
  simp only [hn, true_and, ↓reduceIte]
  intro he
  cases he

private def coordAccess (extra : Bool) : MemAccess where
  kind := .store
  space := some (.shared .cta)
  sem := .weak
  elem := .int .b 32
  vec := 2
  addr := ⟨.reg (if extra then 651 else 612) 32, 221728⟩
  srcs := [.reg (if extra then 638 else 600), .reg (if extra then 643 else 604)]

private theorem coord_tmpl_ok (hpre : Pre P L mem0)
    {d : D} {t : TState} {extra high : Bool} (hd : d.site = .coord extra high)
    (ha : AtD P L g d t) (hi : Inv P L g d) (f : Fault) :
    eventTmpl Assumptions.all L g t (.mem (coordAccess extra)) ≠ .ub f := by
  let base := if extra then 651 else 612
  let lo := if extra then 638 else 600
  let hiReg := if extra then 643 else 604
  let addr := L.sharedBase + (8 * laneOf L g + 256 * d.phase)
  let word := coordValue P L g d.block (laneOf L g) (if high then 1 else 0)
  have hReg : t.regs base = some (b32 addr) := by
    cases extra
    · exact ha.reg (r := 612) (by rw [hd]; cases high <;> decide +kernel)
    · exact ha.reg (r := 651) (by rw [hd]; cases high <;> decide +kernel)
  have hsub : t.sub = if high then 1 else 0 := by rw [ha.2.1, hd]; cases high <;> rfl
  have hVal : t.regs (if t.sub = 0 then lo else hiReg) = some (b32 word) := by
    cases extra <;> cases high
    · rw [hsub]
      exact ha.reg (r := 600) (by rw [hd]; decide +kernel)
    · rw [hsub]
      exact ha.reg (r := 604) (by rw [hd]; decide +kernel)
    · rw [hsub]
      exact ha.reg (r := 638) (by rw [hd]; decide +kernel)
    · rw [hsub]
      exact ha.reg (r := 643) (by rw [hd]; decide +kernel)
  have hwindow := sharedBase_lt hpre
  have hphase := hi.phase
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hFit : addr + 221728 < 2 ^ 32 := by dsimp [addr]; omega
  have hAlign : (addr + 221728) % 8 = 0 := by
    have hBase : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
    dsimp [addr]
    omega
  have hLoc : effAddr L g t .shared base 221728 =
      .ok ⟨.shared, g / L.block, addr + 221728⟩ := effAddr_b32_off hReg hFit
  have hsrc : ([.reg lo, .reg hiReg] : List Opnd)[t.sub]? =
      some (.reg (if t.sub = 0 then lo else hiReg)) := by
    cases high <;> simp [hsub]
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32)
    rfl rfl rfl rfl rfl]
  change storeTmpl L g t .shared 32 base 221728 [.reg lo, .reg hiReg] ≠ _
  simp only [storeTmpl, hLoc, bind, Except.bind, List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [elemAcc_ok (by decide) (by simpa using hAlign)]
  simp only [hsrc, readValue, readReg, hVal, pure, Except.pure,
    show storeValue 32 (b32 word) = .ok (b32 word) by rfl]
  intro he
  cases he

private def validAccess (extra : Bool) : MemAccess where
  kind := .store
  space := some (.shared .cta)
  sem := .weak
  elem := .int .b 8
  addr := ⟨.reg (if extra then 652 else 613) 32, 221696⟩
  srcs := [.reg (if extra then 511 else 508)]

private theorem valid_tmpl_ok (hpre : Pre P L mem0) {d : D} {t : TState} {extra : Bool}
    (hd : d.site = .valid extra) (ha : AtD P L g d t) (hi : Inv P L g d) (f : Fault) :
    eventTmpl Assumptions.all L g t (.mem (validAccess extra)) ≠ .ub f := by
  let base := if extra then 652 else 613
  let src := if extra then 511 else 508
  let addr := L.sharedBase + (8 * d.phase + laneOf L g / 4)
  let word := validWord P L g d.block (laneOf L g)
  have hReg : t.regs base = some (b32 addr) := by
    cases extra
    · exact ha.reg (r := 613) (by rw [hd]; decide +kernel)
    · exact ha.reg (r := 652) (by rw [hd]; decide +kernel)
  have hVal : t.regs src = some (b32 word) := by
    cases extra
    · exact ha.reg (r := 508) (by rw [hd]; decide +kernel)
    · exact ha.reg (r := 511) (by rw [hd]; decide +kernel)
  have hsub : t.sub = 0 := by rw [ha.2.1, hd]; rfl
  have hwindow := sharedBase_lt hpre
  have hphase := hi.phase
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hFit : addr + 221696 < 2 ^ 32 := by dsimp [addr]; omega
  have hLoc : effAddr L g t .shared base 221696 =
      .ok ⟨.shared, g / L.block, addr + 221696⟩ := effAddr_b32_off hReg hFit
  have hword :
      storeValue 8 (b32 word) = .ok (.bits 8 (BitVec.ofNat 64 (word % 256))) := by
    have hm (n : Nat) : n % 18446744073709551616 % 256 = n % 256 :=
      Nat.mod_mod_of_dvd _ (by decide)
    nf_simp [storeValue, Value.bitPattern, Value.bytes, pure, Except.pure, hm]
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32)
    rfl rfl rfl rfl rfl]
  change storeTmpl L g t .shared 8 base 221696 [.reg src] ≠ _
  simp only [storeTmpl, hLoc, bind, Except.bind, hsub]
  rw [elemAcc_ok (by decide) (Nat.mod_one _)]
  simp only [List.getElem?_singleton, ite_true, readValue, readReg, hVal, pure, Except.pure, hword]
  intro he
  cases he

/-- All represented index-warp events have defined templates. -/
theorem tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads)
    {d : D} {t : TState} {ins : Instr} (ha : (Machine.code P L g).AtD (.index d) t)
    (hi : Inv P L g d) (hc : kernel.code[(Machine.code P L g).pc (.index d)]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hcode : kernel.code[d.site.pc]? = some ins := hc
  cases hd : d.site
  case pair extra first high =>
    rw [hd] at hcode
    obtain rfl := Option.some.inj (hcode.symm.trans (pair_code extra first high))
    exact pair_tmpl_ok hpre hg hd ha hi f
  case coord extra high =>
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (coordAccess extra)⟩ := by
      rw [hd]
      cases extra
      · exact Flow.code_2471
      · exact Flow.code_2560
    obtain rfl := Option.some.inj (hcode.symm.trans hc')
    exact coord_tmpl_ok hpre hd ha hi f
  case valid extra =>
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (validAccess extra)⟩ := by
      rw [hd]
      cases extra
      · exact Flow.code_2474
      · exact Flow.code_2563
    obtain rfl := Option.some.inj (hcode.symm.trans hc')
    exact valid_tmpl_ok hpre hd ha hi f
  all_goals exact control_tmpl_ok hpre ha hi hc (by simp [hd]) (by simp [hd]) (by simp [hd]) f

/-- At a coordinate or mask store, the template is a defined weak write. -/
theorem write_template (hpre : Pre P L mem0)
    {d : D} {t : TState} {ins : Instr}
    (hd : (∃ extra high, d.site = .coord extra high) ∨ ∃ extra, d.site = .valid extra)
    (ha : AtD P L g d t) (hi : Inv P L g d) (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ a bs v, a.release = false ∧ eventTmpl Assumptions.all L g t ins.op = .write a bs v := by
  have defined {w base : Nat} {off : Int} {srcs : List Opnd}
      (hOk : ∀ f, storeTmpl L g t .shared w base off srcs ≠ .ub f) :
      ∃ a bs v, a.release = false ∧ storeTmpl L g t .shared w base off srcs = .write a bs v := by
    rcases storeTmpl_cases (L := L) (g := g) (t := t) (sp := .shared) (w := w)
      (base := base) (off := off) (srcs := srcs) with ⟨f, h⟩ | ⟨a, bs, h⟩
    · exact (hOk f h).elim
    · exact ⟨a, bs, _, storeTmpl_noRelease h, h⟩
  rcases hd with ⟨extra, high, hd⟩ | ⟨extra, hd⟩
  · have hCode : kernel.code[d.site.pc]? = some ⟨none, .mem (coordAccess extra)⟩ := by
      rw [hd]
      cases extra
      · exact Flow.code_2471
      · exact Flow.code_2560
    obtain rfl := Option.some.inj (hc.symm.trans hCode)
    have hOk := coord_tmpl_ok hpre hd ha hi
    rw [eventTmpl, memTmpl_store (sp := .shared) (base := if extra then 651 else 612)
      (w := 32) rfl rfl rfl rfl rfl] at hOk ⊢
    exact defined hOk
  · have hCode : kernel.code[d.site.pc]? = some ⟨none, .mem (validAccess extra)⟩ := by
      rw [hd]
      cases extra
      · exact Flow.code_2474
      · exact Flow.code_2563
    obtain rfl := Option.some.inj (hc.symm.trans hCode)
    have hOk := valid_tmpl_ok hpre hd ha hi
    rw [eventTmpl, memTmpl_store (sp := .shared) (base := if extra then 652 else 613)
      (w := 32) rfl rfl rfl rfl rfl] at hOk ⊢
    exact defined hOk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbIndex
