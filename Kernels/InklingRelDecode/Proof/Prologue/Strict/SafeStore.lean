-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.SafeMbar
import Kernels.InklingRelDecode.Proof.Prologue.QueryAddress
import Kernels.InklingRelDecode.Proof.Lib.QTile
import Lemmas.Flow.StoreSvOk
import Lemmas.Flow.StoreSharedSym
import Lemmas.Flow.LoadShared
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Store
import Kernels.InklingRelDecode.Proof.Prologue.Strict.QStore
import Kernels.InklingRelDecode.Flow.Code.Part008

@[expose] public section

/-! # The prologue's shared stores are not undefined behaviour

The 32 elements of the eight query stores (`st.shared.v4.b32` of the packed halves at the lane's
swizzled slot of its group's tile) and the three words stored at the end (`st8`, and the two
elements of `st9`, at fixed offsets of the shared window). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- **A 32-bit store of two packed 2-byte values has a value**: four bytes, or a wider raw
pattern that the store truncates. -/
theorem storeValue_join {a b : Value} (ha : a.bytes = 2) (hb : b.bytes = 2) :
    ∃ v, storeValue 32 (joinValue a b) = .ok v := by
  have hp : (Value.pair a b).bytes = 32 / 8 := by simp [Value.bytes, ha, hb]
  unfold joinValue
  split
  · rename_i whole n whole' off m
    split_ifs with h
    · simp only [Value.bytes] at ha hb
      exact ⟨_, storeValue_of_bytes (by rw [h.2.2]; omega)⟩
    · exact ⟨_, storeValue_of_bytes hp⟩
  · rename_i w x w' y
    split_ifs with h
    · simp only [Value.bytes] at ha hb
      by_cases h4 : 2 * w / 8 = 32 / 8
      · exact ⟨_, storeValue_of_bytes (by simp only [Value.bytes]; exact h4)⟩
      · have hlt : 32 / 8 < 2 * w / 8 := by omega
        refine ⟨.bits 32 (truncBits 32 (BitVec.ofNat 64 (x ||| y <<< w).toNat)), ?_⟩
        have h4' : (Value.bits (2 * w) (x ||| y <<< w)).bytes ≠ 32 / 8 := h4
        have hlt' : 32 / 8 < (Value.bits (2 * w) (x ||| y <<< w)).bytes := hlt
        simp only [storeValue, h4', hlt', ↓reduceIte]
        rfl
    · exact ⟨_, storeValue_of_bytes hp⟩
  · exact ⟨_, storeValue_of_bytes hp⟩

theorem stq_live : ∀ (i : Fin 8) (j : Fin 4), 746 + 5 * i.val ∈ ctlLive (Site.stq i j).pc := by
  decide +kernel

theorem qw_mem : ∀ (i : Fin 8) (j : Fin 4), Data.Tag.qw i j ∈ Data.tags (.stq i j) := by
  decide +kernel

/-- The register of an element of a query store holds the pack of two halves. -/
theorem stq_src {d : Data.D} {t : TState} (hat : (Data.code Q L g w).AtD d t) {i : Fin 8}
    {j : Fin 4} (hs : d.c.site = .stq i j) :
    t.regs (747 + 5 * i.val + j.val) = some (Data.Tag.val Q L g d (.qw i j)) := by
  obtain ⟨-, -, -, -, h⟩ := hat
  have hm : (Data.Tag.reg (.qw i j), Data.Tag.val Q L g d (.qw i j)) ∈ Data.dF Q L g d := by
    refine List.mem_map.mpr ⟨.qw i j, ?_, rfl⟩
    rw [hs] at *
    exact qw_mem i j
  exact holds_mem ((holds_append _ _ _).mp h).2 hm

/-- The access of a query store. -/
def stqAcc (i : Fin 8) : MemAccess :=
  {kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := 4,
   addr := ⟨.reg (746 + 5 * i.val) 32, 0⟩, srcs := srcs i}

/-- **An element of a query store is not undefined behaviour** for any halves of two bytes. -/
theorem safe_stq {m} (hp : Pre Q L m) (hlane : g % L.block < 128) {d : Data.D} {t : TState}
    {ins : Instr} (hat : (Data.code Q L g w).AtD d t) (hk : Ok Q L g d) {i : Fin 8} {j : Fin 4}
    (hs : d.c.site = .stq i j) (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have reg := reg_ctl hat (r := 746 + 5 * i.val) (hs ▸ stq_live i j)
  rw [query_register hp i] at reg
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (fetchQueryStore i))
  have hsub : t.sub = j.val := by
    have := hat.2.1
    change t.sub = d.c.site.sub at this
    rw [hs] at this
    exact this
  have src := stq_src hat hs
  obtain ⟨x, hx⟩ := storeValue_join
    (qv_bytes (L := L) (g := g) d hk.qBytes ⟨8 * i.val + 2 * j.val, by omega⟩)
    (qv_bytes (L := L) (g := g) d hk.qBytes ⟨8 * i.val + 2 * j.val + 1, by omega⟩)
  have room := hp.sharedRange
  have align := hp.sharedAlignment
  have sw := Lib.qSwz_spec _ hlane
  have gr := Lib.qGroup_lt i i.isLt
  have bound := (queryAddress_range hp g i).2
  have hea : effAddr L g t .shared (746 + 5 * i.val) 0 =
      .ok ⟨.shared, g / L.block, queryAddress L g i + 0⟩ := by
    have := effAddr_b32_off (L := L) (g := g) (t := t) (off := 0) reg
      (by unfold sharedBytes at room; omega)
    simpa using this
  have src' : t.regs (747 + 5 * i.val + j.val) = some (joinValue
      (Data.qv L g d ⟨8 * i.val + 2 * j.val, by omega⟩)
      (Data.qv L g d ⟨8 * i.val + 2 * j.val + 1, by omega⟩)) := src
  have hop : storeOp i = .mem (stqAcc i) := rfl
  rw [hop]
  refine storeAl_sv_ok (a := stqAcc i) (sp := .shared) (base := 746 + 5 * i.val) (w := 32)
    (r := 747 + 5 * i.val + j.val) (x := x) (loc := ⟨.shared, g / L.block, queryAddress L g i + 0⟩)
    (v := joinValue (Data.qv L g d ⟨8 * i.val + 2 * j.val, by omega⟩)
      (Data.qv L g d ⟨8 * i.val + 2 * j.val + 1, by omega⟩))
    rfl rfl rfl rfl rfl hea (by simp [stqAcc, DType.width]) ?_ ?_ src' hx f
  · change (queryAddress L g i + 0) % (32 / 8 * 4) = 0
    unfold queryAddress
    omega
  · rw [hsub]
    fin_cases j <;> simp only [stqAcc, srcs] <;> simp <;> omega

/-- The wrapped address of a shared symbol plus an offset, in the window, is aligned. -/
theorem wrap_sym {sb off n : Nat} (hsb : sb % 1024 = 0) (hr : sb + off < 2 ^ 32)
    (hn : n ∣ 1024) (ho : off % n = 0) :
    wrapAddr 32 (BitVec.ofNat 64 (sb + 0)) (off : Int) % n = 0 := by
  simp only [wrapAddr, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  have e2 : ((off : Int) % ((2 ^ 64 : Nat) : Int)).toNat = off := by
    rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
    exact Int.toNat_natCast off
  rw [e2]
  have h1 : ((sb + 0) % 2 ^ 64 + off) % 2 ^ 64 % 2 ^ 32 % 2 ^ 64 = sb + off := by omega
  rw [h1]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (hn.trans (Nat.dvd_of_mod_eq_zero hsb))
    (Nat.dvd_of_mod_eq_zero ho))

theorem readValue_reg {w r : Nat} {t : TState} {v : Value} (hr : t.regs r = some v) :
    readValue L g t w (.reg r) = .ok v := by
  simp [readValue, readReg, hr, pure, Except.pure]

/-- **The word store `st8` is not undefined behaviour.** -/
theorem safe_st8 {m} (hp : Pre Q L m) {d : Data.D} {t : TState} {ins : Instr}
    (hat : (Data.code Q L g w).AtD d t) (hs : d.c.site = .st8)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_570)
  have hsub : t.sub = 0 := by
    have := hat.2.1
    change t.sub = d.c.site.sub at this
    rw [hs] at this
    exact this
  have room := hp.sharedRange
  have align := hp.sharedAlignment
  unfold sharedBytes at room
  refine stSharedSym_ok (o := 0) (w := .cta) (os := .imm 16777730) rfl rfl rfl rfl rfl rfl rfl
    rfl (by decide) ?_ (by simp [hsub]) ⟨.bits 32 (truncBits 32 (BitVec.ofInt 64 16777730)),
      rfl, rfl⟩ f
  exact wrap_sym (off := 213336) align (by omega) (by decide) (by decide)

/-- **An element of the store `st9` is not undefined behaviour.** -/
theorem safe_st9 {m} (hp : Pre Q L m) {d : Data.D} {t : TState} {ins : Instr}
    (hat : (Data.code Q L g w).AtD d t) {j : Fin 2} (hs : d.c.site = .st9 j)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have keys : ∀ j : Fin 2, 493 ∈ ctlLive (Site.st9 j).pc ∧ 487 ∈ ctlLive (Site.st9 j).pc := by
    decide +kernel
  have r493 := reg_ctl hat (r := 493) (hs ▸ (keys j).1)
  have r487 := reg_ctl hat (r := 487) (hs ▸ (keys j).2)
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_571)
  have hsub : t.sub = j.val := by
    have := hat.2.1
    change t.sub = d.c.site.sub at this
    rw [hs] at this
    exact this
  have room := hp.sharedRange
  have align := hp.sharedAlignment
  unfold sharedBytes at room
  fin_cases j
  · refine stSharedSym_ok (o := 0) (w := .cta) (os := .reg 493) rfl rfl rfl rfl rfl rfl rfl
      rfl (by decide) ?_ (by simp [hsub]) ⟨_, readValue_reg r493, rfl⟩ f
    exact wrap_sym (off := 212992) align (by omega) (by decide) (by decide)
  · refine stSharedSym_ok (o := 0) (w := .cta) (os := .reg 487) rfl rfl rfl rfl rfl rfl rfl
      rfl (by decide) ?_ (by simp [hsub]) ⟨_, readValue_reg r487, rfl⟩ f
    exact wrap_sym (off := 212992) align (by omega) (by decide) (by decide)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
