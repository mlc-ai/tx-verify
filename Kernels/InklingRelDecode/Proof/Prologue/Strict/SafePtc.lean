-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.SafeStore
import Kernels.InklingRelDecode.Proof.Lib.CopyOk
import Kernels.InklingRelDecode.Proof.Prologue.CopyAddress
import Kernels.InklingRelDecode.Proof.Prologue.ShapeCopy
import Lemmas.Flow.Step.ShapeClasses
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004

@[expose] public section

/-! # The prologue's tensor copies are not undefined behaviour

The twelve copies of the preload read the map from the parameter pointer, write the half tile of
the broadcast's low bit at the site's offset, signal the block's ready barrier and start at the
column and row of the block's tags: the column is a multiple of 8 as the head's column offset is. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control Arith32

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The register a state's tag names holds the tag's value. -/
theorem tag_reg {d : Data.D} {t : TState} (hat : (Data.code Q L g w).AtD d t)
    {τ : Data.Tag} (hτ : τ ∈ Data.tags d.c.site) : t.regs τ.reg = some (τ.val Q L g d) := by
  obtain ⟨-, -, -, -, h⟩ := hat
  exact holds_mem ((holds_append _ _ _).mp h).2 (List.mem_map.mpr ⟨τ, hτ, rfl⟩)

/-- The destination register of copy `j` of block `b`. -/
def ptcDstReg (b : Fin 3) (j : Fin 4) : Nat :=
  ([[682, 685, 688, 690], [702, 705, 708, 710], [724, 727, 730, 732]].getD b.val []).getD j.val 0

/-- The column tag and the row tag of copy `j` of block `b`. -/
def ptcCol (b : Fin 3) (j : Fin 4) : Data.Tag := .col b ⟨j.val % 2, by omega⟩
def ptcRow (b : Fin 3) (j : Fin 4) : Data.Tag := .row b ⟨j.val / 2, by omega⟩

/-- The code at `pc` is the tensor copy with these registers. -/
def ptcShape (pc d rc rr mb : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨_, .cpTensor false false d' 0 (.reg 1949) [.reg c, .reg r] m 0 none .tile none⟩ =>
    d' == d && c == rc && r == rr && m == mb
  | _ => false

theorem ptc_shape : ∀ (b : Fin 3) (j : Fin 4), ptcShape (Site.ptc b j).pc (ptcDstReg b j)
    (ptcCol b j).reg (ptcRow b j).reg (613 + 2 * b.val) = true := by decide +kernel

theorem ptc_tags : ∀ (b : Fin 3) (j : Fin 4), ptcCol b j ∈ Data.tags (.ptc b j) ∧
    ptcRow b j ∈ Data.tags (.ptc b j) := by decide +kernel

theorem ptc_live : ∀ (b : Fin 3) (j : Fin 4), ptcDstReg b j ∈ ctlLive (Site.ptc b j).pc ∧
    1949 ∈ ctlLive (Site.ptc b j).pc ∧ 613 + 2 * b.val ∈ ctlLive (Site.ptc b j).pc := by
  decide +kernel

theorem bits_b32 {x : BitVec 64} (h : x.toNat < 2 ^ 32) : Value.bits 32 x = b32 x.toNat := by
  unfold b32
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The destination register of a copy holds the half tile of the broadcast's low bit plus the
site's offset. -/
theorem ptc_dst_value (b : Fin 3) (j : Fin 4) (bc : Value) (room : L.sharedBase + 213340 ≤ 2 ^ 18) :
    copyValue L bc (ptcDstReg b j) =
      b32 (L.sharedBase + 16384 * ((Lib.word bc).toNat % 2) + copyOffset b j) := by
  have key : ∀ k : Int, k = ((copyOffset b j : Nat) : Int) →
      Value.bits 32 (addi (copyBase L bc) k) =
        b32 (L.sharedBase + 16384 * ((Lib.word bc).toNat % 2) + copyOffset b j) := by
    intro k hk
    subst hk
    have hd := copy_dest_value bc b j room
    have hmax := offset_bound b j
    have hw : (Lib.word bc).toNat % 2 < 2 := Nat.mod_lt _ (by omega)
    rw [bits_b32 (by rw [hd]; omega), hd]
  fin_cases b <;> fin_cases j
  · simp only [ptcDstReg, copyValue, copy_base_value bc room]
    simp [b32, copyOffset]
  all_goals exact key _ (by decide)

theorem ptc_inst {pc d rc rr mb : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins)
    (h : ptcShape pc d rc rr mb = true) : ∃ gd, ins = ⟨gd, .cpTensor false false d 0 (.reg 1949)
      [.reg rc, .reg rr] mb 0 none .tile none⟩ := by
  unfold ptcShape at h
  rw [hc] at h
  split at h
  · rename_i gd d' c r m heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
    simp only [Option.some.injEq] at heq
    exact ⟨_, heq⟩
  · cases h

/-- **A tensor copy of the prologue is not undefined behaviour.** -/
theorem safe_ptc {m} (hp : Pre Q L m) (hg : g < L.threads) {d : Data.D} {t : TState}
    {ins : Instr} (hat : (Data.code Q L g w).AtD d t) {b : Fin 3} {j : Fin 4}
    (hs : d.c.site = .ptc b j) (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hcta : g / L.block < L.grid := by
    rw [Launch.threads] at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  rw [hs] at hc
  obtain ⟨gd, rfl⟩ := ptc_inst hc (ptc_shape b j)
  obtain ⟨hl1, hl2, hl3⟩ := ptc_live b j
  have room : L.sharedBase + 213340 ≤ 2 ^ 18 := hp.sharedRange
  have hmap : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0) :=
    reg_ctl hat (r := 1949) (hs ▸ hl2)
  have hcr : copyReg (ptcDstReg b j) = true :=
    (by decide +kernel : ∀ (b : Fin 3) (j : Fin 4), copyReg (ptcDstReg b j) = true) b j
  have hd : t.regs (ptcDstReg b j) = some (b32 (L.sharedBase +
      16384 * ((Lib.word d.c.broadcast).toNat % 2) + copyOffset b j)) := by
    have := reg_ctl hat (r := ptcDstReg b j) (hs ▸ hl1)
    rw [this]
    simp only [valueOf, hcr, ↓reduceIte, ptc_dst_value b j _ room]
  have hcol : t.regs (ptcCol b j).reg = some (b32 ((64 * ((Lib.word d.c.broadcast).toNat % 2) +
      128 * (j.val % 2) + Q.headCols * (L.ctaidOf (g / L.block)).get .y) % 2 ^ 32)) :=
    tag_reg hat (hs ▸ (ptc_tags b j).1)
  have hrow : t.regs (ptcRow b j).reg = some (b32 (((Lib.word
      (d.v.pay b ⟨j.val / 2, by omega⟩)).toNat * Q.pageRows +
      Q.headRows * (L.ctaidOf (g / L.block)).get .y) % 2 ^ 32)) :=
    tag_reg hat (hs ▸ (ptc_tags b j).2)
  obtain ⟨reg, bound, aligned⟩ := object_reg hp (atD_ctl hat) (readyIndex b) (hs ▸ hl3)
  have hmb : mbarLoc L g t (613 + 2 * b.val) 0 = .ok ⟨.shared, g / L.block,
      L.sharedBase + MbarRow.initOffset (readyIndex b)⟩ := mbarLoc_b32_ok reg bound aligned
  have hh8 : (Q.headCols * (L.ctaidOf (g / L.block)).get .y) % 8 = 0 :=
    Nat.mod_eq_zero_of_dvd ((Nat.dvd_of_mod_eq_zero hp.headColsAlign).trans (Nat.dvd_mul_right _ _))
  have al := hp.sharedAlignment
  have ho : copyOffset b j % 128 = 0 := by unfold copyOffset; omega
  have hmax := offset_bound b j
  have hw2 : (Lib.word d.c.broadcast).toNat % 2 < 2 := Nat.mod_lt _ (by omega)
  exact Lib.cp_ok hp hcta hmap hd hcol hrow (by omega) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (by omega) (by omega) hmb f

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
