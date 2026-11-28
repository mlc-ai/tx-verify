-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.SafeA
public import Lemmas.Flow.UbFree
import Kernels.InklingRelDecode.Flow.Code.Part015
import Kernels.InklingRelDecode.Flow.Code.Part019
import Kernels.InklingRelDecode.Flow.Code.Part035
import Kernels.InklingRelDecode.Flow.Code.Part036

@[expose] public section

/-! # The softmax's tensor-memory loads and stores are not undefined behaviour

The address register of each of the four accesses is the launch's base word plus a column and the
lane group of the warp (`Control.valueOf`), given the base word of the entry (`Iface.BaseRead`)
and the broadcast of the warp index (`Carry.base`, the word the shuffle at pc 1261 returned).
The values stored are registers tagged as words of four bytes. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Control.Entry} {L : Launch} {g : Nat} {d : Data.D} {t : TState} {ins : Instr}

/-- The warp's lane group: the broadcast word names it. -/
def Names (L : Launch) (g : Nat) (v : Value) : Prop :=
  ∃ x, v = b32 x ∧ x % 4 = g % L.block / 32 % 4

theorem basePlus_b32 (x a : Nat) :
    Control.basePlus (b32 x) a = b32 ((x % 2 ^ 32 + a) % 2 ^ 32) := by
  simp [Control.basePlus, Control.u32, Lib.word, b32, Value.regBits, truncBits]
  congr 1
  omega

/-- The address of the score tile's load and of the first store: column `i % 2 * 128`. -/
theorem addr_1676 (hb : e.base = b32 0) (hx : Names L g d.c.held.base) :
    Control.valueOf e L g d.c 1676 =
      b32 (d.c.i % 2 * 128 + g % L.block / 32 % 4 * 2 ^ 21) := by
  obtain ⟨x, hx, hq⟩ := hx
  have h : Control.valueOf e L g d.c 1676 =
      Control.basePlus (Control.basePlus e.base (d.c.i % 2 * 128))
        ((Lib.word d.c.held.base).toNat % 4 * 2 ^ 21) := rfl
  rw [h, hb, basePlus_b32, basePlus_b32, hx]
  simp only [Lib.word, b32, Value.regBits, truncBits, Option.getD_some, BitVec.toNat_ofNat]
  congr 2
  have : x % 2 ^ 32 % 4 = x % 4 := Nat.mod_mod_of_dvd _ (by decide)
  omega

/-- The address of the accumulator's load and of the second store: column 256. -/
theorem addr_1611 (hb : e.base = b32 0) (hx : Names L g d.c.held.base) :
    Control.valueOf e L g d.c 1611 = b32 (256 + g % L.block / 32 % 4 * 2 ^ 21) := by
  obtain ⟨x, hx, hq⟩ := hx
  have h : Control.valueOf e L g d.c 1611 =
      Control.basePlus (Control.basePlus e.base 256)
        ((Lib.word d.c.held.base).toNat % 4 * 2 ^ 21) := rfl
  rw [h, hb, basePlus_b32, basePlus_b32, hx]
  simp only [Lib.word, b32, Value.regBits, truncBits, Option.getD_some, BitVec.toNat_ofNat]
  congr 2
  have : x % 2 ^ 32 % 4 = x % 4 := Nat.mod_mod_of_dvd _ (by decide)
  omega

/-- A column and the warp's lane group name a supported address of a `16x32bx2` access. -/
theorem tcAddr_ok {off col : Nat} (hc : col + off < 2 ^ 16) :
    tcDataAddressOk L g (.s16x32bx2 off) (col + g % L.block / 32 % 4 * 2 ^ 21) = true := by
  have key : ∀ q, q < 4 → q = g % L.block / 32 % 4 →
      tcDataAddressOk L g (.s16x32bx2 off) (col + q * 2 ^ 21) = true := by
    intro q hq hqd
    simp only [tcDataAddressOk, TcShape.splitOk, tmemLaneFieldOk, laneBase, TcShape.lanes,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ← hqd]
    have hA : (col + q * 2 ^ 21) % 2 ^ 16 = col := by omega
    have hB : (col + q * 2 ^ 21) / 2 ^ 16 = q * 32 := by omega
    rw [hA, hB]
    exact ⟨by omega, by norm_num, Or.inr ⟨by omega, by omega⟩⟩
  exact key _ (Nat.mod_lt _ (by norm_num)) rfl

variable {Q : TState → Prop}

theorem addr_lt {i q : Nat} (hq : q < 4) : i % 2 * 128 + q * 2 ^ 21 < 2 ^ 32 := by omega

theorem hq_lt (L : Launch) (g : Nat) : g % L.block / 32 % 4 < 4 := Nat.mod_lt _ (by norm_num)

/-- **The load of the score tile is not undefined behaviour.** -/
theorem safe_ldS (hl : SoftLaunch L) (hb : e.base = b32 0) (hx : Names L g d.c.held.base)
    (hat : (Data.code e L g).AtD d t) (hs : d.c.site = .ldS)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r := reg_soft hat (r := 1676) (hs ▸ (by decide : 1676 ∈ Control.ctlLive Site.ldS.pc))
  rw [addr_1676 hb hx] at r
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1265)
  have hlt := addr_lt (i := d.c.i) (hq_lt L g)
  refine tcLd_word_ok (x := BitVec.ofNat 64 (d.c.i % 2 * 128 + g % L.block / 32 % 4 * 2 ^ 21))
    hl.block (by decide) r ?_ ?_ f
  · simp only [BitVec.toNat_ofNat]
    omega
  · simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact tcAddr_ok (by omega)

/-- **The load of the accumulator is not undefined behaviour.** -/
theorem safe_ldO (hl : SoftLaunch L) (hb : e.base = b32 0) (hx : Names L g d.c.held.base)
    (hat : (Data.code e L g).AtD d t) (hs : d.c.site = .ldO)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r := reg_soft hat (r := 1611) (hs ▸ (by decide : 1611 ∈ Control.ctlLive Site.ldO.pc))
  rw [addr_1611 hb hx] at r
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2260)
  have hlt := hq_lt L g
  refine tcLd_word_ok (x := BitVec.ofNat 64 (256 + g % L.block / 32 % 4 * 2 ^ 21))
    hl.block (by decide) r ?_ ?_ f
  · simp only [BitVec.toNat_ofNat]
    omega
  · simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact tcAddr_ok (by omega)

/-- The instruction at `pc` is a tensor-memory store whose sources are registers tagged as words
of four bytes. -/
def tcStShape (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨_, .tcSt _ ss _⟩ =>
    ss.all fun o => match o with
      | .reg r => match (lateQt pc).lookup r with
        | some .dat32 => true
        | _ => false
      | _ => false
  | _ => false

theorem tcSt_srcs {pc ta : Nat} {ss : List Opnd} {sh : TcShape} {gd : Option (Nat × Bool)}
    (hc : kernel.code[pc]? = some ⟨gd, .tcSt ta ss sh⟩) (h : tcStShape pc = true)
    (hT : TypedF (lateQt pc) t) :
    ∃ vals, ss.mapM (readValue L g t 32) = .ok vals ∧ vals.all (·.bytes = 4) = true := by
  unfold tcStShape at h
  rw [hc] at h
  refine mapM_regs_ok fun p hp => ?_
  have hall := List.all_eq_true.mp h (ss[p]) (List.getElem_mem hp)
  cases ho : ss[p] with
  | reg r =>
    rw [ho] at hall
    simp only at hall
    split at hall
    · rename_i hk
      obtain ⟨x, hx, hd⟩ := hT r _ hk
      exact ⟨r, x, by rw [List.getElem?_eq_getElem hp, ho], hx, hd.2.1⟩
    · cases hall
  | _ => rw [ho] at hall; cases hall

/-- **The store of the packed bias words is not undefined behaviour.** -/
theorem safe_tmemSt (hl : SoftLaunch L) (hb : e.base = b32 0) (hx : Names L g d.c.held.base)
    (hat : (Data.code e L g).AtD d t) (hq : QTF lateQt t) (hs : d.c.site = .tmemSt)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r := reg_soft hat (r := 1676) (hs ▸ (by decide : 1676 ∈ Control.ctlLive Site.tmemSt.pc))
  rw [addr_1676 hb hx] at r
  have hpc : t.pc = 1009 := by
    have : t.pc = d.c.site.pc := hat.1
    rw [hs] at this
    exact this
  have hT : TypedF (lateQt 1009) t := by
    have := hq
    rwa [QTF, hpc] at this
  rw [hs] at hc
  have hc' := hc.symm.trans Flow.code_1009
  obtain ⟨vals, hv, h4⟩ := tcSt_srcs (L := L) (g := g) (t := t) Flow.code_1009
    (by decide +kernel) hT
  have hlt := addr_lt (i := d.c.i) (hq_lt L g)
  obtain rfl := Option.some.inj hc'
  exact tcSt_ok hl.block (by decide) r hlt (tcAddr_ok (by omega)) hv h4 f

/-- **The store of the rescaled accumulator is not undefined behaviour.** -/
theorem safe_stO (hl : SoftLaunch L) (hb : e.base = b32 0) (hx : Names L g d.c.held.base)
    (hat : (Data.code e L g).AtD d t) (hq : QTF lateQt t) (hs : d.c.site = .stO)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r := reg_soft hat (r := 1611) (hs ▸ (by decide : 1611 ∈ Control.ctlLive Site.stO.pc))
  rw [addr_1611 hb hx] at r
  have hpc : t.pc = 2328 := by
    have : t.pc = d.c.site.pc := hat.1
    rw [hs] at this
    exact this
  have hT : TypedF (lateQt 2328) t := by
    have := hq
    rwa [QTF, hpc] at this
  rw [hs] at hc
  obtain ⟨vals, hv, h4⟩ := tcSt_srcs (L := L) (g := g) (t := t) Flow.code_2328
    (by decide +kernel) hT
  have hlt := hq_lt L g
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2328)
  exact tcSt_ok hl.block (by decide) r (by omega) (tcAddr_ok (by omega)) hv h4 f

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
