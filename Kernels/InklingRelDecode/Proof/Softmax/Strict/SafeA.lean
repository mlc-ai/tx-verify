-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Base
public import Lemmas.Flow.TmplOkMore
public import Lemmas.Flow.UbStop
public import Lemmas.Flow.ShflBytesOk
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.MemAl
import Lemmas.Flow.RegBits
import Kernels.InklingRelDecode.Flow.Code.Part008
import Kernels.InklingRelDecode.Flow.Code.Part015
import Kernels.InklingRelDecode.Flow.Code.Part019
import Kernels.InklingRelDecode.Flow.Code.Part034
import Kernels.InklingRelDecode.Flow.Code.Part035
import Kernels.InklingRelDecode.Flow.Code.Part036

@[expose] public section

/-! # The softmax's polls, barriers, shuffles and shared-memory words are not undefined behaviour

What the launch gives (`SoftLaunch`, from `Pre`): whole warps and the shared window with the
barriers and words of the softmax inside it. A state of the softmax holds the facts of its control
table; the data registers the shuffles and the stores read are typed by `lateQt`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

/-- The launch facts the softmax's events need. -/
structure SoftLaunch (L : Launch) : Prop where
  block : L.block % 32 = 0
  align : L.sharedBase % 1024 = 0
  room : L.sharedBase + 213344 ≤ 2 ^ 32

variable {e : Control.Entry} {L : Launch} {g : Nat} {d : Data.D} {t : TState} {ins : Instr}

/-- A register of the facts of the site holds the table's word. -/
theorem reg_soft (h : (Data.code e L g).AtD d t) {r : Nat}
    (hr : r ∈ Control.ctlLive d.c.site.pc) : t.regs r = some (Control.valueOf e L g d.c r) := by
  obtain ⟨-, -, -, -, hF⟩ := h
  have h2 : Holds t.regs (Control.facts e L g d.c d.c.site.pc ++ Data.dF L d) := hF
  exact holds_mem ((holds_append _ _ _).mp h2).1 (mem_factsFrom hr)

/-- The instruction at `pc` is one whose event is never undefined behaviour. -/
def plainShape (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, op⟩ => plainOk op
  | _ => false

theorem safe_plain_s (hl : SoftLaunch L) {pc : Nat} (hc : kernel.code[pc]? = some ins)
    (h : plainShape pc = true) (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  unfold plainShape at h
  rw [hc] at h
  obtain ⟨gd, op⟩ := ins
  cases gd with
  | none => exact plainOk_tmpl hl.block h f
  | some _ => cases h

/-- The named barriers of the softmax: all threads of a warpgroup. -/
theorem safe_barN (hc : ins = ⟨none, .barSyncN (.imm 0) (.imm 128) true⟩) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  subst hc
  exact (bar_ok (A := Assumptions.all) (L := L) (g := g) (t := t) (id := 0) (n := 128)
    (by decide) (by decide) (by decide) (by decide) f).1

/-- The instruction at `pc` is a full-mask shuffle of a register of four bytes. -/
def shflShape (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .warp ⟨.shfl m, some (.int .b 32), [some _], [.reg r, .imm _, .imm _],
      some (.imm (-1))⟩⟩ =>
    decide (m = .bfly ∨ m = .idx) &&
      match (lateQt pc).lookup r with
      | some .dat32 | some (.old (.bits 32)) => true
      | _ => false
  | _ => false

theorem safe_shfl_s (hl : SoftLaunch L) {pc : Nat} (hc : kernel.code[pc]? = some ins)
    (h : shflShape pc = true) (hT : TypedF (lateQt pc) t) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  unfold shflShape at h
  rw [hc] at h
  obtain ⟨gd, op⟩ := ins
  split at h
  · rename_i m d r b c hm
    simp only [Option.some.injEq, Instr.mk.injEq] at hm
    obtain ⟨-, rfl⟩ := hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hmode, htag⟩ := h
    split at htag
    · rename_i hk
      obtain ⟨x, hx, hd⟩ := hT r _ hk
      exact shfl_bytes_ok (p := none) hmode hl.block hx hd.2.1 f
    · rename_i hk
      obtain ⟨x, hx⟩ := hT r _ hk
      exact shfl_bytes_ok (p := none) hmode hl.block hx rfl f
    · cases htag
  · cases h

theorem poll_parity {r : Nat} {x : Nat} (hr : t.regs r = some (b32 x)) :
    ∃ q, readBits L g t 32 (.reg r) = .ok q :=
  ⟨_, readBits_regBits hr (show (b32 x).regBits = some (BitVec.ofNat 64 x) from rfl)⟩

/-- **The poll of the score tile's barrier is not undefined behaviour.** -/
theorem safe_waitS (hl : SoftLaunch L) (hat : (Data.code e L g).AtD d t) (hs : d.c.site = .waitS)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r874 := reg_soft hat (r := 874) (hs ▸ (by decide : 874 ∈ Control.ctlLive Site.waitS.pc))
  have r875 := reg_soft hat (r := 875) (hs ▸ (by decide : 875 ∈ Control.ctlLive Site.waitS.pc))
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1257)
  have hv : Control.valueOf e L g d.c 874 =
      b32 ((L.sharedBase + d.c.i % 2 * 8 + 213280) % 2 ^ 32) := rfl
  rw [hv] at r874
  have h0 := hl.room
  have h1 : L.sharedBase + d.c.i % 2 * 8 + 213280 < 2 ^ 32 := by omega
  have h2 : (L.sharedBase + d.c.i % 2 * 8 + 213280) % 8 = 0 := by
    have := hl.align
    omega
  rw [Nat.mod_eq_of_lt h1] at r874
  obtain ⟨q, hq⟩ := poll_parity (L := L) (g := g) (x := d.c.i / 2 % 2) r875
  exact wait_loc_ok (mbarLoc_b32_ok r874 h1 h2) hq f

/-- **The poll of the accumulator barrier is not undefined behaviour.** -/
theorem safe_waitO (hl : SoftLaunch L) (hat : (Data.code e L g).AtD d t) (hs : d.c.site = .waitO)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r623 := reg_soft hat (r := 623) (hs ▸ (by decide : 623 ∈ Control.ctlLive Site.waitO.pc))
  have r1532 := reg_soft hat (r := 1532)
    (hs ▸ (by decide : 1532 ∈ Control.ctlLive Site.waitO.pc))
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2239)
  have hv : Control.valueOf e L g d.c 623 = b32 ((L.sharedBase + 213312) % 2 ^ 32) := rfl
  rw [hv] at r623
  have h0 := hl.room
  have h1 : L.sharedBase + 213312 < 2 ^ 32 := by omega
  have h2 : (L.sharedBase + 213312) % 8 = 0 := by
    have := hl.align
    omega
  rw [Nat.mod_eq_of_lt h1] at r623
  obtain ⟨q, hq⟩ := poll_parity (L := L) (g := g) (x := (d.c.i + 1) % 2) r1532
  exact wait_loc_ok (mbarLoc_b32_ok r623 h1 h2) hq f

/-- **The store of the row sum's word is not undefined behaviour.** -/
theorem safe_store10 (hl : SoftLaunch L) (hat : (Data.code e L g).AtD d t)
    (hq : QTF lateQt t) (hs : d.c.site = .store10) (hc : kernel.code[d.c.site.pc]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r1533 := reg_soft hat (r := 1533)
    (hs ▸ (by decide : 1533 ∈ Control.ctlLive Site.store10.pc))
  have hpc : t.pc = 2250 := by
    have : t.pc = d.c.site.pc := hat.1
    rw [hs] at this
    exact this
  have hT : TypedF (lateQt 2250) t := by
    have := hq
    rwa [QTF, hpc] at this
  obtain ⟨y, hy, hd⟩ := hT 1534 .dat32 (by decide +kernel)
  have hsub : t.sub = 0 := hat.2.1
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2250)
  have hv : Control.valueOf e L g d.c 1533 =
      b32 ((L.sharedBase + 212992 + g % L.block / 32 % 4 * 4) % 2 ^ 32) := rfl
  rw [hv] at r1533
  have h0 := hl.room
  have h1 : L.sharedBase + 212992 + g % L.block / 32 % 4 * 4 < 2 ^ 32 := by omega
  have h2 : (L.sharedBase + 212992 + g % L.block / 32 % 4 * 4) % 4 = 0 := by
    have := hl.align
    omega
  rw [Nat.mod_eq_of_lt h1] at r1533
  exact st_ok (ik := .b) (off := 0) r1533 (by omega) (by omega) hsub hy hd.2.1 f

/-- **The reload of the row sum's word is not undefined behaviour.** -/
theorem safe_ldL (hl : SoftLaunch L) (hat : (Data.code e L g).AtD d t) (hs : d.c.site = .ldL)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r500 := reg_soft hat (r := 500) (hs ▸ (by decide : 500 ∈ Control.ctlLive Site.ldL.pc))
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2252)
  have hv : Control.valueOf e L g d.c 500 = b32 ((L.sharedBase + g % L.block % 4 * 4) % 2 ^ 32) :=
    rfl
  rw [hv] at r500
  have h0 := hl.room
  have h1 : L.sharedBase + g % L.block % 4 * 4 < 2 ^ 32 := by omega
  have h2 : (L.sharedBase + g % L.block % 4 * 4) % 4 = 0 := by
    have := hl.align
    omega
  rw [Nat.mod_eq_of_lt h1] at r500
  refine ldShared_ok (n := 4) (x := BitVec.ofNat 64 (L.sharedBase + g % L.block % 4 * 4)) rfl rfl
    rfl rfl rfl rfl rfl (by decide) (by decide) r500 ?_ (by decide) f
  simp only [BitVec.toNat_ofNat]
  omega

/-- **The arrival at the accumulator barrier is not undefined behaviour.** -/
theorem safe_arrive (hl : SoftLaunch L) (hat : (Data.code e L g).AtD d t)
    (hs : d.c.site = .arrive) (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have r1709 := reg_soft hat (r := 1709)
    (hs ▸ (by decide : 1709 ∈ Control.ctlLive Site.arrive.pc))
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1013)
  have hv : Control.valueOf e L g d.c 1709 =
      b32 ((L.sharedBase + d.c.i % 2 * 8 + 213296) % 2 ^ 32) := rfl
  rw [hv] at r1709
  have h0 := hl.room
  have h1 : L.sharedBase + d.c.i % 2 * 8 + 213296 < 2 ^ 32 := by omega
  have h2 : (L.sharedBase + d.c.i % 2 * 8 + 213296) % 8 = 0 := by
    have := hl.align
    omega
  rw [Nat.mod_eq_of_lt h1] at r1709
  exact arrive_loc_ok (cluster := false) (mbarLoc_b32_ok r1709 h1 h2) (bytes := 0) (n := 1) rfl
    rfl f

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
