-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.SafeA
public import Kernels.InklingRelDecode.Proof.Lib.GlobalLoad
import Lemmas.Flow.MemAl
import Kernels.InklingRelDecode.Flow.Code.Part010
import Kernels.InklingRelDecode.Flow.Code.Part017

@[expose] public section

/-! # The softmax's bias loads are not undefined behaviour

The 64 loads of the first block's bias (pcs `680 + 2 j`) and the 64 of the loop (pcs `1124 + 2 j`)
read 16-bit words through registers that hold the launch's bias row pointer plus an even offset
(`Control.valueOf`). Undefined behaviour could only be a misaligned address, and the pointer is
even when the relative-bias base of the entry is (`Pre.relAlign` through the entry). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG

set_option maxRecDepth 100000

variable {e : Control.Entry} {L : Launch} {g : Nat} {d : Data.D} {t : TState} {ins : Instr}

/-- The code at `pc` is a plain global load into one register. -/
def gloadOne (pc base w : Nat) : Bool :=
  Lib.globalLoad pc base w && match kernel.code[pc]? with
    | some ⟨_, .mem a⟩ => a.regs.length == 1
    | _ => false

/-- **A plain global load into one register through an aligned address is not undefined
behaviour.** -/
theorem safe_gload_s {pc base w n : Nat} (hc : kernel.code[pc]? = some ins)
    (h : gloadOne pc base w = true) (hr : t.regs base = some (b64 n)) (hw : w / 8 ≠ 0)
    (hal : n % (w / 8) = 0) (hd : w / 8 ∣ 2 ^ 64) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  simp only [gloadOne, Bool.and_eq_true] at h
  obtain ⟨hg, h1⟩ := h
  obtain ⟨a, hop, hrl, hl, hb, hk, hs, hnc, hoff, hwd⟩ := Lib.global_load_at hc hg
  rw [hc] at h1
  obtain ⟨gd, op⟩ := ins
  change op = .mem a at hop
  subst hop
  have hlen : a.regs.length = 1 := by simpa using h1
  refine ldGlobal_ok' hrl hl hb hk hs hnc (by rw [hwd]; exact hw) hr ?_ f
  simp only [truncBits, hoff, hlen, hwd, Nat.mul_one, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt]
  simp only [Nat.mod_mod_of_dvd _ (dvd_refl _), Int.zero_emod, Int.toNat_zero, Nat.add_zero]
  rw [Nat.mod_mod_of_dvd _ hd]
  exact hal

theorem biasBase_even {t : Nat} (h : e.rel % 2 = 0) : Control.biasBase e t % 2 = 0 := by
  unfold Control.biasBase
  generalize Lib.sx (e.firstToken + Control.token t) * Lib.sx e.stride = a
  generalize (e.head + Control.headInGroup t) * 1280 % 2 ^ 32 = b
  generalize Lib.sx (1280 + 2 ^ 32 - e.biasOffset) = c
  omega

/-- The register of the `j`-th load of the first block holds the row pointer plus `2 j`. -/
theorem val_pre {j : Nat} (hj : j < 64) :
    Control.valueOf e L g d.c (2141 + j) =
      b64 ((Lib.sx ((e.split + d.c.i * e.splits) * 128) * 2 + Control.biasBase e (g % L.block) +
        2 * j) % 2 ^ 64) := by
  interval_cases j <;> rfl

/-- The register of the `j`-th load of the loop holds the row pointer plus `2 j`. -/
theorem val_nxt {j : Nat} (hj : j < 64) :
    Control.valueOf e L g d.c (2211 + j) =
      b64 ((Lib.sx ((e.splits + (e.split + d.c.i * e.splits)) * 128) * 2 +
        Control.biasBase e (g % L.block) + 2 * j) % 2 ^ 64) := by
  interval_cases j <;> rfl

theorem pre_load : ∀ j : Fin 64, gloadOne (680 + 2 * j.val) (2141 + j.val) 16 = true := by
  decide +kernel

theorem nxt_load : ∀ j : Fin 64, gloadOne (1124 + 2 * j.val) (2211 + j.val) 16 = true := by
  decide +kernel

theorem pre_live : ∀ j : Fin 64, 2141 + j.val ∈ Control.ctlLive (680 + 2 * j.val) := by
  decide +kernel

theorem nxt_live : ∀ j : Fin 64, 2211 + j.val ∈ Control.ctlLive (1124 + 2 * j.val) := by
  decide +kernel

/-- **A bias load of the first block is not undefined behaviour.** -/
theorem safe_pre (hrel : e.rel % 2 = 0) (hat : (Data.code e L g).AtD d t) {j : Fin 64}
    (hs : d.c.site = .pre j) (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hl : 2141 + j.val ∈ Control.ctlLive d.c.site.pc := by
    rw [hs]
    exact pre_live j
  have r := reg_soft hat hl
  rw [val_pre j.isLt] at r
  have hb := biasBase_even (e := e) (t := g % L.block) hrel
  have hpc : d.c.site.pc = 680 + 2 * j.val := by rw [hs]; rfl
  rw [hpc] at hc
  refine safe_gload_s hc (pre_load j) r (by decide) ?_ (by decide) f
  show _ % 2 = 0
  omega

/-- **A bias load of the loop is not undefined behaviour.** -/
theorem safe_nxt (hrel : e.rel % 2 = 0) (hat : (Data.code e L g).AtD d t) {j : Fin 64}
    (hs : d.c.site = .nxt j) (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hl : 2211 + j.val ∈ Control.ctlLive d.c.site.pc := by
    rw [hs]
    exact nxt_live j
  have r := reg_soft hat hl
  rw [val_nxt j.isLt] at r
  have hb := biasBase_even (e := e) (t := g % L.block) hrel
  have hpc : d.c.site.pc = 1124 + 2 * j.val := by rw [hs]; rfl
  rw [hpc] at hc
  refine safe_gload_s hc (nxt_load j) r (by decide) ?_ (by decide) f
  show _ % 2 = 0
  omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
