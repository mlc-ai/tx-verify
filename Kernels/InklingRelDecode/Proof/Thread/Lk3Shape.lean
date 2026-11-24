-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSSync

@[expose] public section

/-!
# Event shapes of the softmax region's butterfly shuffles

`Thread/EvSSync.lean` gives the shape of the broadcast `shfl4` and of the last exchange of the
rescale test `shfl12` (offset 1). This file adds the exchange `shfl11` (offset 2): a full-warp
`shfl.sync.bfly` of the word `ldL` loaded (`D.stg.ld`), with offset 2 and clamp 31. The received
word and the validity are free.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- **A full-warp `shfl.sync.bfly` of register `r` with offset `i` and clamp 31** fires a shuffle
whose operand is the register's value (the instruction of `fires_shfl_bfly1` with another
offset, whose 32-bit pattern is `n`). -/
theorem fires_shfl_bfly {A : List Assumption} {t : TState} {d r : Nat}
    {p : Option Nat} {ty : Option DType} {mask : Opnd} {pc : Nat} {e : Event}
    {o : Option TState} {v : Value} {i : Int} {n : Nat}
    (hi : (truncBits 32 (BitVec.ofInt 64 i)).toNat = n) (hr : t.regs r = some v)
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.shfl .bfly, ty, some d :: (p.map some).toList,
      [.reg r, .imm i, .imm 31], some mask⟩)) e o)
    (hs : Execution.isShfl e = true) : ∃ recv ok, e = ⟨pc, .shfl .bfly v n 31 recv ok⟩ := by
  have h31 : (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 := by decide
  have hp : (p.map some).toList.head?.join = p := by cases p <;> rfl
  simp only [eventTmpl] at hf
  rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := .bfly) (ty := ty) (d := d)
    (ps := (p.map some).toList) (a := .reg r) (b := .imm i) (c := .imm 31) (mask := mask) with
    h | h <;> rw [h] at hf
  swap
  · obtain ⟨epc, ek⟩ := e
    simp_all [Fires, Execution.isShfl]
  rw [hp] at hf
  simp only [shflTmpl, readValue, readReg, hr, readBits] at hf
  repeat' (split at hf)
  all_goals simp_all [Fires, pure, Except.pure, bind, Except.bind, Execution.isShfl]
  all_goals subst_vars
  all_goals aesop

/-- **The exchange of the loaded scratch word**: a full-warp `shfl.sync.bfly` of `D.stg.ld` with
lane offset 2. -/
theorem shape_shfl11 (hF : Fired L g d e (some u)) (hs : d.site = .shfl11) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .bfly d.stg.ld 2 31 recv ok⟩ := by
  have hpc : d.site.pc = 2253 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_shfl_11) hF
  rw [hpc] at hf
  have hr : t.regs 1542 = some d.stg.ld := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_bfly (p := none) (i := 2) (n := 2) (by decide) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

/-- **The exchange of the row maximum**: a full-warp `shfl.sync.bfly` of the thread's own row
maximum (`ownV` of its 64 words, `erealValue .f32 D.ownE` on score words) with lane offset 16. -/
theorem shape_shfl5 (hF : Fired L g d e (some u)) (hs : d.site = .shfl5) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .bfly (ownV fun k => (d.stg.fsv k).1) 16 31 recv ok⟩ := by
  have hpc : d.site.pc = 1838 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_shfl_5) hF
  rw [hpc] at hf
  have hr : t.regs 1520 = some (ownV fun k => (d.stg.fsv k).1) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_bfly (p := none) (i := 16) (n := 16) (by decide) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

/-- **The exchange of the row sum**: a full-warp `shfl.sync.bfly` of the thread's sum of
probabilities (the word `Stg.sw`) with lane offset 16. -/
theorem shape_shfl6 (hF : Fired L g d e (some u)) (hs : d.site = .shfl6) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .bfly d.stg.sw 16 31 recv ok⟩ := by
  have hpc : d.site.pc = 2234 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_shfl_6) hF
  rw [hpc] at hf
  have hr : t.regs 1529 = some d.stg.sw := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_bfly (p := none) (i := 16) (n := 16) (by decide) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
