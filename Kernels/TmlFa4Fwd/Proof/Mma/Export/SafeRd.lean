-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Kernels.TmlFa4Fwd.Flow.Code.Part033
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
import Kernels.TmlFa4Fwd.Proof.Lib.LoadAl
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's request reads are no undefined behaviour under its reference values

A global word read faults only when misaligned (`fires_load_reg_al`). Under `MFits` the request's
reads address the chosen request's cuQ words (`cuQBase + 4 i`, `+ 4 (i + 1)`) and its used-K word
(`usedKBase + 4 i`), all 4-aligned (`Pre.alignment`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

set_option maxHeartbeats 4000000 in
/-- **No request read of the MMA warp under its reference values is undefined behaviour.** -/
theorem read_safe (hp : Pre p L m) {d : D} {ns nv : Nat} (hF : MFits p L g d ns nv) {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (h : (code p L g ent).AtD d t)
    (hc : kernel.code[(code p L g ent).pc d]? = some ins)
    (hf : Fires ((code p L g ent).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk) (f : Fault) : e.kind ≠ .ub f := by
  replace h : At t d.site.pc (facts p L g ent d) := h
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  have hb := Epilogue.batch_lt hp
  obtain ⟨-, -, -, -, -, -, -, -, hcq, huk, -⟩ := hp.alignment
  have hroom : p.usedKBase + 4 * p.batch ≤ 2 ^ 64 :=
    hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  have hFE := efits hF (by rcases hs with h | h | h <;> rw [h] <;> rfl)
  obtain ⟨R, bal, hC⟩ : ∃ R bal, Epilogue.ChosenVals p L g R bal (toE d) (ns - 1 - d.v.ps) nv := by
    rcases hs with h | h | h <;> simp only [Epilogue.Fits, toE, h, Site.epi] at hFE
    · exact hFE
    · obtain ⟨R, bal, h, -⟩ := hFE; exact ⟨R, bal, h⟩
    · obtain ⟨R, bal, h, -⟩ := hFE; exact ⟨R, bal, h⟩
  obtain ⟨i, hi, hib⟩ := Epilogue.chosen_W hp hC
  have hci : chosen d.v.sc = W i := by simpa only [toE] using hi
  obtain ⟨site, v⟩ := d
  intro hk
  rcases hs with rfl | rfl | rfl
  · site_code
    change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [2538] 7881 0) e o at hf
    have := fires_load_reg_al h.2.1 (reg_bits h (by lit_mem) rfl) hf hk
    simp only at hci
    apply this
    have ha := Epilogue.addrS_toNat0 hp (show i ≤ p.batch by omega)
    simp only [Epilogue.vbits] at ha
    dsimp only
    rw [hci, ha]
    omega
  · site_code
    change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [2539] 7881 4) e o at hf
    have := fires_load_reg_al h.2.1 (reg_bits h (by lit_mem) rfl) hf hk
    simp only at hci
    apply this
    have ha := Epilogue.addrS_toNat4 hp hib
    simp only [Epilogue.vbits] at ha
    dsimp only
    rw [hci, ha]
    omega
  · site_code
    change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [2541] 7882 0) e o at hf
    have := fires_load_reg_al h.2.1 (reg_bits h (by lit_mem) rfl) hf hk
    simp only at hci
    apply this
    have ha := addrK_toNat hp hroom (show i < p.batch by omega)
    simp only [Epilogue.vbits] at ha
    dsimp only
    rw [hci, ha]
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
