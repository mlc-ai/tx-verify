-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Flow.Code
import Lemmas.Flow.TcStWord
import Lemmas.Flow.TcStValsAny

@[expose] public section

/-! # The words of the rescale store at its site

At the site of the rescale store (pc 2328) the 64 words it stores are the registers `1612 + i`, the
product of the rescale factor with the word `i` of the accumulator load, as the value state holds
them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {L : Launch} {g : Nat} {ent : Control.Entry}

theorem rs2_reg (V : Nat → Value) {i : Nat} (hi : i < 64) :
    (1612 + i, okVal (.bits 32 0) (mulE false (V 507) (V (1547 + i)))) ∈ Gen.rs_facts2 V := by
  have h : (Gen.rs_facts2 V)[4 + i]? =
      some (1612 + i, okVal (.bits 32 0) (mulE false (V 507) (V (1547 + i)))) := by
    interval_cases i <;> rfl
  exact List.mem_of_getElem? h

theorem st_ops : ∃ ss sh, kernel.code[2328]? = some ⟨some (171, false), .tcSt 1611 ss sh⟩ ∧
    ss.length = 64 ∧ (∀ i < 64, ss[i]? = some (.reg (1612 + i))) ∧ ∀ s, sh ≠ .packed16 s :=
  ⟨_, _, Flow.code_tmemStore_1, rfl, fun i hi => by interval_cases i <;> rfl, fun _ h => nomatch h⟩


/-- **The words of the rescale store at its site** are the rescale factor times the words of the
accumulator load. -/
theorem rs_site_words {a : Nat} {vals : List Value} {sh : TcShape} {y : Data.D} {t : TState}
    {ins : Instr} {o : Option TState} (ht : (Data.codeS ent L g).AtD y t)
    (hc : kernel.code[y.c.site.pc]? = some ins)
    (fire : Fires y.c.site.pc (eventTmpl Assumptions.all L g t ins.op)
      ⟨2328, .tc (.st a vals sh)⟩ o) (site : y.c.site = .stO) :
    vals.length = 64 ∧ ∀ i < 64, vals[i]? = some (okVal (.bits 32 0)
      (mulE false (alphaWord (scaleW L) y.v.m y.v.mx) (y.v.ov.getD i (b32 0)))) := by
  have ht := atS_code ht
  have h7 : y.c.site.pc = 2328 := by rw [site]; rfl
  rw [h7] at hc fire
  obtain ⟨ss, sh0, hcode, hsl, hss, hsh⟩ := st_ops
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  refine ⟨(Flow.fires_tcSt_valsAny hsh fire rfl).1.trans hsl, fun i hi => ?_⟩
  have reg : t.regs (1612 + i) = some (okVal (.bits 32 0) (mulE false (rsV L y.v 507)
      (rsV L y.v (1547 + i)))) := by
    have mem : (1612 + i, okVal (.bits 32 0) (mulE false (rsV L y.v 507)
        (rsV L y.v (1547 + i)))) ∈ dFS L y.c.site y.v := by
      rw [site]
      exact rs2_reg _ hi
    exact holds_mem (atD_dF ht) mem
  have := Flow.fires_tcSt_word hsh fire rfl (hss i hi) reg
  have e507 : rsV L y.v 507 = alphaWord (scaleW L) y.v.m y.v.mx := by simp [rsV, alphaWord]
  have eov : rsV L y.v (1547 + i) = y.v.ov.getD i (b32 0) := by
    simp [rsV, show 1547 ≤ 1547 + i by omega, show 1547 + i < 1611 by omega]
  rw [e507, eov] at this
  exact this

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
