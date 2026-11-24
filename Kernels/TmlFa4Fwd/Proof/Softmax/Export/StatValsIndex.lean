-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Row
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Lag

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Flow

private theorem factor_table (b pl : Bool) :
    (ptsOf b .sst).countP (before (.stat pl)) = 0 ∧
    (ptsOf b (.acquire 80)).countP (before (.stat pl)) = 2 ∧
    (ptsOf b .sst).countP inBias = 1 ∧ (ptsOf b .sst).countP inPlain = 1 ∧
    (ptsOf b (.acquire 80)).countP inBias = 1 ∧ (ptsOf b (.acquire 80)).countP inPlain = 1 := by
  cases b <;> cases pl <;> decide +kernel

theorem factor_ordinal {p L g d c rb rp pl} (hQ : RefQ p L g d c rb rp)
    (hs : d.site = .stat pl) : c (.acquire 80) = c .sst + 2 := by
  obtain ⟨a,b,f,h,i,j⟩ := factor_table (lz L g) pl
  rw [hQ.cnt _ rfl, hQ.cnt _ rfl, hs]
  simp only [passed,a,b,f,h,i,j,Nat.mul_one]
  omega

private theorem final_table (b : Bool) (j : Fin 2) :
    (ptsOf b .sst).countP (before (.fin j)) = j.val ∧
    (ptsOf b .sst).countP inBias = 1 ∧ (ptsOf b .sst).countP inPlain = 1 := by
  cases b <;> fin_cases j <;> decide +kernel

theorem final_ordinal {p L g d c rb rp ns nv j} (hQ : RefQ p L g d c rb rp)
    (hF : SmWarp.SFits p L g d ns nv) (hs : d.site = .fin j) :
    c .sst = Values.softRounds p L g - 1 + j.val ∧ 0 < Values.softRounds p L g := by
  obtain ⟨ha,hb,hc⟩ := final_table (lz L g) j
  have hcnt := hQ.cnt .sst rfl
  rw [hs] at hcnt
  simp only [passed,ha,hb,hc,Nat.mul_one] at hcnt
  have hfin := hQ.fin (by rw [hs]; fin_cases j <;> decide)
  obtain ⟨hf,hu⟩ := hF
  have ep : SmWarp.epi d.site = .ready 0 := by rw [hs]; rfl
  simp only [Epilogue.Fits, SmWarp.toE, ep] at hf
  obtain ⟨R,bal,hC,h0,h1⟩ := hf
  obtain ⟨bEq,pEq⟩ := nBP hC h0 h1 (hu (by rw [hs]; rfl))
  have toNat {r : Nat} {z : Int} (hd : Done r z) : z.toNat = r := by
    rcases hd with h | ⟨rfl,h⟩ <;> omega
  have hr : SoftRounds p L g (1+rb+rp) := ⟨R,bal,hC.1,by
    rw [← bEq, ← pEq, toNat hfin.1, toNat hfin.2]⟩
  have hex : ∃ N, SoftRounds p L g N := ⟨_,hr⟩
  simp only [Values.softRounds, dite_eq_left hex, hex.choose_spec.unique hr]
  omega

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
