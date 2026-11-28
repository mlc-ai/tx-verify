-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Shuffle
import Kernels.InklingRelDecode.Gen.StepSoftmax37
import Lemmas.Flow.BranchU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}
local notation "F" => facts e L g (D.mk Softmax.Site.shfl6 i v)

private theorem first_test (hi : i < 2^31) :
    SegU kernel Assumptions.all L g 2235 (F 2234) 2237 ((169,.pred (decide (i=0)))::(F 2234)) := by
  seg_ctl Lib.rulesFrame, Lib.hooks_ok using seg_close []

private theorem parity : SegU kernel Assumptions.all L g 2238 (F 2234)
    2239 (facts e L g ⟨.waitO,i,v⟩ 2239) := by
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using
    simp only [valueOf,scalarValue]
    have cases' : i%2 = 0 ∨ i%2 = 1 := by omega
    rcases cases' with h | h
    · rw [h,show (i+1)%2 = 1 by omega]; rfl
    · rw [h,show (i+1)%2 = 0 by omega]; rfl

theorem step_shfl6 : (code e L g).StepAtU ⟨.shfl6,i,v⟩ := by
  apply step_of_inv
  intro hi
  have lt := hi.iter_lt (by decide : SiteBody .shfl6)
  have eq := hi.entry.limitEq
  have small : i < 2^31 := by split at eq <;> omega
  let z : Site := if i=0 then .bar20 else .waitO
  apply shuffle_data (s := .shfl6) (z := z) Flow.code_shfl_6 (fun _ => rfl)
    (by dsimp [z]; split <;> decide) (by decide +kernel)
  apply (first_test small).comp
  apply (SegU.branch (decide (i=0)) Flow.code_2237 Lib.bra_rule (segFree (by decide))).comp
  by_cases h : i = 0
  · simp only [h,decide_true,↓reduceIte,z]
    apply SegU.of_havoc Lib.rulesFrame Lib.hooks_ok (by decide) (by decide +kernel)
    · change Havoc.check Lib.hooks ((facts e L g ⟨.bar20,0,v⟩ 999).map Prod.fst) 949 999 _ = true
      rw [facts,factsFrom_keys]
      decide +kernel
    · exact project (p := 2234) (q := 999) (by decide +kernel)
  · simp only [z,h,decide_false,Bool.false_eq_true,↓reduceIte]
    exact parity (e := e) (L := L) (g := g) (i := i) (v := v)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
