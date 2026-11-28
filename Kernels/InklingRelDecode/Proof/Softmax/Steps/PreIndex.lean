-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.LoopRoute
import Kernels.InklingRelDecode.Gen.StepSoftmax
import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Kernels.InklingRelDecode.Gen.StepSoftmax01
import Lemmas.Flow.FloatRun
import Lemmas.Flow.SegJump
import Lemmas.Flow.SignedBits
import Lemmas.Flow.BranchU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Carry}
local notation "F" => facts e L g (D.mk (Softmax.Site.bar0) 0 v)
local macro "idx_close" ht:ident : tactic => `(tactic| (
  simp only [valueOf,scalarValue,u32,u16,u64,Nat.reduceEqDiff,↓reduceIte]
  all_goals first
    | rfl
    | (generalize eqt : _ % Launch.block _ = tid at $ht ⊢
       clear eqt
       revert tid
       decide +kernel)
    | (norm_bits [row,token,headInGroup]; done)
    | (norm_cmp [row,token,validRow]; done)))

private theorem index_576 (hT : g % L.block < 256) :
    SegU kernel Assumptions.all L g 576 (F 575) 580 (F 580) := by
  apply SegU.of_seg (n := 4)
  intro t ht
  seg_fp ht using idx_close hT

private theorem index_580 (hT : g % L.block < 256) :
    SegU kernel Assumptions.all L g 580 (F 580) 584 (F 584) := by
  apply SegU.of_seg (n := 4)
  intro t ht
  seg_fp ht using idx_close hT

theorem cmp_gt_signed (a b : Nat) (ha : a < 2^32) (hb : b < 2^31) :
    PTX.compare .gt .s 32 (truncBits 32 (BitVec.ofNat 64 a))
      (truncBits 32 (BitVec.ofNat 64 b)) = decide (b < a ∧ a < 2^31) := by
  simp only [PTX.compare,toSigned32_ofNat,Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2^32 by omega),hb,↓reduceIte,decide_eq_decide]
  split <;> omega

private theorem index_584 (hT : g % L.block < 256) (ok : e.Ok) :
    SegU kernel Assumptions.all L g 584 (F 584) 587 (F 587) := by
  have tok : token (g % L.block) < 2^31 := by unfold token row; omega
  have s : Seg kernel Assumptions.all L g 1 584 (F 584) 585 (F 585) := by
    intro t ht
    seg_fp ht using idx_close hT
  have t : Seg kernel Assumptions.all L g 1 585 (F 585) 586 (F 586) := by
    intro t ht
    seg_fp ht using exact congrArg Value.pred (cmp_gt_signed _ _ ok.query tok)
  apply (SegU.of_seg (s.comp t)).comp
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using simp [valueOf,scalarValue,validRow]

private theorem index_587 (hT : g % L.block < 256) :
    SegU kernel Assumptions.all L g 587 (F 587) 589 (F 589) := by
  apply SegU.of_seg (n := 2)
  intro t ht
  seg_fp ht using idx_close hT

private theorem index_589 :
    SegU kernel Assumptions.all L g 589 (F 589) 593 (F 593) := by
  ink_ctl

private theorem index_593 (hT : g % L.block < 256) :
    SegU kernel Assumptions.all L g 593 (F 593) 598 (F 598) := by
  have first : Seg kernel Assumptions.all L g 4 593 (F 593) 597 (F 597) := by
    intro t ht
    seg_fp ht using idx_close hT
  apply (SegU.of_seg first).comp
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using norm_bits [valueOf,scalarValue,u32]

private theorem index_598 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 598 (F 598) 599 (F 599) := by
  have small : token (g%L.block) < 2^31 := by unfold token row; omega
  apply Lib.sum_span (dst := 803) (r := 610) (δ := token (g%L.block)) (op := .reg 496)
    false small Flow.code_598 (by decide) (by decide)
  · change u32 (e.firstToken + token _) = Lib.addBase e.firstWord _
    have bits := ok.firstBits
    unfold Entry.firstToken
    cases h : e.firstWord <;> simp_all [Lib.addBase,u32]
    change false = true at bits
    contradiction
  · intro t ht
    exact Lib.delta_reg ht (by decide : 496 ∈ ctlLive 598) rfl (by omega)
  · decide +kernel

theorem pre_index (hT : g % L.block < 256) (ok : e.Ok) :
    SegU kernel Assumptions.all L g 576 (F 575) 599 (F 599) := by
  apply (index_576 hT).comp
  apply (index_580 hT).comp
  apply (index_584 hT ok).comp
  apply (index_587 hT).comp
  apply (index_589).comp
  apply (index_593 hT).comp
  exact index_598 ok

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
