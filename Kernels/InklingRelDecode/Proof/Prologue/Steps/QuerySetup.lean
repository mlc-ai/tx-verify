-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryPointer
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain
import Lemmas.Flow.Scalars

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
local notation "F" => facts Q L g w d

theorem seg_masks (x : BitVec 64) (hx : subValue d.last d.first = .bits 32 x) :
    Seg kernel Assumptions.all L g 5 79 (F 79) 84 (F 84) := by
  intro t ht
  have val : valueOf Q L g w d 481 = .bits 32 x := hx
  let V := valueOf Q L g w d
  have eq : V = Function.update V 481 (.bits 32 x) := by
    funext r
    by_cases h : r=481
    · subst r; simpa using val
    · simp [h]
  change At t 79 (factsFrom (ctlLive 79) V) at ht
  change ∃ u, run kernel Assumptions.all L g 5 t = some u ∧ At u 84 (factsFrom (ctlLive 84) V)
  rw [eq] at ht ⊢
  have h₀ : g%L.block/8%16 < 60 := by omega
  have h₁ : g%L.block/8%16+16 < 60 := by omega
  have h₂ : g%L.block/8%16+32 < 60 := by omega
  seg_fp ht using
    (simp [V,valueOf,copyReg,registerValue,queryOn,qlen,hx,Lib.word,Value.regBits,
        scmp,r32,truncBits_idem,h₀,h₁,h₂])

private theorem warp {b : Nat} (bound : b<256) :
    PTX.compare .eq .b 32 (r32 (W (b/32))) (i32 0) = decide (b<32) := by
  revert b
  decide +kernel

theorem seg_eligible (bound : g%L.block<256) :
    Seg kernel Assumptions.all L g 1 129 (F 129) 130 (F 130) := by
  intro t ht
  seg_fp ht using exact congrArg Value.pred (warp bound)

theorem query_setup (bound : g%L.block<256) (x) (hx : subValue d.last d.first = .bits 32 x)
    (bit : d.first.regBits.isSome) :
    SegU kernel Assumptions.all L g 79 (F 79) 130 (F 130) :=
  (SegU.of_seg (seg_masks x hx)).comp ((query_chain bit).comp (SegU.of_seg (seg_eligible bound)))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
