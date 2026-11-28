-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.RawArith
public import Kernels.InklingRelDecode.Proof.Loader.Inputs
public import Kernels.InklingRelDecode.Proof.Loader.StepsHead
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases
import Lemmas.Flow.Bits

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {rest : Nat → Value} (i n a b : Value)

/-- Build the initial ring cursors from the loaded counter and the split stride. -/
theorem index_span :
    let V := entryValue Q L g w rest i n a b
    SegU kernel Assumptions.all L g 2360 (factsFrom (Flow.live 2360) V) 2365
      (loopFacts (L := L) (g := g) (w := w) (regs := inputs Q L g rest) i n a b 2365) := by
  intro V
  have shift (k : Int) : shl (bits i) k = shl (i.regBits.getD 0) k := by
    simp only [shl, bits, r32, truncBits_idem]
  have s0 := Lib.shiftLive (L := L) (g := g) (rs := Flow.live 2360) (rs' := Flow.live 2361)
    V Flow.code_2360 (by decide) (by decide) (congrArg (Value.bits 32) (shift 3)) (by decide)
  have s1 := Lib.shiftLive (L := L) (g := g) (rs := Flow.live 2361) (rs' := Flow.live 2362)
    V Flow.code_2361 (by decide) (by decide) (congrArg (Value.bits 32) (shift 15)) (by decide)
  have s2 : SegU kernel Assumptions.all L g 2362 (factsFrom (Flow.live 2362) V) 2363
      (factsFrom (Flow.live 2363) V) := by
    apply Lib.madStep Flow.code_2362 (by decide) (mem_factsFrom (by decide))
      (mem_factsFrom (by decide)) (mem_factsFrom (by decide))
    have hv : V 577 = .bits 32 (truncBits 32
        (Lib.word (V 532) * Lib.word (V 1905) + Lib.word (V 468))) := by
      change Value.bits 32 (mad32 _ (bits i) _) = Value.bits 32 (truncBits 32
        (r32 (BitVec.ofNat 64 (Q.splits % 2 ^ 32)) * bits i +
          r32 (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .x)))))
      simp only [mad32, bits, r32, truncBits_idem]
    rw [← hv]
    exact fun _ hR => Lib.writeLive (by decide) hR
  apply s0.comp (s1.comp (s2.comp ?_))
  apply SegU.of_seg (n := 2)
  intro t ht
  dsimp only [V, loopFacts] at ht ⊢
  have hlane : compare .eq .b 32 (r32 (andi (BitVec.ofNat 64 (g % L.block)) 31)) (i32 0) =
      decide (laneOf L g = 0) := by
    unfold PTX.compare laneOf
    rw [decide_eq_decide]
    nf_simp [r32, andi, i32]
    omega
  seg_fp ht using (first | rfl | exact congrArg Value.pred hlane)

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
