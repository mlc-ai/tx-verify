-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.StepsInc
public import Kernels.InklingRelDecode.Proof.Loader.Cursors
public import Kernels.InklingRelDecode.Proof.Loader.StepsHead
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {rest : Nat → Value} (i n a b : Value)

def nextCounter (i : Value) : Value := .bits 32 (r32 (bits i + 1))

/-- Preserve the raw result of pointer arithmetic until the comparison checks it. -/
def replaceCounter (val : Nat → Value) (v : Value) (r : Nat) :=
  ([(1905, v)].lookup r).getD (val r)

theorem counter_span (V : Nat → Value) (hi : V 1905 = i) :
    SegU kernel Assumptions.all L g 2413 (factsFrom (Flow.live 2413) V) 2414
      (factsFrom (Flow.live 2414) (replaceCounter V (incValue i))) := by
  apply inc_span (hi ▸ mem_factsFrom (val := V) (show 1905 ∈ Flow.live 2413 by decide))
  intro R hR
  apply holds_of_pointwise
  intro r hr
  by_cases h : r = 1905
  · subst r
    exact Function.update_self ..
  · rw [Function.update_of_ne h]
    have hl : ∀ x ∈ Flow.live 2414, x ∈ Flow.live 2413 := by decide
    simpa [replaceCounter, List.lookup, beq_eq_false_iff_ne.mpr h] using
      holds_mem hR (mem_factsFrom (hl r hr))

private def cursorTable (base : Nat → Value) (v2 v3 v4 st : BitVec 64) (r : Nat) :=
  ([(1902, Value.bits 32 v2), (1903, .bits 32 v3), (1904, .bits 32 v4),
    (466, .bits 32 st)].lookup r).getD (base r)

private theorem moveCursors (base : Nat → Value) (v2 v3 v4 st : BitVec 64) :
    Seg kernel Assumptions.all L g 3 2414 (factsFrom (Flow.live 2414)
        (cursorTable base v2 v3 v4 st)) 2417 (factsFrom (Flow.live 2417)
          (cursorTable base (add32 v2 st) (addi v3 32768) (addi v4 8) st)) := by
  intro u hu
  seg_fp hu using rfl

set_option linter.unusedTactic false in
set_option maxRecDepth 2048 in
/-- Advance the byte, tile and slab cursors. The last increment adds the split stride
that the worker inherited from startup. -/
theorem cursors_span :
    let V := loopValue L g w (inputs Q L g rest) ⟨.poll,i,n,a,b⟩
    let N := loopValue L g w (inputs Q L g rest) ⟨.poll,nextCounter i,n,a,b⟩
    Seg kernel Assumptions.all L g 3 2414
      (factsFrom (Flow.live 2414) (replaceCounter V (incValue i)))
      2417 (factsFrom (Flow.live 2417) (replaceCounter N (incValue i))) := by
  intro V N t ht
  let val := replaceCounter N (incValue i)
  let x := bits i
  have hb : bits (nextCounter i) = r32 (x + 1) := truncBits_idem ..
  have byte : val 1904 = .bits 32 (shl (bits (nextCounter i)) ((3 : Nat) : Int)) := rfl
  have tile : val 1903 = .bits 32 (shl (bits (nextCounter i)) ((15 : Nat) : Int)) := rfl
  let stride := r32 (BitVec.ofNat 64 (Q.splits % 2 ^ 32))
  let c := r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .x))
  have slab : val 1902 = .bits 32 (shl (mad32 stride (bits (nextCounter i)) c) 7) := rfl
  rw [hb, ← shift_succ x 3 (by decide)] at byte
  rw [hb, ← shift_succ x 15 (by decide)] at tile
  rw [hb, ← slab_succ] at slab
  have strideShift : shl stride 7 = shl (BitVec.ofNat 64 (Q.splits % 2 ^ 32)) 7 := by
    simp only [shl, stride, r32, truncBits_idem]
  rw [strideShift] at slab
  dsimp only [V] at ht
  dsimp only [val, N] at byte tile slab
  dsimp only [N]
  let rs := [3,20,462,463,464,465,466,467,470,528,529,530,531,532,534,583,586,588,590,
    1902,1903,1904,1905,1949,1950,2020]
  rw [show Flow.live 2414 = rs by decide +kernel] at ht
  rw [show Flow.live 2417 = rs by decide +kernel]
  dsimp only [rs] at ht
  let v2 := shl (mad32 stride x c) 7
  let v3 := shl x 15
  let v4 := shl x 3
  let st := shl (BitVec.ofNat 64 (Q.splits % 2 ^ 32)) 7
  have seg := moveCursors (L := L) (g := g) (replaceCounter V (incValue i)) v2 v3 v4 st
  rw [show Flow.live 2414 = rs by decide +kernel, show Flow.live 2417 = rs by decide +kernel] at seg
  refine seg.weaken_end ?_ t ?_
  · intro R hR
    apply holds_of_pointwise
    intro r hr
    have h := holds_mem hR (mem_factsFrom hr)
    dsimp only [rs] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | (rw [byte]; exact h) | (rw [tile]; exact h) | (rw [slab]; exact h) | exact h
  · exact ht

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
