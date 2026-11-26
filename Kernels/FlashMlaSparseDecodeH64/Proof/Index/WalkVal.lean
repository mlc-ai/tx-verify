-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.WalkHead
public import Lemmas.Flow.SelpReg
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepIndex

@[expose] public section

/-! # The index warp's stored coordinates and validity bits: the values after the wait

After the wait on the slot (pcs 2449-2463 of the main loop, 2537-2552 of the extra loop) the code
tests the pair's words and positions (`setp`, `and.pred`), `selp`s each coordinate word, the
pair's `mad` or `-1`, on the test, and each validity bit (1 or 2) on the same test; the bits are
`or`ed, shifted to the lane's place in its quad and `cvt`ed to a byte's word: the facts name the two
stored registers (`%r600`, `%r604`; `%r638`, `%r643`) and the two words the shuffles send
(`ixPairs`, `ixQuad`). The evaluation of a `selp` on a symbolic predicate is `Seg.selp_ri` and
`Seg.selp_imm_eq`: the stretch is cut at each `selp` of a tracked word, the predicate being an
explicit fact. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

set_option hygiene false in
/-- A register is not among a list of explicit facts and the table's. -/
macro "ix_hd" : tactic => `(tactic| (
  simp only [List.forall_mem_cons]
  constructorm* _ ∧ _ <;>
    first | (refine not_mem_factsFrom ?_; decide +kernel) | (simp; done)))

/-- The side condition that no assumption has a local rule for the instruction. -/
macro "ix_hL" : term => `(div_hL (by decide) (by decide) (by decide)
  (fun t ht => Assumptions.peerPackRule_of_none (by rw [ht]; rfl)))

/-- `selp.b32 d, a, b, p` of two immediates on a predicate fact. -/
theorem selpIi {pc d p : Nat} {a b : Int} {c : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? =
      some ⟨none, .int ⟨.selp, .int .b 32, false, [some d], [.imm a, .imm b, .reg p]⟩⟩)
    (hp : (p, Value.pred c) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ Assumptions.all,
      as.localRule L g t (.int ⟨.selp, .int .b 32, false, [some d],
        [.imm a, .imm b, .reg p]⟩) = none) :
    SegU kernel Assumptions.all L g pc F (pc + 1) ((d, w32 (sel c (i32 a) (i32 b))) :: F) :=
  SegU.of_seg (Seg.selp_imm_eq hc hp hd (by cases c <;> rfl) hL)

/-- `selp.b32 d, a, b, p` of a register fact and an immediate on a predicate fact. -/
theorem selpRi {pc d a p : Nat} {x : BitVec 64} {b : Int} {c : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? =
      some ⟨none, .int ⟨.selp, .int .b 32, false, [some d], [.reg a, .imm b, .reg p]⟩⟩)
    (ha : (a, Value.bits 32 x) ∈ F) (hp : (p, Value.pred c) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ Assumptions.all,
      as.localRule L g t (.int ⟨.selp, .int .b 32, false, [some d],
        [.reg a, .imm b, .reg p]⟩) = none) :
    SegU kernel Assumptions.all L g pc F (pc + 1) ((d, w32 (sel c x (i32 b))) :: F) :=
  SegU.of_seg (Seg.selp_ri hc ha hp hd hL)

/-- **The main loop's stored coordinates and validity bits** (pcs 2449–2463). -/
theorem ixu_val (c : IxCtl) :
    SegU kernel Assumptions.all L g 2449 (ixFacts P L g c .wA) 2464 (ixFacts P L g c .sA1) := by
  refine SegU.comp (b := 2452) (G := (23, .pred (okM0 c)) ::
    factsFrom (ixLive 2452) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.comp (b := 2453) (G := (598, w32 (sel (okM0 c) (i32 1) (i32 0))) ::
    (23, .pred (okM0 c)) :: factsFrom (ixLive 2452) (ixVal P L g c))
    (selpIi Flow.code_2452 (by simp) (by ix_hd) ix_hL) ?_
  refine SegU.comp (b := 2454) (G := (599, w32 (mad32 (divu32 c.m0 (pw P.page))
    (ixDiv528 (pw P.blockStride))
    (sub32 c.m0 (mul32 (divu32 c.m0 (pw P.page)) (pw P.page))))) ::
    (23, .pred (okM0 c)) :: factsFrom (ixLive 2454) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.comp (b := 2455) (G := (600, w32 (ixCoord c.m0 (pw P.page)
    (ixDiv528 (pw P.blockStride)) (okM0 c))) ::
    (599, w32 (mad32 (divu32 c.m0 (pw P.page)) (ixDiv528 (pw P.blockStride))
    (sub32 c.m0 (mul32 (divu32 c.m0 (pw P.page)) (pw P.page))))) ::
    (23, .pred (okM0 c)) :: factsFrom (ixLive 2454) (ixVal P L g c))
    (selpRi Flow.code_2454 (by simp) (by simp) (by ix_hd) ix_hL) ?_
  refine SegU.comp (b := 2458) (G := (26, .pred (okM1 c)) ::
    factsFrom (ixLive 2458) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.comp (b := 2459) (G := (601, w32 (sel (okM1 c) (i32 2) (i32 0))) ::
    (26, .pred (okM1 c)) :: factsFrom (ixLive 2458) (ixVal P L g c))
    (selpIi Flow.code_2458 (by simp) (by ix_hd) ix_hL) ?_
  refine SegU.comp (b := 2461) (G := (603, w32 (mad32 (divu32 c.m1 (pw P.page))
    (ixDiv528 (pw P.blockStride))
    (sub32 c.m1 (mul32 (divu32 c.m1 (pw P.page)) (pw P.page))))) ::
    (26, .pred (okM1 c)) :: factsFrom (ixLive 2461) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.comp (b := 2462) (G := (604, w32 (ixCoord c.m1 (pw P.page)
    (ixDiv528 (pw P.blockStride)) (okM1 c))) ::
    (603, w32 (mad32 (divu32 c.m1 (pw P.page)) (ixDiv528 (pw P.blockStride))
    (sub32 c.m1 (mul32 (divu32 c.m1 (pw P.page)) (pw P.page))))) ::
    (26, .pred (okM1 c)) :: factsFrom (ixLive 2461) (ixVal P L g c))
    (selpRi Flow.code_2461 (by simp) (by simp) (by ix_hd) ix_hL) ?_
  ix_seg

/-- **The extra loop's stored coordinates and validity bits** (pcs 2537–2552). -/
theorem ixu_xval (c : IxCtl) :
    SegU kernel Assumptions.all L g 2537 (ixFacts P L g c .wB) 2553 (ixFacts P L g c .sB1) := by
  refine SegU.comp (b := 2540) (G := (38, .pred (okE0 c)) ::
    factsFrom (ixLive 2540) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.comp (b := 2541) (G := (636, w32 (sel (okE0 c) (i32 1) (i32 0))) ::
    (38, .pred (okE0 c)) :: factsFrom (ixLive 2540) (ixVal P L g c))
    (selpIi Flow.code_2540 (by simp) (by ix_hd) ix_hL) ?_
  refine SegU.comp (b := 2542) (G := (637, w32 (mad32 (divu32 c.e0 (pw P.extraPage))
    (ixDiv528 (pw P.extraBlockStride))
    (sub32 c.e0 (mul32 (divu32 c.e0 (pw P.extraPage)) (pw P.extraPage))))) ::
    (38, .pred (okE0 c)) :: factsFrom (ixLive 2542) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.comp (b := 2543) (G := (638, w32 (ixCoord c.e0 (pw P.extraPage)
    (ixDiv528 (pw P.extraBlockStride)) (okE0 c))) ::
    (637, w32 (mad32 (divu32 c.e0 (pw P.extraPage)) (ixDiv528 (pw P.extraBlockStride))
    (sub32 c.e0 (mul32 (divu32 c.e0 (pw P.extraPage)) (pw P.extraPage))))) ::
    (38, .pred (okE0 c)) :: factsFrom (ixLive 2542) (ixVal P L g c))
    (selpRi Flow.code_2542 (by simp) (by simp) (by ix_hd) ix_hL) ?_
  refine SegU.comp (b := 2547) (G := (41, .pred (okE1 c)) ::
    factsFrom (ixLive 2547) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.comp (b := 2548) (G := (640, w32 (sel (okE1 c) (i32 2) (i32 0))) ::
    (41, .pred (okE1 c)) :: factsFrom (ixLive 2547) (ixVal P L g c))
    (selpIi Flow.code_2547 (by simp) (by ix_hd) ix_hL) ?_
  refine SegU.comp (b := 2550) (G := (642, w32 (mad32 (divu32 c.e1 (pw P.extraPage))
    (ixDiv528 (pw P.extraBlockStride))
    (sub32 c.e1 (mul32 (divu32 c.e1 (pw P.extraPage)) (pw P.extraPage))))) ::
    (41, .pred (okE1 c)) :: factsFrom (ixLive 2550) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.comp (b := 2551) (G := (643, w32 (ixCoord c.e1 (pw P.extraPage)
    (ixDiv528 (pw P.extraBlockStride)) (okE1 c))) ::
    (642, w32 (mad32 (divu32 c.e1 (pw P.extraPage)) (ixDiv528 (pw P.extraBlockStride))
    (sub32 c.e1 (mul32 (divu32 c.e1 (pw P.extraPage)) (pw P.extraPage))))) ::
    (41, .pred (okE1 c)) :: factsFrom (ixLive 2550) (ixVal P L g c))
    (selpRi Flow.code_2550 (by simp) (by simp) (by ix_hd) ix_hL) ?_
  ix_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
