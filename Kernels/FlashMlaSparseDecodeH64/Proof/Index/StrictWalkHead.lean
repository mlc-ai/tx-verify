-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.WalkVal
public import Lemmas.Flow.SegQDiv
public import Lemmas.Flow.SelpReg
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepIndex

@[expose] public section

/-! # The strict walks through the divisions and the stored coordinates

The strict counterparts (`SegQ (QT ixQt)`) of `ixu_head`, `ixu_xhead` (`Index/WalkHead.lean`) and
`ixu_val`, `ixu_xval` (`Index/WalkVal.lean`): the divisors' nonzero tags are those of `ixQt`
(`%r497`, `%r502`), so a division is `SegQ.div_u32`; the `selp` of a stored word is `Seg.selp_ri`
as an exact piece that touches no tagged register. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- The side conditions of a strict piece at `pc`. -/
def QSide (pc : Nat) : Prop :=
  (pc ∉ paramAdds ∧ pc ∉ prefetchTensorMapSites ∧ pc ∉ Assumptions.sharedBitsSites) ∧
    Assumptions.peerPack pc = none ∧ pc + 1 ≤ 2600 ∧ 2332 ≤ pc ∧
    frameB ((kernel.code.drop pc).take 1) ((ixQt (pc + 1)).map Prod.fst) = true ∧
    tagsIn (ixQt (pc + 1)) (ixQt pc) = true ∧ pc + 1 ≤ kernel.code.length

set_option hygiene false in
/-- Discharge `QSide pc` for a numeral `pc`. -/
macro "qk_side" : tactic => `(tactic| (
  refine ⟨⟨by decide, by decide, by decide⟩, rfl, by decide, by decide, by decide +kernel,
    by decide +kernel, by decide +kernel⟩))

/-- A division of the head: the strict piece, from its facts' dividend and divisor. -/
theorem qk_div (hP : Plain L g) {pc d a r : Nat} {x y : BitVec 64} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? =
      some ⟨none, .int ⟨.div, .int .u 32, false, [some d], [.reg a, .reg r]⟩⟩)
    (ha : (a, Value.bits 32 x) ∈ F) (hr : (r, Value.bits 32 y) ∈ F)
    (hnz : (ixQt pc).lookup r = some (Tag.nz 32)) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hpc : pc ∉ paramAdds ∧ pc ∉ prefetchTensorMapSites ∧ pc ∉ Assumptions.sharedBitsSites)
    (hpk : Assumptions.peerPack pc = none)
    (hl1 : pc + 1 ≤ 2600) (hl2 : 2332 ≤ pc)
    (hB : frameB ((kernel.code.drop pc).take 1) ((ixQt (pc + 1)).map Prod.fst) = true)
    (hq : tagsIn (ixQt (pc + 1)) (ixQt pc) = true)
    (hlen : pc + 1 ≤ kernel.code.length) :
    SegQ kernel Assumptions.all L g (QT ixQt) pc F (pc + 1) ((d, .bits 32 (divu32 x y)) :: F) :=
  SegQ.div_u32 rulesFrame hc ha hr hnz hd
    (div_hL hpc.1 hpc.2.1 hpc.2.2
      (fun t ht => Assumptions.peerPackRule_of_none (by rw [ht]; exact hpk)))
    noSegments.segFreePc hlen (hP.segs.mono hl2 hl1) hB hq

/-- A `selp` of a stored word: the strict piece (it touches no tagged register). -/
theorem qk_selp (hP : Plain L g) {pc d a p : Nat} {x : BitVec 64} {b : Int} {c : Bool}
    {F : List (Nat × Value)}
    (hc : kernel.code[pc]? =
      some ⟨none, .int ⟨.selp, .int .b 32, false, [some d], [.reg a, .imm b, .reg p]⟩⟩)
    (ha : (a, Value.bits 32 x) ∈ F) (hp : (p, Value.pred c) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hs : QSide pc) :
    SegQ kernel Assumptions.all L g (QT ixQt) pc F (pc + 1)
      ((d, .bits 32 (sel c x (i32 b))) :: F) := by
  obtain ⟨hpc, hpk, hl1, hl2, hB, hq, hlen⟩ := hs
  exact SegQ.of_seg_frame rulesFrame (Seg.selp_ri hc ha hp hd
    (div_hL hpc.1 hpc.2.1 hpc.2.2
      (fun t ht => Assumptions.peerPackRule_of_none (by rw [ht]; exact hpk)))
    noSegments.segFreePc) (by omega) hlen (Nat.le_succ pc) (hP.segs.mono hl2 hl1) hB hq

/-- A `selp` of two immediates on a predicate fact: the strict piece (it writes a register the
tags do not name). -/
theorem qk_selpIi (hP : Plain L g) {pc d p : Nat} {a b : Int} {c : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? =
      some ⟨none, .int ⟨.selp, .int .b 32, false, [some d], [.imm a, .imm b, .reg p]⟩⟩)
    (hp : (p, Value.pred c) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hs : QSide pc) :
    SegQ kernel Assumptions.all L g (QT ixQt) pc F (pc + 1)
      ((d, w32 (sel c (i32 a) (i32 b))) :: F) := by
  obtain ⟨hpc, hpk, hl1, hl2, hB, hq, hlen⟩ := hs
  exact SegQ.of_seg_frame rulesFrame (Seg.selp_imm_eq hc hp hd (by cases c <;> rfl)
    (div_hL hpc.1 hpc.2.1 hpc.2.2
      (fun t ht => Assumptions.peerPackRule_of_none (by rw [ht]; exact hpk)))
    noSegments.segFreePc) (by omega) hlen (Nat.le_succ pc) (hP.segs.mono hl2 hl1) hB hq

/-- **The main loop's block head** (pcs 2432–2445), strictly. -/
theorem qk_head (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2432 (factsFrom (ixLive 2432) (ixVal P L g c)) 2446
      (factsFrom (ixLive 2446) (ixVal P L g c)) := by
  refine SegQ.comp (b := 2433) (G := (589, w32 (divu32 c.m0 (pw P.page))) ::
    factsFrom (ixLive 2432) (ixVal P L g c))
    (qk_div hP (a := 2974) (r := 497) Flow.code_2432 (mem_factsFrom_eq (by decide +kernel) rfl)
      (mem_factsFrom_eq (by decide +kernel) rfl) (by decide +kernel)
      (not_mem_factsFrom (by decide +kernel)) ⟨by decide, by decide, by decide⟩ rfl (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ?_
  refine SegQ.comp (b := 2435) (G := factsFrom (ixLive 2435) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2436) (G := (592, w32 (divu32 c.m1 (pw P.page))) ::
    factsFrom (ixLive 2435) (ixVal P L g c))
    (qk_div hP (a := 2973) (r := 497) Flow.code_2435 (mem_factsFrom_eq (by decide +kernel) rfl)
      (mem_factsFrom_eq (by decide +kernel) rfl) (by decide +kernel)
      (not_mem_factsFrom (by decide +kernel)) ⟨by decide, by decide, by decide⟩ rfl (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ?_
  ixq_seg

/-- **The extra loop's block head** (pcs 2520–2533), strictly. -/
theorem qk_xhead (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2520 (factsFrom (ixLive 2520) (ixVal P L g c)) 2534
      (factsFrom (ixLive 2534) (ixVal P L g c)) := by
  refine SegQ.comp (b := 2521) (G := (627, w32 (divu32 c.e0 (pw P.extraPage))) ::
    factsFrom (ixLive 2520) (ixVal P L g c))
    (qk_div hP (a := 2982) (r := 502) Flow.code_2520 (mem_factsFrom_eq (by decide +kernel) rfl)
      (mem_factsFrom_eq (by decide +kernel) rfl) (by decide +kernel)
      (not_mem_factsFrom (by decide +kernel)) ⟨by decide, by decide, by decide⟩ rfl (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ?_
  refine SegQ.comp (b := 2523) (G := factsFrom (ixLive 2523) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2524) (G := (630, w32 (divu32 c.e1 (pw P.extraPage))) ::
    factsFrom (ixLive 2523) (ixVal P L g c))
    (qk_div hP (a := 2981) (r := 502) Flow.code_2523 (mem_factsFrom_eq (by decide +kernel) rfl)
      (mem_factsFrom_eq (by decide +kernel) rfl) (by decide +kernel)
      (not_mem_factsFrom (by decide +kernel)) ⟨by decide, by decide, by decide⟩ rfl (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) ?_
  ixq_seg

/-- **The main loop's stored coordinates and validity bits** (pcs 2449–2463), strictly. -/
theorem qk_val (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2449 (ixFacts P L g c .wA) 2464
      (ixFacts P L g c .sA1) := by
  refine SegQ.comp (b := 2452) (G := (23, .pred (okM0 c)) ::
    factsFrom (ixLive 2452) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2453) (G := (598, w32 (sel (okM0 c) (i32 1) (i32 0))) ::
    (23, .pred (okM0 c)) :: factsFrom (ixLive 2452) (ixVal P L g c))
    (qk_selpIi hP Flow.code_2452 (by simp) (by ix_hd) (by qk_side)) ?_
  refine SegQ.comp (b := 2454) (G := (599, w32 (mad32 (divu32 c.m0 (pw P.page))
    (ixDiv528 (pw P.blockStride))
    (sub32 c.m0 (mul32 (divu32 c.m0 (pw P.page)) (pw P.page))))) ::
    (23, .pred (okM0 c)) :: factsFrom (ixLive 2454) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2455) (G := (600, w32 (ixCoord c.m0 (pw P.page)
    (ixDiv528 (pw P.blockStride)) (okM0 c))) ::
    (599, w32 (mad32 (divu32 c.m0 (pw P.page)) (ixDiv528 (pw P.blockStride))
    (sub32 c.m0 (mul32 (divu32 c.m0 (pw P.page)) (pw P.page))))) ::
    (23, .pred (okM0 c)) :: factsFrom (ixLive 2454) (ixVal P L g c))
    (qk_selp hP (b := -1) Flow.code_2454 (by simp) (by simp) (by ix_hd) (by qk_side)) ?_
  refine SegQ.comp (b := 2458) (G := (26, .pred (okM1 c)) ::
    factsFrom (ixLive 2458) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2459) (G := (601, w32 (sel (okM1 c) (i32 2) (i32 0))) ::
    (26, .pred (okM1 c)) :: factsFrom (ixLive 2458) (ixVal P L g c))
    (qk_selpIi hP Flow.code_2458 (by simp) (by ix_hd) (by qk_side)) ?_
  refine SegQ.comp (b := 2461) (G := (603, w32 (mad32 (divu32 c.m1 (pw P.page))
    (ixDiv528 (pw P.blockStride))
    (sub32 c.m1 (mul32 (divu32 c.m1 (pw P.page)) (pw P.page))))) ::
    (26, .pred (okM1 c)) :: factsFrom (ixLive 2461) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2462) (G := (604, w32 (ixCoord c.m1 (pw P.page)
    (ixDiv528 (pw P.blockStride)) (okM1 c))) ::
    (603, w32 (mad32 (divu32 c.m1 (pw P.page)) (ixDiv528 (pw P.blockStride))
    (sub32 c.m1 (mul32 (divu32 c.m1 (pw P.page)) (pw P.page))))) ::
    (26, .pred (okM1 c)) :: factsFrom (ixLive 2461) (ixVal P L g c))
    (qk_selp hP (b := -1) Flow.code_2461 (by simp) (by simp) (by ix_hd) (by qk_side)) ?_
  ixq_seg

/-- **The extra loop's stored coordinates and validity bits** (pcs 2537–2552), strictly. -/
theorem qk_xval (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2537 (ixFacts P L g c .wB) 2553
      (ixFacts P L g c .sB1) := by
  refine SegQ.comp (b := 2540) (G := (38, .pred (okE0 c)) ::
    factsFrom (ixLive 2540) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2541) (G := (636, w32 (sel (okE0 c) (i32 1) (i32 0))) ::
    (38, .pred (okE0 c)) :: factsFrom (ixLive 2540) (ixVal P L g c))
    (qk_selpIi hP Flow.code_2540 (by simp) (by ix_hd) (by qk_side)) ?_
  refine SegQ.comp (b := 2542) (G := (637, w32 (mad32 (divu32 c.e0 (pw P.extraPage))
    (ixDiv528 (pw P.extraBlockStride))
    (sub32 c.e0 (mul32 (divu32 c.e0 (pw P.extraPage)) (pw P.extraPage))))) ::
    (38, .pred (okE0 c)) :: factsFrom (ixLive 2542) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2543) (G := (638, w32 (ixCoord c.e0 (pw P.extraPage)
    (ixDiv528 (pw P.extraBlockStride)) (okE0 c))) ::
    (637, w32 (mad32 (divu32 c.e0 (pw P.extraPage)) (ixDiv528 (pw P.extraBlockStride))
    (sub32 c.e0 (mul32 (divu32 c.e0 (pw P.extraPage)) (pw P.extraPage))))) ::
    (38, .pred (okE0 c)) :: factsFrom (ixLive 2542) (ixVal P L g c))
    (qk_selp hP (b := -1) Flow.code_2542 (by simp) (by simp) (by ix_hd) (by qk_side)) ?_
  refine SegQ.comp (b := 2547) (G := (41, .pred (okE1 c)) ::
    factsFrom (ixLive 2547) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2548) (G := (640, w32 (sel (okE1 c) (i32 2) (i32 0))) ::
    (41, .pred (okE1 c)) :: factsFrom (ixLive 2547) (ixVal P L g c))
    (qk_selpIi hP Flow.code_2547 (by simp) (by ix_hd) (by qk_side)) ?_
  refine SegQ.comp (b := 2550) (G := (642, w32 (mad32 (divu32 c.e1 (pw P.extraPage))
    (ixDiv528 (pw P.extraBlockStride))
    (sub32 c.e1 (mul32 (divu32 c.e1 (pw P.extraPage)) (pw P.extraPage))))) ::
    (41, .pred (okE1 c)) :: factsFrom (ixLive 2550) (ixVal P L g c)) (by ixq_seg) ?_
  refine SegQ.comp (b := 2551) (G := (643, w32 (ixCoord c.e1 (pw P.extraPage)
    (ixDiv528 (pw P.extraBlockStride)) (okE1 c))) ::
    (642, w32 (mad32 (divu32 c.e1 (pw P.extraPage)) (ixDiv528 (pw P.extraBlockStride))
    (sub32 c.e1 (mul32 (divu32 c.e1 (pw P.extraPage)) (pw P.extraPage))))) ::
    (41, .pred (okE1 c)) :: factsFrom (ixLive 2550) (ixVal P L g c))
    (qk_selp hP (b := -1) Flow.code_2550 (by simp) (by simp) (by ix_hd) (by qk_side)) ?_
  ixq_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
