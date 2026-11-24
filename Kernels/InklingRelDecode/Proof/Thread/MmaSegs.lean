-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.MmaBase
public import Kernels.InklingRelDecode.Proof.Thread.RawWord

@[expose] public section

/-! # The local code between the MMA warp's events

The straight-line pieces of the loop's control code (`pc 2425` to `2461`, `2447` to `2454`,
`2500` to `2509`), each from the facts of its first pc to the facts of its last, valued by the
table of the loop state. Their hypotheses are the shape facts of the launch (`Env`). The
composite segments of the end of an iteration (`seg_iter`), of the first half of an iteration
(`seg_afterQk`) and of the start of the loop (`seg_start`) follow in `MmaSegsLoop`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The shape facts the loop's local code needs: the shared window is inside the 18-bit shared
address space, `num_iters` is below `2 ^ 31 - 1`, the iteration is below `2 ^ 31` and the Tensor
Memory base has room for 512 columns; `%r10` holds a word the code reads as `num_iters`. -/
structure Env (L : Launch) (d : D) : Prop where
  sb : L.sharedBase + 213340 ≤ 2 ^ 18
  n : d.n ≤ 2147483646
  i : d.i < 2 ^ 31
  tm : d.tm + 512 < 2 ^ 32
  wd : Raw.word32Of (d.pro 471) = some d.n

variable {L : Launch} {g : Nat} {d : D}

/-- `%r10` is the role's `pro 471`. -/
theorem valueOf_471 (d : D) : valueOf L d 471 = d.pro 471 := by
  simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_none]

/-- The register `%r10` of a state of the facts at `pc`. -/
theorem reg_471 {pc : Nat} {t : TState} (h : At t pc (factsAt L pc d)) (hl : 471 ∈ Flow.live pc) :
    t.regs 471 = some (d.pro 471) :=
  valueOf_471 (L := L) d ▸ holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- `setp.gt.u32 %p6, num_iters, 2147483646`: the loaded word read as bits. -/
theorem s_p6 (hw : Raw.word32Of (d.pro 471) = some d.n) :
    SegE L g 2425 (factsAt L 2425 d) 2426 (factsAt L 2426 d) := by
  have hn := Raw.word32Of_lt hw
  refine ⟨1, Raw.seg_int1 (d := 6) (v := .pred (decide (2147483646 < d.n))) Flow.code_2425 rfl
    rfl (Raw.asms_segFree (by decide +kernel)) (fun t h => ?_) (fun R hR => ?_)⟩
  · have hb := Raw.readBits_word32 (L := L) (g := g) (reg_471 h (by table_decide)) hw
    simp only [execInt, hb, DType.width, bind, Except.bind, pure, Except.pure]
    simp only [readBits, PTX.compare, DType.kind?, truncBits, pure, Except.pure,
      BitVec.toNat_ofNat, BitVec.toNat_ofInt, Option.getD_some]
    congr 4
    simp only [decide_eq_decide]
    omega
  · exact Raw.holds_set_live hR (by ink_values) (by table_decide)

/-- `add.s32 %r11, %r10, 1`: the loaded word read as bits, plus one. -/
theorem s_r11 (hd : Env L d) :
    SegE L g 2442 (factsAt L 2442 d) 2443 (factsAt L 2443 d) := by
  obtain ⟨hsr, hn, -, htm, hw⟩ := hd
  refine ⟨1, Raw.seg_int1 (d := 472) (v := b32 (d.n + 1)) Flow.code_2442 rfl
    rfl (Raw.asms_segFree (by decide +kernel)) (fun t h => ?_) (fun R hR => ?_)⟩
  · rw [Raw.execInt_add_imm (reg_471 h (by table_decide)) hw]
    congr 3
    simp only [b32]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
    omega
  · exact Raw.holds_set_live hR (by ink_values) (by table_decide)

/-- The setup of the loop (`pc 2427` to `2446`), at iteration 0. -/
theorem s_init (hd : Env L d) (hi : d.i = 0) :
    SegE L g 2427 (factsAt L 2427 d) 2455 (factsAt L 2455 d) := by
  have h2 := s_r11 (g := g) hd
  obtain ⟨hsr, hn, -, htm, -⟩ := hd
  have h1 : SegE L g 2427 (factsAt L 2427 d) 2442 (factsAt L 2442 d) :=
    ⟨15, fun t h => by ink_seg h⟩
  have h3 : SegE L g 2443 (factsAt L 2443 d) 2455 (factsAt L 2455 d) :=
    ⟨4, fun t h => by ink_seg h⟩
  exact (h1.comp h2).comp h3

/-- `setp.ge.s32 %p7, i, num_iters`: the loaded word read as bits. -/
theorem s_p7 (hd : Env L d) :
    SegE L g 2455 (factsAt L 2455 d) 2456 (factsAt L 2456 d) := by
  obtain ⟨hsr, hn, hi, htm, hw⟩ := hd
  refine ⟨1, Raw.seg_int1 (d := 7) (v := .pred (decide (d.n ≤ d.i))) Flow.code_2455 rfl
    rfl (Raw.asms_segFree (by decide +kernel)) (fun t h => ?_) (fun R hR => ?_)⟩
  · have hb := Raw.readBits_word32 (L := L) (g := g) (reg_471 h (by table_decide)) hw
    have h1911 : t.regs 1911 = some (b32 d.i) := by
      have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L d)
        (show 1911 ∈ Flow.live 2455 by table_decide))
      simpa [valueOf, values, PTX.Flow.lookupLit] using this
    simp only [execInt, hb, DType.width, bind, Except.bind, pure, Except.pure]
    simp only [readBits, readReg, h1911, b32, PTX.compare, DType.kind?, truncBits, toSigned,
      pure, Except.pure, bind, Except.bind, BitVec.toNat_ofNat, Option.getD_some]
    congr 4
    simp only [decide_eq_decide]
    split_ifs <;> omega
  · exact Raw.holds_set_live hR (by ink_values) (by table_decide)

/-- The ring slot, parity and barrier address of the QK half (`pc 2457` to `2460`). -/
theorem s_top (hd : Env L d) :
    SegE L g 2457 (factsAt L 2457 d) 2461 (factsAt L 2461 d) := by
  obtain ⟨hsr, hn, hi, htm, -⟩ := hd
  exact ⟨4, fun t h => by ink_seg h⟩

/-- `setp.eq.b32 %p12, i, 0`. -/
theorem s_p12 (hd : Env L d) :
    SegE L g 2500 (factsAt L 2500 d) 2501 (factsAt L 2501 d) := by
  obtain ⟨hsr, hn, hi, htm, -⟩ := hd
  exact ⟨1, fun t h => by ink_seg h⟩

/-- The parity and barrier address of the PV half (`pc 2502` to `2508`), in iteration
`i ≥ 1`. -/
theorem s_pvtail (hd : Env L d) (hi1 : 1 ≤ d.i) :
    SegE L g 2502 (factsAt L 2502 d) 2509 (factsAt L 2509 d) := by
  obtain ⟨hsr, hn, hi, htm, -⟩ := hd
  exact ⟨7, fun t h => by ink_seg h⟩

/-- The loop's increments (`pc 2447` to `2453`) and the loop test `%p17`: the facts of the next
iteration. -/
theorem s_incr (hd : Env L d) (hin : d.i ≤ d.n) :
    SegE L g 2447 (factsAt L 2447 d) 2454 (factsAt L 2454 { d with i := d.i + 1 }) := by
  obtain ⟨hsr, hn, hi, htm, -⟩ := hd
  exact ⟨7, fun t h => by ink_seg h⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
