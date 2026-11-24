-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiPm

@[expose] public section

/-! # The local code between the epilogue's stores

The straight-line code of the epilogue that no event separates: the row index and the `LsePart`
word (pcs 2674-2681), the addresses of the `OPart` words (pcs 2683-2749), and the unpack of each
product pair into the two words of the stores that follow it (`mov.b64 {lo, hi}, pair`, one per
pair, pc `2750 + 3 q`). Each piece is a segment from the facts of its first pc to the facts of
its last, valued by the state's table. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-! ### The unpack of a product pair -/

/-- Every product pair splits into two four-byte words. -/
theorem prod_split (d : D) (q : Nat) :
    (d.prod q).bytes = 8 ∧ (splitValue 64 (d.prod q)).1.bytes = 4 ∧
      (splitValue 64 (d.prod q)).2.bytes = 4 := by
  unfold D.prod
  split_ifs
  · simp [b32, joinValue, splitValue, Value.bytes, truncBits]
  · obtain ⟨x, y, h, hx, hy⟩ := mulOut_pair d.pr.cpair
      (joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0)))
    rw [h]
    simp [Value.bytes, hx, hy, splitValue]

/-- `mov.b64 {lo, hi}, a` of a register that holds an eight-byte value whose halves have four
bytes writes the halves, at a state where no assumption takes a segment. -/
theorem exec_unpack_gen {t : TState} (hM : CoreMoves asms) (hS : Assumption.SegFreePc asms t.pc)
    {lo hi a : Nat} {v : Value} (h : t.regs a = some v) (hv : v.bytes = 8)
    (h1 : (splitValue 64 v).1.bytes = 4) (h2 : (splitValue 64 v).2.bytes = 4) :
    execLocalA asms L g t (.move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩) =
      .ok (PTX.next (setReg (setReg t lo (splitValue 64 v).1) hi (splitValue 64 v).2)) := by
  rw [(hS.at rfl).exec, execLocalRule_of_none (hM _ L g t)]
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, h, hv,
    h1, h2, bind, Except.bind, pure, Except.pure]

theorem unpack_codeB : ∀ q < 32, unpackCodeB kernel (2750 + 3 * q)
    [(2479 + q, 1832 + 2 * q, 1833 + 2 * q)] = true := by
  decide +kernel

theorem unpack_code (q : Nat) (hq : q < 32) : kernel.code[2750 + 3 * q]? = some ⟨none, .move
    ⟨.unpack, .int .b 64, [some (1832 + 2 * q), some (1833 + 2 * q)], [.reg (2479 + q)]⟩⟩ :=
  (UnpackCode.of_bool (unpack_codeB q hq)).1

/-- **The unpack of product pair `q`** writes its two halves. -/
theorem seg_unpack (d : D) {q : Nat} (hq : q < 32) {F : List (Nat × Value)}
    (hsrc : (2479 + q, d.prod q) ∈ F) (hk1 : ∀ p ∈ F, p.1 ≠ 1832 + 2 * q)
    (hk2 : ∀ p ∈ F, p.1 ≠ 1833 + 2 * q) :
    Seg kernel asms L g 1 (2750 + 3 * q) F (2751 + 3 * q)
      ((1833 + 2 * q, (splitValue 64 (d.prod q)).2) ::
        (1832 + 2 * q, (splitValue 64 (d.prod q)).1) :: F) := by
  intro t h
  have hsrc' : t.regs (2479 + q) = some (d.prod q) := holds_mem h.2.2.2.2 hsrc
  obtain ⟨hb, h1, h2⟩ := prod_split d q
  have hpc : 2560 ≤ t.pc := by rw [h.1]; omega
  have hex := exec_unpack_gen (L := L) (g := g) asms_moves (segFree hpc) hsrc' hb h1 h2
    (lo := 1832 + 2 * q) (hi := 1833 + 2 * q)
  have hc : kernel.code[t.pc]? = some ⟨none, .move
      ⟨.unpack, .int .b 64, [some (1832 + 2 * q), some (1833 + 2 * q)], [.reg (2479 + q)]⟩⟩ := by
    rw [h.1]; exact unpack_code q hq
  refine ⟨PTX.next (setReg (setReg t (1832 + 2 * q) (splitValue 64 (d.prod q)).1)
    (1833 + 2 * q) (splitValue 64 (d.prod q)).2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [run, tauStep, tau_of_ok hc rfl h.2.2.2.1 hex, Option.bind_some]
  · simp [PTX.next, setReg, h.1]; omega
  · simpa [PTX.next, setReg] using h.2.1
  · simpa [PTX.next, setReg] using h.2.2.1
  · simpa [PTX.next, setReg] using h.2.2.2.1
  · have hR := h.2.2.2.2
    refine ⟨?_, ?_, ?_⟩
    · simp [PTX.next, setReg]
    · simp [PTX.next, setReg]
    · have := holds_update (holds_update hR (r := 1832 + 2 * q) (x := some (splitValue 64
        (d.prod q)).1) hk1) (r := 1833 + 2 * q) (x := some (splitValue 64 (d.prod q)).2)
        (fun p hp => hk2 p hp)
      exact this

/-- The registers live after an unpack are its two destinations or were live before it. -/
theorem unpack_live_end : ∀ q < 32, ∀ r ∈ Flow.live (2751 + 3 * q),
    r = 1832 + 2 * q ∨ r = 1833 + 2 * q ∨ r ∈ Flow.live (2750 + 3 * q) := by
  decide +kernel

theorem unpack_live_keys : ∀ q < 32, 1832 + 2 * q ∉ Flow.live (2750 + 3 * q) ∧
    1833 + 2 * q ∉ Flow.live (2750 + 3 * q) ∧ 2479 + q ∈ Flow.live (2750 + 3 * q) := by
  decide +kernel

theorem word_even (d : D) (q : Nat) : d.word (2 * q) = (splitValue 64 (d.prod q)).1 := by
  simp [D.word, Nat.mul_mod_right]

theorem word_odd (d : D) (q : Nat) : d.word (2 * q + 1) = (splitValue 64 (d.prod q)).2 := by
  have h1 : (2 * q + 1) % 2 = 1 := by omega
  have h2 : (2 * q + 1) / 2 = q := by omega
  simp [D.word, h1, h2]

/-- **The unpack of product pair `q`**, between the facts of the table. -/
theorem seg_unpack_facts (d : D) {q : Nat} (hq : q < 32) :
    SegE L g (2750 + 3 * q) (factsAt (2750 + 3 * q) d) (2751 + 3 * q)
      (factsAt (2751 + 3 * q) d) := by
  obtain ⟨hk1, hk2, hs⟩ := unpack_live_keys q hq
  have hsrc : (2479 + q, d.prod q) ∈ factsAt (2750 + 3 * q) d := by
    have := Flow.mem_factsFrom (val := valueOf d) hs
    rwa [valueOf_prod d hq] at this
  refine ⟨1, (seg_unpack d hq hsrc (facts_ne hk1) (facts_ne hk2)).weaken_end fun R hR => ?_⟩
  refine Flow.holds_of_pointwise fun r hr => ?_
  rcases unpack_live_end q hq r hr with rfl | rfl | hl
  · rw [show 1832 + 2 * q = 1832 + (2 * q) from rfl, valueOf_word d (by omega), word_even]
    exact hR.2.1
  · rw [show 1833 + 2 * q = 1832 + (2 * q + 1) by omega, valueOf_word d (by omega), word_odd]
    exact (show 1832 + (2 * q + 1) = 1833 + 2 * q by omega) ▸ hR.1
  · exact reg_of hR.2.2 hl

/-! ### The addresses of the `OPart` words (pcs 2683-2749) -/

theorem seg_addr_2683 (d : D) (hok : d.pr.Ok) :
    SegE L g 2683 (factsAt 2682 d) 2687 (factsAt 2687 d) := by
  have hr := hok.row
  simp only [Prm.row, Prm.r1898, Prm.r1897, M32] at hr
  refine ⟨4, fun t h => ?_⟩
  epi_segs h [Prm.row, Prm.oAddr, Prm.r1897, Prm.r1898,
    Nat.mod_eq_of_lt hok.a, Nat.mod_eq_of_lt hok.b, Nat.mod_eq_of_lt hok.c,
    Nat.mod_eq_of_lt hok.dd, Nat.mod_eq_of_lt hok.e, Nat.mod_eq_of_lt hok.lb,
    Nat.mod_eq_of_lt hok.ob, Nat.mod_eq_of_lt hok.d0, M32, M64]

theorem seg_addr_2687 (d : D) (hok : d.pr.Ok) :
    SegE L g 2687 (factsAt 2687 d) 2703 (factsAt 2703 d) := by
  have hr := hok.row
  simp only [Prm.row, Prm.r1898, Prm.r1897, M32] at hr
  refine ⟨16, fun t h => ?_⟩
  epi_segs h [Prm.row, Prm.oAddr, Prm.r1897, Prm.r1898,
    Nat.mod_eq_of_lt hok.a, Nat.mod_eq_of_lt hok.b, Nat.mod_eq_of_lt hok.c,
    Nat.mod_eq_of_lt hok.dd, Nat.mod_eq_of_lt hok.e, Nat.mod_eq_of_lt hok.lb,
    Nat.mod_eq_of_lt hok.ob, Nat.mod_eq_of_lt hok.d0, M32, M64]

theorem seg_addr_2703 (d : D) (hok : d.pr.Ok) :
    SegE L g 2703 (factsAt 2703 d) 2719 (factsAt 2719 d) := by
  have hr := hok.row
  simp only [Prm.row, Prm.r1898, Prm.r1897, M32] at hr
  refine ⟨16, fun t h => ?_⟩
  epi_segs h [Prm.row, Prm.oAddr, Prm.r1897, Prm.r1898,
    Nat.mod_eq_of_lt hok.a, Nat.mod_eq_of_lt hok.b, Nat.mod_eq_of_lt hok.c,
    Nat.mod_eq_of_lt hok.dd, Nat.mod_eq_of_lt hok.e, Nat.mod_eq_of_lt hok.lb,
    Nat.mod_eq_of_lt hok.ob, Nat.mod_eq_of_lt hok.d0, M32, M64]

theorem seg_addr_2719 (d : D) (hok : d.pr.Ok) :
    SegE L g 2719 (factsAt 2719 d) 2735 (factsAt 2735 d) := by
  have hr := hok.row
  simp only [Prm.row, Prm.r1898, Prm.r1897, M32] at hr
  refine ⟨16, fun t h => ?_⟩
  epi_segs h [Prm.row, Prm.oAddr, Prm.r1897, Prm.r1898,
    Nat.mod_eq_of_lt hok.a, Nat.mod_eq_of_lt hok.b, Nat.mod_eq_of_lt hok.c,
    Nat.mod_eq_of_lt hok.dd, Nat.mod_eq_of_lt hok.e, Nat.mod_eq_of_lt hok.lb,
    Nat.mod_eq_of_lt hok.ob, Nat.mod_eq_of_lt hok.d0, M32, M64]

theorem seg_addr_2735 (d : D) (hok : d.pr.Ok) :
    SegE L g 2735 (factsAt 2735 d) 2750 (factsAt 2750 d) := by
  have hr := hok.row
  simp only [Prm.row, Prm.r1898, Prm.r1897, M32] at hr
  refine ⟨15, fun t h => ?_⟩
  epi_segs h [Prm.row, Prm.oAddr, Prm.r1897, Prm.r1898,
    Nat.mod_eq_of_lt hok.a, Nat.mod_eq_of_lt hok.b, Nat.mod_eq_of_lt hok.c,
    Nat.mod_eq_of_lt hok.dd, Nat.mod_eq_of_lt hok.e, Nat.mod_eq_of_lt hok.lb,
    Nat.mod_eq_of_lt hok.ob, Nat.mod_eq_of_lt hok.d0, M32, M64]

/-- **The addresses of the `OPart` words and the unpack of the first pair**: from the state
after the `LsePart` store to the first `OPart` store. -/
theorem seg_addr (d : D) (hok : d.pr.Ok) :
    SegE L g 2683 (factsAt 2682 d) 2751 (factsAt 2751 d) :=
  (((((seg_addr_2683 d hok).comp (seg_addr_2687 d hok)).comp (seg_addr_2703 d hok)).comp
    (seg_addr_2719 d hok)).comp (seg_addr_2735 d hok)).comp (seg_unpack_facts d (q := 0) (by omega))

/-! ### The row index and the `LsePart` word (pcs 2674-2681) -/

theorem seg_w4a (d : D) (hok : d.pr.Ok) :
    SegE L g 2674 (factsAt 2674 d) 2680 (factsAt 2680 d) := by
  have hr := hok.row
  simp only [Prm.row, Prm.r1898, Prm.r1897, M32] at hr
  refine ⟨6, fun t h => ?_⟩
  epi_segs h [Prm.row, Prm.lAddr, Prm.lead, Prm.lseWord, Prm.r1897, Prm.r1898,
    Nat.mod_eq_of_lt hok.a, Nat.mod_eq_of_lt hok.b, Nat.mod_eq_of_lt hok.c,
    Nat.mod_eq_of_lt hok.dd, Nat.mod_eq_of_lt hok.e, Nat.mod_eq_of_lt hok.lb, M32, M64]

/-- `selp.b32 %r1832, -inf, lse, %p178`. -/
theorem seg_selp_core {F : List (Nat × Value)} (d : D) (hl : d.pr.lse.bytes = 4)
    (h525 : (524, d.pr.lse) ∈ F) (h179 : (178, Value.pred d.pr.eq0) ∈ F)
    (hk : ∀ q ∈ F, q.1 ≠ 1831) :
    Seg kernel asms L g 1 2680 F 2681 ((1831, d.pr.lseWord) :: F) := by
  intro t h
  have h525' : t.regs 524 = some d.pr.lse := holds_mem h.2.2.2.2 h525
  have h179' : t.regs 178 = some (.pred d.pr.eq0) := holds_mem h.2.2.2.2 h179
  have hex : execLocalA asms L g t (.int ⟨.selp, .int .b 32, false, [some 1831],
      [.imm (-8388608), .reg 524, .reg 178]⟩) = .ok (PTX.next (setReg t 1831 d.pr.lseWord)) := by
    rw [(segFree (pc := t.pc) (by rw [h.1]; omega)).exec rfl,
      execLocalRule_of_none (asms_none (by simp) (by simp))]
    cases hc : d.pr.eq0
    · simp [execLocal_selp (i := ⟨.selp, .int .b 32, false, [some 1831],
        [.imm (-8388608), .reg 524, .reg 178]⟩) rfl, execMove, DType.width, readReg, h179',
        h525', readValue, hl, Prm.lseWord, hc, bind, Except.bind, pure, Except.pure]
    · simp [execLocal_selp (i := ⟨.selp, .int .b 32, false, [some 1831],
        [.imm (-8388608), .reg 524, .reg 178]⟩) rfl, execMove, DType.width, readReg, h179',
        readBits, readValue, Value.bytes, Prm.lseWord, hc, bind, Except.bind, pure, Except.pure,
        b32]
      rfl
  have hc : kernel.code[t.pc]? = some ⟨none, .int ⟨.selp, .int .b 32, false, [some 1831],
      [.imm (-8388608), .reg 524, .reg 178]⟩⟩ := by rw [h.1]; exact Flow.code_2680
  have := At.set (r := 1831) (v := d.pr.lseWord) h hk
  refine ⟨PTX.next (setReg t 1831 d.pr.lseWord), ?_, this⟩
  simp only [run, tauStep, tau_of_ok hc rfl h.2.2.2.1 hex, Option.bind_some]

theorem selp_live : ∀ r ∈ Flow.live 2681, r = 1831 ∨ r ∈ Flow.live 2680 := by decide +kernel

theorem selp_keys : 524 ∈ Flow.live 2680 ∧ 178 ∈ Flow.live 2680 ∧ 1831 ∉ Flow.live 2680 := by
  decide +kernel

theorem seg_w4b (d : D) (hok : d.pr.Ok) :
    SegE L g 2680 (factsAt 2680 d) 2681 (factsAt 2681 d) := by
  obtain ⟨h525, h179, h1832⟩ := selp_keys
  refine ⟨1, (seg_selp_core d hok.lse (Flow.mem_factsFrom (val := valueOf d) h525)
    (Flow.mem_factsFrom (val := valueOf d) h179) (facts_ne h1832)).weaken_end fun R hR => ?_⟩
  refine Flow.holds_of_pointwise fun r hr => ?_
  rcases selp_live r hr with rfl | hl
  · exact hR.1
  · exact reg_of hR.2 hl

theorem seg_w4c (d : D) :
    SegE L g 2681 (factsAt 2681 d) 2682 (factsAt 2682 d) := by
  refine ⟨1, fun t h => ?_⟩
  epi_seg h

/-- **The row index, the addresses of `LsePart` and the `LsePart` word**: from pc 2674 to the
store at pc 2682. -/
theorem seg_w4 (d : D) (hok : d.pr.Ok) :
    SegE L g 2674 (factsAt 2674 d) 2682 (factsAt 2682 d) :=
  ((seg_w4a d hok).comp (seg_w4b d hok)).comp (seg_w4c d)

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
