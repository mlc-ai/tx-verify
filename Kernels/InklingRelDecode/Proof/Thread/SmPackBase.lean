-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmLoads

@[expose] public section

/-! # Tools for packing the bias words and the key positions (pcs 816-942)

After the last preload (pc 806) the softmax region packs the 64 loaded half-words into 32
registers (`mov.b32 %r, {%rs, %rs}`, pcs 816-847) and builds 31 pairs of key positions
(`add.s32 %r, %r349, -c` twice, then `mov.b64 %rd, {%r, %r}`, pcs 850-942). `seg_fp` evaluates
neither kind of `mov`: it cannot compute `joinValue` of two symbolic values. These two kinds are
proved here as one-instruction pieces from two local execution lemmas (`exec_pack`, the packing
of two values of half the width, and `exec_addImm`), and the pieces are chained by induction on
the index. The register table gives every operand its value by one lookup at a symbolic
register (`valueOf_packed`, `valueOf_pair`, `valueOf_sum`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-! ### Two local execution lemmas -/

/-- `add.s32 d, a, -c` of a 32-bit word, for `0 < c ≤ 2 ^ 32`. -/
theorem exec_addImm {t : TState} {d a c x : Nat} (hS : Assumption.SegFreePc asms t.pc)
    (hc0 : 0 < c) (hc : c ≤ 2 ^ 32) (ha : t.regs a = some (b32 x)) :
    execLocalA asms L g t (Op.int ⟨IntOp.add, DType.int IType.s 32, false, [some d],
        [Opnd.reg a, Opnd.imm (-(c : Int))]⟩) =
      .ok (PTX.next (setReg t d (b32 ((x + 2 ^ 32 - c) % 2 ^ 32)))) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  simp [execLocal, Op.rule, IntInstr.rule, execInt, DType.width, readValue, readReg, readBits, ha,
    b32, bind, Except.bind, pure, Except.pure]
  congr 3
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_add]
  have h : (-(c : Int) % ((2 ^ 64 : Nat) : Int)).toNat = 2 ^ 64 - c := by omega
  rw [h]
  omega

/-- `mov.b32/64 d, {a, b}` of two values of half the width. -/
theorem exec_pack {t : TState} {d a b w : Nat} {x y : Value}
    (hS : Assumption.SegFreePc asms t.pc) (hw : w = 32 ∨ w = 64)
    (ha : t.regs a = some x) (hb : t.regs b = some y)
    (hx : x.bytes = w / 16) (hy : y.bytes = w / 16) :
    execLocalA asms L g t (.move ⟨.pack, .int .b w, [some d], [.reg a, .reg b]⟩) =
      .ok (PTX.next (setReg t d (joinValue x y))) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  rcases hw with rfl | rfl <;>
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, ha, hb, hx,
    hy, bind, Except.bind, pure, Except.pure]

/-! ### One-instruction pieces -/

/-- `mov.b32/64 dst, {a, b}` as a piece between the table's facts. -/
theorem seg_pack1 {pc dst a b w : Nat} {d : D} {x y : Value}
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.pack, .int .b w, [some dst], [.reg a, .reg b]⟩⟩)
    (hw : w = 32 ∨ w = 64) (hno : Assumptions.emuSites.contains pc = false)
    (hx : valueOf L g d a = x) (hy : valueOf L g d b = y)
    (hxb : x.bytes = w / 16) (hyb : y.bytes = w / 16)
    (hla : a ∈ Flow.live pc) (hlb : b ∈ Flow.live pc)
    (hv : valueOf L g d dst = joinValue x y)
    (hlive : ∀ r ∈ Flow.live (pc + 1), r = dst ∨ r ∈ Flow.live pc) :
    Seg kernel asms L g 1 pc (factsAt L g pc d) (pc + 1) (factsAt L g (pc + 1) d) := by
  refine seg_one hc rfl (fun t h => ?_) hv hlive
  have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree hno
  have ha := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) hla)
  have hb := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) hlb)
  rw [hx] at ha
  rw [hy] at hb
  exact exec_pack hS hw ha hb hxb hyb

/-- `add.s32 dst, a, -c` as a piece between the table's facts. -/
theorem seg_addImm1 {pc dst a c x : Nat} {d : D}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
      [.reg a, .imm (-(c : Int))]⟩⟩)
    (hc0 : 0 < c) (hc1 : c ≤ 2 ^ 32) (hno : Assumptions.emuSites.contains pc = false)
    (hx : valueOf L g d a = b32 x) (hla : a ∈ Flow.live pc)
    (hv : valueOf L g d dst = b32 ((x + 2 ^ 32 - c) % 2 ^ 32))
    (hlive : ∀ r ∈ Flow.live (pc + 1), r = dst ∨ r ∈ Flow.live pc) :
    Seg kernel asms L g 1 pc (factsAt L g pc d) (pc + 1) (factsAt L g (pc + 1) d) := by
  refine seg_one hc rfl (fun t h => ?_) hv hlive
  have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree hno
  have ha := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) hla)
  rw [hx] at ha
  exact exec_addImm hS hc0 hc1 ha

/-- An unconditional branch (`bra.uni`) as a piece. -/
theorem seg_goto {pc target : Nat} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .bra target true⟩)
    (hno : Assumptions.emuSites.contains pc = false) :
    Seg kernel asms L g 1 pc F target F := by
  intro t h
  have hS : Assumption.SegFreePc asms pc := segFree hno
  refine ⟨{ t with pc := target }, ?_, rfl, h.2⟩
  simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, hS.exec,
    execLocalRule_of_none (localRule_bra (t := t) (target := target) (uni := true)), execLocal,
    Op.rule, execBranch, Op.isLocal, pure, Except.pure]

/-- A piece moved to other, equal start and end counters. -/
theorem seg_cast {n s s' b b' : Nat} {d : D} (h : Seg kernel asms L g n s (factsAt L g s d) b
    (factsAt L g b d)) (hs : s = s') (hb : b = b') :
    Seg kernel asms L g n s' (factsAt L g s' d) b' (factsAt L g b' d) := by
  subst hs hb
  exact h

/-! ### The code, decided -/

/-- The instruction at `pc` is `mov.b<w> dst, {a, b}`. -/
def packAt (pc dst a b w : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .move m⟩ => m == ⟨.pack, .int .b w, [some dst], [.reg a, .reg b]⟩
  | _ => false

theorem packAt_spec {pc dst a b w : Nat} (h : packAt pc dst a b w = true) :
    kernel.code[pc]? = some ⟨none, .move ⟨.pack, .int .b w, [some dst], [.reg a, .reg b]⟩⟩ := by
  unfold packAt at h
  split at h
  · rename_i m hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

/-- The instruction at `pc` is `add.s32 dst, a, -c`. -/
def addAt (pc dst a c : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .int i⟩ => i == ⟨.add, .int .s 32, false, [some dst], [.reg a, .imm (-(c : Int))]⟩
  | _ => false

theorem addAt_spec {pc dst a c : Nat} (h : addAt pc dst a c = true) :
    kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
      [.reg a, .imm (-(c : Int))]⟩⟩ := by
  unfold addAt at h
  split at h
  · rename_i m hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

theorem packAt_words : ∀ q < 32, packAt (816 + q) (1916 + q) (263 + 2 * q) (263 + (2 * q + 1)) 32 =
    true := by decide +kernel
theorem emu_words : ∀ q < 32, Assumptions.emuSites.contains (816 + q) = false := by
  decide +kernel
theorem live_words_src : ∀ q < 32, (263 + 2 * q) ∈ Flow.live (816 + q) ∧
    (263 + (2 * q + 1)) ∈ Flow.live (816 + q) := by decide +kernel
theorem live_words_next : ∀ q < 32, ∀ r ∈ Flow.live (816 + q + 1),
    r = 1916 + q ∨ r ∈ Flow.live (816 + q) := by decide +kernel

theorem addAt_a : ∀ m < 31, addAt (850 + 3 * m) (812 + 2 * m) 810 (63 - 2 * m) = true := by
  decide +kernel
theorem addAt_b : ∀ m < 31, addAt (851 + 3 * m) (813 + 2 * m) 810 (62 - 2 * m) = true := by
  decide +kernel
theorem packAt_pairs : ∀ m < 31,
    packAt (852 + 3 * m) (1992 - m) (813 + 2 * m) (812 + 2 * m) 64 = true := by decide +kernel
theorem emu_pairs : ∀ m < 31, Assumptions.emuSites.contains (850 + 3 * m) = false ∧
    Assumptions.emuSites.contains (851 + 3 * m) = false ∧
    Assumptions.emuSites.contains (852 + 3 * m) = false := by decide +kernel
theorem live_pairs : ∀ m < 31, 810 ∈ Flow.live (850 + 3 * m) ∧ 810 ∈ Flow.live (851 + 3 * m) ∧
    (813 + 2 * m) ∈ Flow.live (852 + 3 * m) ∧ (812 + 2 * m) ∈ Flow.live (852 + 3 * m) := by
  decide +kernel
theorem live_pairs_next : ∀ m < 31,
    (∀ r ∈ Flow.live (850 + 3 * m + 1), r = 812 + 2 * m ∨ r ∈ Flow.live (850 + 3 * m)) ∧
    (∀ r ∈ Flow.live (851 + 3 * m + 1), r = 813 + 2 * m ∨ r ∈ Flow.live (851 + 3 * m)) ∧
    (∀ r ∈ Flow.live (852 + 3 * m + 1), r = 1992 - m ∨ r ∈ Flow.live (852 + 3 * m)) := by
  decide +kernel

/-! ### The table at the packed words, the sums and the pairs -/

/-- The registers of the packed words are looked up in the bias-word section. -/
theorem valueOf_packed (d : D) {q : Nat} (hq : q < 32) :
    valueOf L g d (1916 + q) = joinValue (d.wd (2 * q)) (d.wd (2 * q + 1)) := by
  obtain ⟨hS, hP, hQ, hR⟩ := keys_off_words (L := L) (g := g) d (r := 1916 + q)
    (Or.inr (Or.inr ⟨by omega, by omega⟩))
  have hX := keys_off_X (L := L) (g := g) d (r := 1916 + q)
    (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  have hI := notI (L := L) (g := g) d (r := 1916 + q) (by unfold IKey; omega)
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ hI,
    lookup_none_of_not_mem _ hS,
    lookup_none_of_not_mem _ hP, lookup_none_of_not_mem _ hQ, lookup_none_of_not_mem _ hR,
    lookup_none_of_not_mem _ hX, Option.none_or, Option.or_none, valuesW, valuesWf,
    lookup_range_map]
  have h1 : ¬ (263 ≤ 1916 + q ∧ 1916 + q < 263 + 64) := by omega
  have h2 : 1916 ≤ 1916 + q ∧ 1916 + q < 1916 + 32 := by omega
  have e1 : (1916 + q == 332) = false := by simp; omega
  have e2 : (1916 + q == 333) = false := by simp; omega
  have h3 : ¬ (334 ≤ 1916 + q ∧ 1916 + q < 334 + 63) := by omega
  simp [h1, h2, List.lookup, e1, e2, lookup_range_map, h3]

/-- The registers of the pairs and of the sums hold no register of the scalar or 64-bit
sections. -/
theorem keys_off_pairs (d : D) {r : Nat} (hr : (812 ≤ r ∧ r < 874) ∨ (1962 ≤ r ∧ r < 1993)) :
    r ∉ (valuesS L g d).map Prod.fst ∧ r ∉ (valuesP L g d).map Prod.fst ∧
      r ∉ (valuesI L g d).map Prod.fst := by
  refine ⟨fun hm => ?_, fun hm => ?_, notI d (by unfold IKey; omega)⟩
  · simp only [valuesS, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    omega
  · simp only [valuesP, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    omega

/-- The sum register `%r(351 + k)` is `pos - (63 - k)`. -/
theorem valueOf_sum (d : D) {k : Nat} (hk : k < 62) :
    valueOf L g d (812 + k) = posSum d.e (g % L.block) (63 - k) := by
  obtain ⟨hS, hP, hI⟩ := keys_off_pairs (L := L) (g := g) d (r := 812 + k)
    (Or.inl ⟨by omega, by omega⟩)
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ hI,
    lookup_none_of_not_mem _ hS, lookup_none_of_not_mem _ hP, Option.none_or, valuesQ,
    lookup_range_map]
  have h1 : ¬ (1962 ≤ 812 + k ∧ 812 + k < 1962 + 31) := by omega
  have h2 : 812 ≤ 812 + k ∧ 812 + k < 812 + 62 := by omega
  simp [h1, h2]

/-- The pair register `%rd(14 + j)` packs `pos - 2 j - 2` and `pos - 2 j - 3`. -/
theorem valueOf_pair (d : D) {j : Nat} (hj : j < 31) :
    valueOf L g d (1962 + j) = pairPos d.e (g % L.block) (2 + 2 * j) (3 + 2 * j) := by
  obtain ⟨hS, hP, hI⟩ := keys_off_pairs (L := L) (g := g) d (r := 1962 + j)
    (Or.inr ⟨by omega, by omega⟩)
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ hI,
    lookup_none_of_not_mem _ hS, lookup_none_of_not_mem _ hP, Option.none_or, valuesQ,
    lookup_range_map]
  have h2 : 1962 ≤ 1962 + j ∧ 1962 + j < 1962 + 31 := by omega
  simp [h2]

theorem wd_bytes {d : D} (hwb : ∀ k, (d.w k).bytes = 2) (k : Nat) : (d.wd k).bytes = 2 := by
  unfold D.wd
  split
  · exact hwb k
  · rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
