-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmPackBase

@[expose] public section

/-! # The packs of the bias words and of the key positions (pcs 807-948)

From the last preload to the jump into the loop test: the negated scale (pc 807), the sign
extension of the block count and the other integer setup (pcs 808-815), the 32 packs of the loaded
half-words (pcs 816-847), the two 64-bit packs of the scale and of the first position pair
(pcs 848-849), the 31 pairs of key positions (pcs 850-942) and the loop's start values
(pcs 943-947). The packs are chained by induction on the index from the one-instruction pieces of
`SmPackBase`; the rest is `seg_fp`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

/-- `mov.b32 %r(1455 + q), {%rs(82 + 2 q), %rs(83 + 2 q)}` (pc `816 + q`). -/
theorem seg_word (d : D) (hwb : ∀ k, (d.w k).bytes = 2) {q : Nat} (hq : q < 32) :
    Seg kernel asms L g 1 (816 + q) (factsAt L g (816 + q) d) (816 + q + 1)
      (factsAt L g (816 + q + 1) d) := by
  obtain ⟨la, lb⟩ := live_words_src q hq
  exact seg_pack1 (packAt_spec (packAt_words q hq)) (Or.inl rfl) (emu_words q hq)
    (valueOf_pre d (by omega : 2 * q < 64)) (valueOf_pre d (by omega : 2 * q + 1 < 64))
    (wd_bytes hwb _) (wd_bytes hwb _) la lb (valueOf_packed d hq) (live_words_next q hq)

/-- **The 32 packs of the bias words** (pcs 816 to 847). -/
theorem seg_words (d : D) (hwb : ∀ k, (d.w k).bytes = 2) : ∀ m, m ≤ 32 →
    Seg kernel asms L g m 816 (factsAt L g 816 d) (816 + m) (factsAt L g (816 + m) d) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih => exact fun hm => (ih (by omega)).comp (seg_word d hwb (q := m) (by omega))

theorem valueOf_sumA (d : D) {m : Nat} (hm : m < 31) :
    valueOf L g d (812 + 2 * m) = posSum d.e (g % L.block) (63 - 2 * m) :=
  valueOf_sum d (k := 2 * m) (by omega)

theorem valueOf_sumB (d : D) {m : Nat} (hm : m < 31) :
    valueOf L g d (813 + 2 * m) = posSum d.e (g % L.block) (62 - 2 * m) := by
  have := valueOf_sum (L := L) (g := g) d (k := 2 * m + 1) (by omega)
  rw [show 812 + (2 * m + 1) = 813 + 2 * m by omega,
    show 63 - (2 * m + 1) = 62 - 2 * m by omega] at this
  exact this

theorem valueOf_pairM (d : D) {m : Nat} (hm : m < 31) :
    valueOf L g d (1992 - m) = joinValue (posSum d.e (g % L.block) (62 - 2 * m))
      (posSum d.e (g % L.block) (63 - 2 * m)) := by
  have := valueOf_pair (L := L) (g := g) d (j := 30 - m) (by omega)
  rw [show 1962 + (30 - m) = 1992 - m by omega] at this
  rw [this, pairPos, show 2 + 2 * (30 - m) = 62 - 2 * m by omega,
    show 3 + 2 * (30 - m) = 63 - 2 * m by omega]

theorem posSum_eq (d : D) {c : Nat} (hc : c ≤ 2 ^ 32) : posSum d.e (g % L.block) c =
    b32 ((posOf d.e (g % L.block) + 2 ^ 32 - c) % 2 ^ 32) := by
  unfold posSum posOf
  congr 1
  omega

/-- The two sums and the pack of the pair `m` (pcs `850 + 3 m` to `852 + 3 m`). -/
theorem seg_pair (d : D) {m : Nat} (hm : m < 31) :
    Seg kernel asms L g 3 (850 + 3 * m) (factsAt L g (850 + 3 * m) d) (850 + 3 * (m + 1))
      (factsAt L g (850 + 3 * (m + 1)) d) := by
  obtain ⟨hn1, hn2, hn3⟩ := emu_pairs m hm
  obtain ⟨l1, l2, l3, l4⟩ := live_pairs m hm
  obtain ⟨u1, u2, u3⟩ := live_pairs_next m hm
  have v811 : valueOf L g d 810 = b32 (posOf d.e (g % L.block)) := by sm_vals
  have h1 := seg_addImm1 (L := L) (g := g) (d := d) (addAt_spec (addAt_a m hm)) (by omega)
    (by omega) hn1 v811 l1 (by rw [valueOf_sumA d hm, posSum_eq d (by omega)]) u1
  have h2 := seg_addImm1 (L := L) (g := g) (d := d) (addAt_spec (addAt_b m hm)) (by omega)
    (by omega) hn2 v811 l2 (by rw [valueOf_sumB d hm, posSum_eq d (by omega)]) u2
  have h3 := seg_pack1 (L := L) (g := g) (d := d) (packAt_spec (packAt_pairs m hm))
    (Or.inr rfl) hn3 (x := valueOf L g d (813 + 2 * m)) (y := valueOf L g d (812 + 2 * m))
    rfl rfl (by rw [valueOf_sumB d hm]; rfl) (by rw [valueOf_sumA d hm]; rfl) l3 l4
    (by rw [valueOf_pairM d hm, valueOf_sumA d hm, valueOf_sumB d hm]) u3
  have h1' := seg_cast h1 rfl (show 850 + 3 * m + 1 = 851 + 3 * m by omega)
  have h2' := seg_cast h2 rfl (show 851 + 3 * m + 1 = 852 + 3 * m by omega)
  have h3' := seg_cast h3 rfl (show 852 + 3 * m + 1 = 850 + 3 * (m + 1) by omega)
  exact Seg.of_len ((h1'.comp h2').comp h3') rfl

/-- **The 31 position pairs** (pcs 850 to 942). -/
theorem seg_pairs (d : D) : ∀ m, m ≤ 31 →
    Seg kernel asms L g (3 * m) 850 (factsAt L g 850 d) (850 + 3 * m)
      (factsAt L g (850 + 3 * m) d) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih =>
    exact fun hm => Seg.of_len ((ih (by omega)).comp (seg_pair d (m := m) (by omega))) (by omega)

theorem emu_848 : Assumptions.emuSites.contains 848 = false ∧
    Assumptions.emuSites.contains 849 = false := by decide +kernel

/-- `mov.b64 %rd12, {%r344, %r344}`, the scale's reciprocal twice (pc 848). -/
theorem seg_848 (d : D) :
    Seg kernel asms L g 1 848 (factsAt L g 848 d) 849 (factsAt L g 849 d) := by
  have v806 : valueOf L g d 805 = .float .f32 (1 / d.e.sc) := by sm_vals
  exact seg_pack1 (d := d) Flow.code_848 (Or.inr rfl) emu_848.1 (x := .float .f32 (1 / d.e.sc))
    (y := .float .f32 (1 / d.e.sc)) v806 v806 rfl rfl (by decide +kernel) (by decide +kernel)
    (by sm_vals) (by decide +kernel)

/-- `mov.b64 %rd13, {%r349, %r350}` (pc 849). -/
theorem seg_849 (d : D) :
    Seg kernel asms L g 1 849 (factsAt L g 849 d) 850 (factsAt L g 850 d) := by
  have v811 : valueOf L g d 810 = b32 (posOf d.e (g % L.block)) := by sm_vals
  have v812 : valueOf L g d 811 = b32 (pos2Of d.e (g % L.block)) := by sm_vals
  exact seg_pack1 (d := d) Flow.code_849 (Or.inr rfl) emu_848.2 v811 v812 rfl rfl
    (by decide +kernel) (by decide +kernel) (by sm_vals) (by decide +kernel)

theorem seg_808 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 4 808 (factsAt L g 808 d) 812 (factsAt L g 812 d) := by
  intro t h
  sm_seg h

/-- `cvt.s64.s32 %rd10, %r25`: the block count as a signed 64-bit number (pc 812). -/
theorem seg_812 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 812 (factsAt L g 812 d) 813 (factsAt L g 813 d) := by
  intro t h
  sm_seg h [cvt_s64_s32]

theorem seg_813 (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) :
    Seg kernel asms L g 3 813 (factsAt L g 813 d) 816 (factsAt L g 816 d) := by
  have := hok.r26_lt
  have := hok.past
  intro t h
  sm_seg h [posOf, pos2Of]

theorem seg_943 (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hi0 : d.i = 0)
    (hm : d.m = b32 4286578688) (hl : d.l = b32 0) :
    Seg kernel asms L g 5 943 (factsAt L g 943 d) 948 (factsAt L g 948 d) := by
  have := hok.split
  have := hok.splits
  intro t h
  sm_seg h [hi0, hm, hl, blkOf]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
