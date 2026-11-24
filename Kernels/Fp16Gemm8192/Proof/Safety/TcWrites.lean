-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.Resource
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds
public import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

/-! # The Tensor Memory conflict branches of `Unsafe`, from the interface

The only Tensor Memory writers are the MMAs (no store or copy is issued). An MMA of warp
`w ∈ {8, 9}` of a leader CTA writes columns `256 * (w % 2)` to `256 * (w % 2) + 255` of the
cluster's CTA pair (`ThreadFacts.mma_issue`, `mma_dst`), so a cell names the CTA pair and the
warp of every MMA that writes or accumulates it. The MMA is issued by its warp's elected lane: its
slot's full barrier was polled successfully before, and that poll follows the full-mask election
(`ThreadFacts.elected`), which elects the same lane everywhere (`ElectOk`). So two MMAs at one
cell are issued by one thread, in program order, on the same accumulator: a pipeline pair
(`TcMma.Pipelined`). This excludes `TcMma.WritesUnsafe` (`no_writes_unsafe`) and
`TcMma.ReadsUnsafe` (`no_reads_unsafe`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX PTX.Flow TcMma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The result cells of the kernel's MMAs name the issuer's CTA pair and its warp's buffer. -/
theorem result_cell {cta w sl j row col : Nat} {cell : Cell}
    (h : resultCell (InputRing.mmaSpec L cta w sl j) (256 * (w % 2)) row col = some cell) :
    cell.cta / 2 = cta / 2 ∧ cell.column / 256 = w % 2 := by
  have hm : (InputRing.mmaSpec L cta w sl j).descriptor.m =
      128 * (InputRing.mmaSpec L cta w sl j).descriptor.group.size := rfl
  unfold resultCell at h
  simp only [hm, ↓reduceIte] at h
  have hw : w % 2 < 2 := Nat.mod_lt _ (by decide)
  split_ifs at h with h1 h2
  all_goals
    simp only [Option.some.injEq] at h
    subst h
    simp only [InputRing.mmaSpec, InputRing.mmaDescriptor, CtaGroup.size] at h1 ⊢
    constructor <;> omega

/-- An MMA of the kernel: issued by an elected lane of warp 8 or 9 of a leader CTA, of its warp's
operands and buffer. -/
theorem mma_source (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {x : EvId} {dst : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue x dst s acc mask) :
    x.1 < L.threads ∧ x.1 / L.block % 2 = 0 ∧
      (x.1 % L.block / 32 = 8 ∨ x.1 % L.block / 32 = 9) ∧
      (∃ sl j, s = InputRing.mmaSpec L (x.1 / L.block) (x.1 % L.block / 32) sl j) ∧
      dst = 256 * (x.1 % L.block / 32 % 2) ∧ mask = List.replicate 8 0 ∧
      ∃ j pc inst, X.Elect (x.1, j) pc 4294967295 inst (laneOf L x.1) := by
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨m, sl, j, rfl, -, hlead, hsp, hcnt⟩ := ht.mma_issue hg he hσ rfl
  obtain ⟨hdst, hmask⟩ := ht.mma_dst hg he hσ rfl
  have hw := ht.role_warp hg (List.getElem?_eq_some_iff.mp he).1.le hσ
  simp only [roleWarp] at hw
  obtain ⟨jp, ppc, pp, pacq, psc, -, hjp⟩ := exists_okPoll (X := X)
    (show 0 < okPolls ⟨.shared, x.1 / L.block, L.sharedBase + 8 + 8 * sl.val⟩
      ((X.tr x.1).take x.2) by omega)
  obtain ⟨dp, hσp⟩ := Frame.event_state ht.sound hX ht.tracked hjp nofun
  have hloc : (⟨.shared, x.1 / L.block, L.sharedBase + 8 + 8 * sl.val⟩ : Loc) =
      Bar.loc L (x.1 / L.block) ⟨.input, sl.val, true⟩ := by
    simp only [Bar.loc, Bar.off, Nat.add_assoc]
  rw [hloc] at hjp
  obtain ⟨hpoll, -⟩ :=
    (ht.ring_event (Frame.lt_of_get hX hjp) hjp hσp).wait ⟨.input, sl.val, true⟩ _
    _ _ _ _ rfl (show sl.val < 4 from sl.isLt)
  obtain ⟨mm, rfl⟩ : ∃ mm, dp = .inr (.mma mm) := hpoll
  obtain ⟨je, inst, leader, -, hje, hlane⟩ := ht.elected (r := .mma mm)
    (Frame.lt_of_get hX hjp) hjp hσp
    rfl trivial
  refine ⟨hg, hlead, ?_, ⟨sl.val, j.val, hsp⟩, hdst, hmask, je, ?_⟩
  · exact hw.2
  · exact ⟨_, inst, hlane ▸ hje⟩

/-- Two MMAs at one cell are issued by one thread, on the same accumulator. -/
theorem same_cell_issuer (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {x y : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} (hx : X.MmaIssue x d s acc mask) (hy : X.MmaIssue y d' s' acc' mask')
    {r c r' c' : Nat} {cell : Cell} (hcx : resultCell s d r c = some cell)
    (hcy : resultCell s' d' r' c' = some cell) :
    x.1 = y.1 ∧ SameAccumulator d s d' s' := by
  obtain ⟨hgx, hlx, hwx, ⟨slx, jx, rfl⟩, rfl, -, ex, pcx, ix, hex⟩ := mma_source hX ht hx
  obtain ⟨hgy, hly, hwy, ⟨sly, jy, rfl⟩, rfl, -, ey, pcy, iy, hey⟩ := mma_source hX ht hy
  obtain ⟨cx1, cx2⟩ := result_cell hcx
  obtain ⟨cy1, cy2⟩ := result_cell hcy
  have hb := hpre.block
  have hcta : x.1 / 384 = y.1 / 384 := by rw [hb] at hlx hly hwx hwy cx1 cx2 cy1 cy2; omega
  have hw : x.1 % 384 / 32 = y.1 % 384 / 32 := by rw [hb] at hlx hly hwx hwy cx1 cx2 cy1 cy2; omega
  have hlane : laneOf L x.1 = laneOf L y.1 :=
    hX.elect.2.2 _ _ _ _ _ _ _ _ _ hex hey ⟨⟨hgx, hgy, by rw [hb]; exact hcta⟩, by
      rw [hb]; exact hw⟩
  simp only [laneOf, hb] at hlane
  rw [hb] at hlx hly hwx hwy cx1 cx2 cy1 cy2 ⊢
  have hxy : x.1 = y.1 := by omega
  refine ⟨hxy, by rw [hw], ?_⟩
  simp only [InputRing.mmaSpec, InputRing.mmaDescriptor, hcta, and_self]

/-- Two MMAs at one cell, in program order, are a pipeline pair. -/
theorem pipeline_of (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {x y : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} (hx : X.MmaIssue x d s acc mask) (hy : X.MmaIssue y d' s' acc' mask')
    {r c r' c' : Nat} {cell : Cell} (hcx : resultCell s d r c = some cell)
    (hcy : resultCell s' d' r' c' = some cell)
    (hlt : x.2 < y.2) : Pipelined L X .dWrite x .dWrite y := by
  obtain ⟨hxy, hsame⟩ := same_cell_issuer hpre hX ht hx hy hcx hcy
  obtain ⟨pcy, hey⟩ := hy
  have hlen := (List.getElem?_eq_some_iff.mp hey).1
  have hgy := Frame.lt_of_get hX hey
  exact ⟨⟨⟨hxy ▸ hgy, hgy, by rw [hxy]⟩, by rw [hxy]⟩,
    .inl (.single (.inl (po_of_not_access hxy hlt hlen (by simp [hey, Event.acc])))), d, s, acc,
    mask, d', s', acc', mask', hx, ⟨pcy, hey⟩, hsame⟩

/-- Two MMAs at one cell are equal or a pipeline pair, one way or the other. -/
theorem pipeline_cases (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {x y : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} (hx : X.MmaIssue x d s acc mask) (hy : X.MmaIssue y d' s' acc' mask')
    {r c r' c' : Nat} {cell : Cell} (hcx : resultCell s d r c = some cell)
    (hcy : resultCell s' d' r' c' = some cell) :
    x = y ∨ Pipelined L X .dWrite x .dWrite y ∨ Pipelined L X .dWrite y .dWrite x := by
  have hxy := (same_cell_issuer hpre hX ht hx hy hcx hcy).1
  rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
  · exact .inr (.inl (pipeline_of hpre hX ht hx hy hcx hcy h))
  · exact .inl (Prod.ext hxy h)
  · exact .inr (.inr (pipeline_of hpre hX ht hy hx hcy hcx h))

/-- A Tensor Memory write of the kernel is an MMA's. -/
theorem write_mma (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {w : EvId}
    {cell : Cell} (hw : TmemWrite L X w cell) :
    ∃ d s acc mask r c, X.MmaIssue w d s acc mask ∧ resultCell s d r c = some cell := by
  rcases hw with ⟨d, s, acc, mask, r, c, hi, hc⟩ | ⟨a, vals, sh, j, ⟨pc, he⟩, -⟩ |
      ⟨a, src, cta, idx, ⟨pc, he⟩, -⟩ | ⟨sp, hsh, -⟩
  · exact ⟨d, s, acc, mask, r, c, hi, writeCell_resultCell hc⟩
  · obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
    exact absurd rfl (ht.no_tc_st (Frame.lt_of_get hX he) he hσ)
  · obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
    exact absurd rfl (ht.no_tc_cp (Frame.lt_of_get hX he) he hσ)
  · exact (no_shift hX ht hsh).elim

/-- **No two Tensor Memory writes of a cell are unordered.** -/
theorem no_writes_unsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ¬ WritesUnsafe L X := by
  refine fun hn => hn fun x y cell hx hy => ?_
  obtain ⟨d, s, acc, mask, r, c, hix, hcx⟩ := write_mma hX ht hx
  obtain ⟨d', s', acc', mask', r', c', hiy, hcy⟩ := write_mma hX ht hy
  rcases pipeline_cases hpre hX ht hix hiy hcx hcy with h | h | h
  · exact .inl h
  · exact .inr (.inl (.inl (.inr h)))
  · exact .inr (.inr (.inl (.inr h)))

/-- **No accumulator read of a cell is unordered with a write of it.** The kernel's MMAs read
no Tensor Memory A operand and it issues no shift. -/
theorem no_reads_unsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ¬ ReadsUnsafe L X := by
  refine fun hn => hn (readsSafe_iff.mpr ⟨fun rd wr cell hr hw => ?_, fun rd wr cell hr hw => ?_,
    fun rd wr cell hr hw => ?_⟩)
  · obtain ⟨d', s', acc', mask', r', c', hiw, hcw⟩ := write_mma hX ht hw
    obtain ⟨d, s, mask, r, c, hir, hcr⟩ := hr
    rcases pipeline_cases hpre hX ht hir hiw hcr hcw with h | h | h
    · exact .inl h
    · exact .inr (.inr (.inr (.inr h)))
    · exact .inr (.inl (.inl (.inr h)))
  · obtain ⟨d, s, acc, mask, idx, b, hir, ha⟩ := hr
    obtain ⟨-, -, -, ⟨sl, j, rfl⟩, -⟩ := mma_source hX ht hir
    simp [aCell, InputRing.mmaSpec] at ha
  · obtain ⟨sp, hsh, -⟩ := hr
    exact (no_shift hX ht hsh).elim

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
