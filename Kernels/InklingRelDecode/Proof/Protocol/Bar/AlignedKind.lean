-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.MBarrier.BarrierOrdinal
public import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
open PTX

variable {L : Launch} {m : Mem0} {X : Execution}

private theorem one_unaligned : ∀ p ∈ Lib.barOneSites, kernel.alignedAt p = false := by
  decide +kernel

private theorem full_aligned : ∀ p ∈ BarRow.fullZeroSites, kernel.alignedAt p = true := by
  decide +kernel

private theorem sites_apart : ∀ p ∈ BarRow.fullZeroSites ++ BarRow.halfZeroSites,
    p ∉ Lib.barOneSites := by
  decide

/-- **An aligned whole-CTA barrier event is a full barrier-0 rendezvous at one of the four full
sites.** -/
theorem aligned_event {i ev} (hX : Consistent L kernel Assumptions.all m X) (hb : L.block = 256)
    (he : X.get i = some ev) (h : kernel.isAlignedCtaBar ev = true) :
    ∃ pc, ev = ⟨pc, .bar 0 none .sync⟩ ∧ pc ∈ BarRow.fullZeroSites := by
  obtain ⟨pc, id, mode, rfl, al⟩ := Kernel.isAlignedCtaBar_iff h
  obtain ⟨rfl, rest⟩ := Lib.recorded_bar hX hb he
  rcases rest with ⟨rfl, -, site⟩ | ⟨rfl, -, site⟩ | ⟨-, cnt, -⟩
  · rw [one_unaligned pc site] at al
    cases al
  · exact ⟨pc, rfl, site⟩
  · simp [BarRow.recCnt, hb] at cnt

/-- A full barrier-0 rendezvous at a full site is aligned. -/
theorem aligned_of_site {pc} (h : pc ∈ BarRow.fullZeroSites) :
    kernel.isAlignedCtaBar ⟨pc, .bar 0 none .sync⟩ = true := by
  simp [Kernel.isAlignedCtaBar, full_aligned pc h]

/-- The barrier of a barrier event is determined by its pc. -/
theorem bar_id_of_pc {i pc id cnt md} (hX : Consistent L kernel Assumptions.all m X)
    (hb : L.block = 256) (he : X.get i = some ⟨pc, .bar id cnt md⟩) :
    id = if pc ∈ Lib.barOneSites then 1 else 0 := by
  obtain ⟨-, rest⟩ := Lib.recorded_bar hX hb he
  rcases rest with ⟨rfl, -, site⟩ | ⟨rfl, -, site⟩ | ⟨rfl, -, site⟩
  · simp [site]
  · simp [sites_apart pc (List.mem_append_left _ site)]
  · simp [sites_apart pc (List.mem_append_right _ site)]

/-- Barrier events at one pc are on one barrier. -/
theorem isBarId_of_pc {i j pc k k'} (hX : Consistent L kernel Assumptions.all m X)
    (hb : L.block = 256) (hi : X.get i = some ⟨pc, k⟩) (hj : X.get j = some ⟨pc, k'⟩)
    (bi : Execution.isBar ⟨pc, k⟩ = true) (bj : Execution.isBar ⟨pc, k'⟩ = true) (n : Nat) :
    Execution.isBarId n ⟨pc, k⟩ = Execution.isBarId n ⟨pc, k'⟩ := by
  cases k <;> simp [Execution.isBar] at bi
  cases k' <;> simp [Execution.isBar] at bj
  rw [bar_id_of_pc hX hb hi, bar_id_of_pc hX hb hj]
  simp only [Execution.isBarId]

private theorem isBar_of_id {n pc k} (h : Execution.isBarId n ⟨pc, k⟩ = true) :
    Execution.isBar ⟨pc, k⟩ = true := by
  cases k <;> simp_all [Execution.isBarId, Execution.isBar]

private theorem ids_apart {pc k} (h : Execution.isBarId 0 ⟨pc, k⟩ = true) :
    Execution.isBarId 1 ⟨pc, k⟩ = false := by
  cases k <;> simp_all [Execution.isBarId]

private theorem ids_apart' {pc k} (h : Execution.isBarId 1 ⟨pc, k⟩ = true) :
    Execution.isBarId 0 ⟨pc, k⟩ = false := by
  cases k <;> simp_all [Execution.isBarId]

theorem isBarId_split {l : List Event}
    (h : ∀ ev ∈ l, Execution.isBar ev = true →
      Execution.isBarId 0 ev = true ∨ Execution.isBarId 1 ev = true) :
    l.countP Execution.isBar = l.countP (Execution.isBarId 0) + l.countP (Execution.isBarId 1) := by
  induction l with
  | nil => rfl
  | cons ev l ih =>
    have tail := ih (fun x mem => h x (List.mem_cons_of_mem _ mem))
    obtain ⟨pc, k⟩ := ev
    by_cases isb : Execution.isBar ⟨pc, k⟩ = true
    · rcases h _ List.mem_cons_self isb with h0 | h1
      · simp [isb, h0, ids_apart h0]
        omega
      · simp [isb, h1, ids_apart' h1]
        omega
    · have n0 : Execution.isBarId 0 ⟨pc, k⟩ = false :=
        Bool.eq_false_iff.mpr fun x => isb (isBar_of_id x)
      have n1 : Execution.isBarId 1 ⟨pc, k⟩ = false :=
        Bool.eq_false_iff.mpr fun x => isb (isBar_of_id x)
      simp [isb, n0, n1]
      omega

/-- **Every barrier event of a prefix is on barrier 0 or 1.** -/
theorem bar_count_split {g k} (hX : Consistent L kernel Assumptions.all m X) (hb : L.block = 256) :
    ((X.tr g).take k).countP Execution.isBar =
      ((X.tr g).take k).countP (Execution.isBarId 0) +
        ((X.tr g).take k).countP (Execution.isBarId 1) := by
  apply isBarId_split
  intro ev mem isb
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take mem)
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp [Execution.isBar] at isb
  obtain ⟨-, rest⟩ := Lib.recorded_bar hX hb (show X.get (g, n) = _ from hn)
  rcases rest with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [Execution.isBarId]

/-- The first two rendezvous of a lane are full ones: a barrier event at pc 12 or 14 is the
aligned whole-CTA barrier 0. -/
theorem early_aligned {i pc id cnt md} (hX : Consistent L kernel Assumptions.all m X)
    (hb : L.block = 256) (he : X.get i = some ⟨pc, .bar id cnt md⟩) (h : pc = 12 ∨ pc = 14) :
    kernel.isAlignedCtaBar ⟨pc, .bar id cnt md⟩ = true := by
  obtain ⟨rfl, rest⟩ := Lib.recorded_bar hX hb he
  rcases h with rfl | rfl <;> rcases rest with ⟨-, -, s⟩ | ⟨rfl, rfl, -⟩ | ⟨-, -, s⟩
  all_goals first | exact absurd s (by decide) | exact aligned_of_site (by decide)


theorem bar_shape {pc k} (h : Execution.isBar ⟨pc, k⟩ = true) :
    ∃ id cnt md, k = .bar id cnt md := by
  cases k <;> simp_all [Execution.isBar]

/-- A barrier event off barrier 1 is a rendezvous of barrier 0 that waits. -/
theorem zero_sync {i pc id cnt md} (hX : Consistent L kernel Assumptions.all m X)
    (hb : L.block = 256) (he : X.get i = some ⟨pc, .bar id cnt md⟩)
    (off : pc ∉ Lib.barOneSites) : id = 0 ∧ md = .sync := by
  have := bar_id_of_pc hX hb he
  simp only [off, ↓reduceIte] at this
  exact ⟨this, (Lib.recorded_bar hX hb he).1⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
