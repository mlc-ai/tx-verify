-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Ord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0

@[expose] public section

/-! # The barrier class of the `.aligned` rule

* `bar_pc`: two lanes of a warp at their `k`-th barrier event, one of them aligned, are at one pc.
  The aligned barriers are the startup's `bar.sync 0` (pc 97) and warpgroup 0's `bar.sync`; the
  `everyone_sync` sites are `barrier.sync` (not aligned, `unaligned_pcs`), so two of them never
  compare. The barrier ordinals (`BarInputs`) separate the startup's barrier from the others and
  put the lanes of warpgroup 0 at one pc.
* `bar_unexited`: the aligned barrier without a thread count is the startup's `bar.sync 0` only
  (`everyone_sync` is unaligned, the others carry a count), the first barrier event of its
  thread, and every thread's `exit` follows a barrier-0 event (`bar0_exit`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The `everyone_sync` sites are `barrier.sync`, not aligned. -/
theorem unaligned_pcs : ([1835, 2160, 2330, 2585, 2604, 3610].all fun pc =>
    !kernel.alignedAt pc) = true := by
  decide +kernel

/-- The startup's `bar.sync 0` is aligned. -/
theorem aligned_97 : kernel.alignedAt 97 = true := by
  decide +kernel

/-- **A barrier event is the startup's (pc 97), warpgroup 0's, or an unaligned
`everyone_sync` of a warp of warps 4–11.** -/
theorem bar_pcCls {g : Nat} {e : Event} (hu : BarUse L g e) :
    (e.pc = 97 ∧ StartupAt e.pc ∧ BarRow.Cta e) ∨
    (Wg0At L g e.pc ∧ BarRow.Wg0Use L g e) ∨
    (4 ≤ warp L g ∧ 103 ≤ e.pc ∧ kernel.alignedAt e.pc = false ∧ e.kind = .bar 12 none .sync) := by
  have hun := List.all_eq_true.mp unaligned_pcs
  rcases hu with ⟨hw, hpc, h⟩ | ⟨hw, h⟩ | ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩ | ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩ |
    ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩ | ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩ | ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩
  · exact .inl ⟨hpc, hw, h⟩
  · exact .inr (.inl ⟨hw, h⟩)
  all_goals refine .inr (.inr ⟨by omega, by omega, ?_, h⟩)
  all_goals have := hun e.pc (by rw [hpc]; simp)
  all_goals simpa using this

/-- **Two lanes of a warp at one barrier ordinal, one of them aligned, are at one pc.** -/
theorem bar_pc (hp : Pre P L m) (hR : BarRows P L X) (hO : BarInputs L X) {g h i j : Nat}
    {e e' : Event} (hw : SameWarp L g h) (hi : X.get (g, i) = some e)
    (hj : X.get (h, j) = some e') (hb : Execution.isBar e = true)
    (hb' : Execution.isBar e' = true)
    (hk : ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar)
    (ha : (kernel.alignedAt e.pc || kernel.alignedAt e'.pc) = true) : e.pc = e'.pc := by
  obtain ⟨⟨hg, hh, -⟩, -⟩ := id hw
  have hwe := warp_eq hp hw
  rcases bar_pcCls (bar_use hR hg hi hb) with ⟨hp1, hs, -⟩ | ⟨hs, -⟩ | ⟨hw1, hpc, hu, -⟩ <;>
    rcases bar_pcCls (bar_use hR hh hj hb') with ⟨hp2, hs', -⟩ | ⟨hs', -⟩ | ⟨hw2, hpc', hu', -⟩
  · omega
  · have := hO.first hg hi hs hb
    have := hO.later hh hj hs'.2.1 hb'
    omega
  · have := hO.first hg hi hs hb
    have := hO.later hh hj hpc' hb'
    omega
  · have := hO.later hg hi hs.2.1 hb
    have := hO.first hh hj hs' hb'
    omega
  · exact hO.wg0 hw hi hj hs hs' hb hb' hk
  · have := hs.1; omega
  · have := hO.later hg hi hpc hb
    have := hO.first hh hj hs' hb'
    omega
  · have := hs'.1; omega
  · simp [hu, hu'] at ha

/-- **No participant exits before an aligned barrier without a thread count**: that barrier is
the startup's `bar.sync 0`, its thread's first barrier event, and every `exit` follows one. -/
theorem bar_unexited (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) (hO : BarInputs L X) {e f : EvId} {ev : Event}
    (hs : SameCta L e.1 f.1) (he : X.get e = some ev) (hm : kernel.isAlignedCtaBar ev = true)
    (hx : X.ExitedShort kernel.isAlignedCtaBar f
      (((X.tr e.1).take e.2).countP kernel.isAlignedCtaBar)) : False := by
  obtain ⟨hg, hf, -⟩ := hs
  obtain ⟨⟨pcx, hxe⟩, hcnt⟩ := hx
  have hal := isAlignedCtaBar_kind hm
  obtain ⟨pc, kd⟩ := ev
  have hbar : Execution.isBar ⟨pc, kd⟩ = true := by
    cases kd <;> simp_all [Kernel.isAlignedCtaBar, Execution.isBar]
  have hnone : ∃ id md, kd = .bar id none md := by
    cases kd <;> simp_all [Kernel.isAlignedCtaBar]
    rename_i id cnt md
    cases cnt <;> simp_all
  obtain ⟨id, md, rfl⟩ := hnone
  have hstart : pc = 97 ∧ StartupAt pc := by
    rcases bar_pcCls (bar_use hR hg he hbar) with ⟨hp1, hs0, -⟩ | ⟨-, h⟩ | ⟨-, -, hu, -⟩
    · exact ⟨hp1, hs0⟩
    · simp only [BarRow.Wg0Use, BarRow.Sync, BarRow.Everyone, Kind.bar.injEq] at h
      rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h1, h2⟩
      · simp at h
      · simp at h
      · simp only at h1 hal
        rw [h1] at hal
        have := List.all_eq_true.mp unaligned_pcs 1835 (by simp)
        simp_all
    · simp_all
  obtain ⟨hpc, hst⟩ := hstart
  subst hpc
  have h0 := hO.first hg he hst hbar
  have hz : ((X.tr e.1).take e.2).countP kernel.isAlignedCtaBar = 0 := by
    refine Nat.eq_zero_of_le_zero ?_
    rw [← h0]
    refine List.countP_mono_left fun b _ hb => ?_
    obtain ⟨pb, kb⟩ := b
    cases kb <;> simp_all [Kernel.isAlignedCtaBar, Execution.isBar]
  rw [hz] at hcnt
  have hb0 := bar0_exit hp hX hFw (g := f.1) hxe
  obtain ⟨b, hbm, hb0'⟩ := List.countP_pos_iff.mp hb0
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp ((List.take_sublist _ _).subset hbm)
  obtain ⟨pb, kb⟩ := b
  obtain ⟨id', c', md', rfl⟩ : ∃ id c md, kb = .bar id c md := by
    cases kb <;> simp_all [isBar0]
  have hget : X.get (f.1, n) = some ⟨pb, .bar id' c' md'⟩ := hn
  have hid : id' = 0 := by
    by_contra hne
    simp [isBar0, hne] at hb0'
  subst hid
  have hbb : Execution.isBar ⟨pb, .bar 0 c' md'⟩ = true := rfl
  have hc' : c' = none := bar0_count hR (e := (f.1, n)) (pc := pb) ⟨md', hget⟩ hf
  subst hc'
  rcases bar_pcCls (bar_use hR hf hget hbb) with ⟨hp1, -⟩ | ⟨-, h⟩ | ⟨-, -, -, h⟩
  · have hmem : kernel.isAlignedCtaBar ⟨pb, .bar 0 none md'⟩ = true := by
      simp only [Kernel.isAlignedCtaBar, Kernel.alignedAt]
      simp only at hp1
      rw [hp1]
      exact aligned_97
    have := List.countP_pos_iff.mpr ⟨_, List.mem_iff_getElem?.mpr ⟨n, hn⟩, hmem⟩
    omega
  · simp only [BarRow.Wg0Use, BarRow.Sync, BarRow.Everyone, Kind.bar.injEq] at h
    rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> simp at h
  · simp at h

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
