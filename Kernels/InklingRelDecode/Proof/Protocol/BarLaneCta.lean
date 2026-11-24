-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneLoop
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneFault
public import Kernels.InklingRelDecode.Proof.Interface.BarStatic

@[expose] public section

/-!
# `ctaBar`: no CTA barrier fault, from the generation ledger of barrier 0

`Safety.Protocol.ctaBar` (`¬ CtaBarFault L X`) for the kernel's named barriers. A fault is a pending
(unrecorded) `bar.sync` lane that the barrier resource cannot perform after the recorded history:
a second arrival of its warp in the open generation (`NamedBar.no_dup_pending`, whatever the
counts) or a count that differs from the open generation's (`NamedBar.no_fault_of_mismatch` takes
the exclusion of this case as its premise).

Every barrier event but those of `bar.sync 0, 128` has no count, so a mismatch needs a
`bar.sync 0, 128` of named barrier 0 and an arrival of another count in the same generation. The
exclusion is `bar0_no_mismatch`. It uses the phased ledger of the resource (`Phased`: a loop warp
arrives in every generation, a live warp in each of the first two) and two premises about the
events:

* `AlphaAgree`: two default-partition threads of one CTA agree on the count of their barrier-0
  arrival of each source ordinal. The count of the arrival of ordinal `o` is `128` or none
  according to whether the lazy-rescale barriers of the softmax loop (`bar23`, `bar24`) were taken
  the same number of times, and all four default warps take them together because the decision is
  the minimum of `alpha` reduced through shared memory. This is a value fact (`SmPeer.PeerExchange`,
  `Sm.next`'s `shfl12`), stated here as a premise.
* `WorkerLate`: the workers' final `bar.sync 0` (source ordinal at least 2) of a CTA follows
  every default-partition thread's `bar.sync 0, 128` in the sense that those events are not the
  last event of their thread (the threads have continued to the next barrier-1 arrival). It is
  proved from the phases and barrier 1 (`workerLate_of_roleReads`, in `BarLaneLate.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The default-partition threads of a CTA agree on the count of each barrier-0 arrival.** -/
def AlphaAgree (L : Launch) (X : Execution) : Prop :=
  ∀ {g g' k k' pc pc' : Nat} {c c' : Option Nat} {m m' : BarMode}, g < L.threads →
    g' < L.threads → g / L.block = g' / L.block → g % L.block < 128 → g' % L.block < 128 →
    X.get (g, k) = some ⟨pc, .bar 0 c m⟩ → X.get (g', k') = some ⟨pc', .bar 0 c' m'⟩ →
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      ((X.tr g').take k').countP (Execution.isBarId 0) → c = c'

/-- **The workers' final arrival follows the default partition's `bar.sync 0, 128`s**: when a worker
thread has a barrier-0 arrival of source ordinal at least 2, every `bar.sync 0, 128` of a
default-partition thread of its CTA has a later event in its thread. -/
def WorkerLate (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads → 128 ≤ g % L.block →
    X.get (g, k) = some ⟨pc, .bar 0 cnt m⟩ →
    2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0) →
    ∀ {g' k' pc' : Nat}, g' / L.block = g / L.block → g' % L.block < 128 →
      X.get (g', k') = some ⟨pc', .bar 0 (some 128) .sync⟩ → k' + 1 < (X.tr g').length

/-- **No count mismatch of named barrier 0**: a pending `bar.sync` lane whose warp has not arrived
in the open generation of a barrier does not meet another count in it. -/
theorem bar_no_mismatch (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hA : AlphaAgree L X) (hW : WorkerLate L X) : NamedBar.NoMismatch L X := by
  intro c hc s hrun id g pc k n cnt e hgb he1 hbar hfree hgx hndup hk hn hkn i u t w2 cnt2 lanes2
    g2 e2 hi ha hgen htg hp2 hm2
  have hb256 : L.block = 256 := hpre.block
  have hnb : L.block ≠ 128 := by omega
  obtain ⟨-, hsrcs, -⟩ := hX.ctaBar.2 c hc
  obtain ⟨hg2b, he2, pc2, mode2, hb2⟩ := hsrcs _ (List.mem_of_getElem? hi) (g2, e2) hm2
  simp only at hg2b he2 hb2
  have hbar2 : X.IsBarrier e2 id cnt2 pc2 := hX.isBarrier_of_arrival (K := kernel) Fact.out
    ⟨mode2, hb2⟩
  by_cases hid : id = 0
  · subst hid
    have hge : e.1 < L.threads := by rw [he1]; exact NamedBar.cta_thread_lt hc hgb
    have hmodE : e.1 % L.block = g := by
      rw [he1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hgb]
    have hdivE : e.1 / L.block = c := by rw [he1]; exact lane_div hgb
    have hge2 : e2.1 < L.threads := by rw [he2]; exact NamedBar.cta_thread_lt hc hg2b
    have hmodE2 : e2.1 % L.block = g2 := by
      rw [he2, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg2b]
    have hdivE2 : e2.1 / L.block = c := by rw [he2]; exact lane_div hg2b
    have htn : CtaBarrier.target L.block none = .ok (CtaBarrier.warps L.block) := by
      simp [CtaBarrier.target]
    have hSrc := bar0_sources hpre hX hS ht
    have hprot := hSrc.protocol hX hc
    have hl := NamedBar.phased_run (loopGroup_sub hpre) loopGroup_card (loopGroup_ne hpre)
      loopGroup_target hprot hrun
    have hlive : CtaBarrier.warpLive L.block s.exited (g / 32) :=
      NamedBar.warpLive_of_lane hgb hgx
    have hlast : ¬ e.2 + 1 < (X.tr e.1).length :=
      barrier_unrecorded_last hX hbar (by rw [hdivE]; exact hfree)
    have hord := NamedBar.pending_ordinal hX hc hrun hgb he1 hbar hfree hgx
    have hse := hSrc e pc cnt ⟨.sync, hbar⟩ hge
    rw [hmodE] at hse
    obtain ⟨hql, hq2, hqw, -, hord2, hle2⟩ := NamedBar.record_ordinal hX hc hrun hi ha hm2
    simp only at hord2
    have hse2 := hSrc e2 pc2 cnt2 ⟨mode2, hb2⟩ hge2
    rw [hmodE2, ← hord2, hqw] at hse2
    have hne : cnt ≠ cnt2 := by
      rintro rfl
      exact hkn (Except.ok.inj (htg.symm.trans hn))
    have hwrange : ∀ {w : Nat}, w ∈ loopGroup ↔ w < 4 := by
      intro w
      simp [loopGroup]
    by_cases hD : g < 128
    · -- the pending arrival is a loop warp's
      have hwD : g / 32 ∈ loopGroup := hwrange.mpr (by omega)
      have hbal := hl.balD (g / 32) hwD hlive
      simp only [hndup, ↓reduceIte, Nat.add_zero] at hbal
      have hoe : ((X.tr e.1).take e.2).countP (Execution.isBarId 0) =
          (s.slots 0).generation := hord.trans hbal
      by_cases hw2D : w2 ∈ loopGroup
      · have hg2 := NamedBar.gen_of_record (loopGroup_sub hpre) loopGroup_card
          (loopGroup_ne hpre) loopGroup_target hprot ha hp2 (.inl hw2D)
        have hg2d : g2 < 128 := by have := hwrange.mp hw2D; omega
        exact hne (hA hge hge2 (by rw [hdivE, hdivE2]) (by rw [hmodE]; exact hD)
          (by rw [hmodE2]; exact hg2d) hbar hb2 (by omega))
      · have hg2d : 128 ≤ g2 := by
          have := hwrange.not.mp hw2D
          omega
        by_cases hN2 : ((X.tr e2.1).take e2.2).countP (Execution.isBarId 0) < 2
        · have hg2 := NamedBar.gen_of_record (loopGroup_sub hpre) loopGroup_card
            (loopGroup_ne hpre) loopGroup_target hprot ha hp2 (.inr (by omega))
          have hc1 : cnt = none := by
            rcases hse with h | ⟨-, -, h⟩
            · exact h
            · omega
          have hc2 : cnt2 = none := by
            rcases hse2 with h | ⟨-, -, h⟩
            · exact h
            · omega
          exact hne (hc1.trans hc2.symm)
        · have hge2' : 2 ≤ ((X.tr e2.1).take e2.2).countP (Execution.isBarId 0) := by omega
          by_cases hc128 : cnt = some 128
          · subst hc128
            exact hlast (hW hge2 (by rw [hmodE2]; exact hg2d) hb2 hge2' (by rw [hdivE, hdivE2])
              (by rw [hmodE]; exact hD) hbar)
          · have hc1 : cnt = none := by
              rcases hse with h | ⟨h, -, -⟩
              · exact h
              · exact absurd h hc128
            have hc2 : cnt2 = none := by
              rcases hse2 with h | ⟨-, h, -⟩
              · exact h
              · exact absurd h hw2D
            exact hne (hc1.trans hc2.symm)
    · -- the pending arrival is a worker's: the open generation is a loop generation
      have hgw : 128 ≤ g := by omega
      have hc1 : cnt = none := by
        rcases hse with h | ⟨-, h, -⟩
        · exact h
        · have := hwrange.mp h
          omega
      subst hc1
      have hn8 : n = CtaBarrier.warps L.block :=
        Except.ok.inj (hn.symm.trans htn)
      obtain ⟨hkk, -, hk4⟩ := hl.some_info k hk
      have hk4' : k = 4 := by
        rcases hkk with h | h
        · exact absurd (h.trans hn8.symm) hkn
        · exact h
      obtain ⟨-, hgam⟩ := hk4 hk4'
      have hwr : g / 32 ∈ Finset.range (CtaBarrier.warps L.block) := by
        simp only [Finset.mem_range, CtaBarrier.warps, hb256]
        omega
      have hearly := (hl.early (g / 32) hwr hlive).2 hgam
      have hoe : 2 ≤ ((X.tr e.1).take e.2).countP (Execution.isBarId 0) := by omega
      have hc2 : cnt2 = some 128 := by
        rcases hse2 with h | ⟨h, -, -⟩
        · subst h
          exfalso
          have := Except.ok.inj (htg.symm.trans htn)
          rw [hk4'] at this
          simp [hb256, CtaBarrier.warps] at this
        · exact h
      subst hc2
      have hw2D : w2 ∈ loopGroup := by
        rcases hse2 with h | ⟨-, h, -⟩
        · exact absurd h (by simp)
        · exact h
      have hg2d : g2 < 128 := by have := hwrange.mp hw2D; omega
      have hpass := hW hge (by rw [hmodE]; exact hgw) hbar hoe (by rw [hdivE, hdivE2])
        (by rw [hmodE2]; exact hg2d) hbar2
      have hg2 := NamedBar.gen_of_record (loopGroup_sub hpre) loopGroup_card
        (loopGroup_ne hpre) loopGroup_target hprot ha hp2 (.inl hw2D)
      obtain ⟨key, hk', hdone⟩ := ctaBarDone_of_returned hX hbar2 hpass
      have hkeq := NamedBar.D_arrival_key hX hSrc (loopGroup_sub hpre) loopGroup_card
        (loopGroup_ne hpre) loopGroup_target hb2 (by rw [hmodE2]; exact hwrange.mpr (by omega))
        (CtaBarK.arrival hk')
      have hmod : (0 + 16 * ((X.tr e2.1).take e2.2).countP (Execution.isBarId 0)) % 16 = 0 := by
        omega
      have hdiv : (0 + 16 * ((X.tr e2.1).take e2.2).countP (Execution.isBarId 0)) / 16 =
          ((X.tr e2.1).take e2.2).countP (Execution.isBarId 0) := by omega
      unfold CtaBarDone at hdone
      rw [hkeq, hmod, hdiv, hdivE2] at hdone
      have := CtaBarrier.released_generation_lt hrun hdone
      omega
  · -- every other barrier has no count: the counts agree
    have hc1 : cnt = none := by
      rcases bar_event_static hX hnb hbar with ⟨-, ⟨h1, -⟩ | ⟨h0, -⟩⟩
      · exact h1
      · exact absurd h0 hid
    have hc2 : cnt2 = none := by
      rcases bar_event_static hX hnb hbar2 with ⟨-, ⟨h1, -⟩ | ⟨h0, -⟩⟩
      · exact h1
      · exact absurd h0 hid
    subst hc1 hc2
    exact hkn (Except.ok.inj (htg.symm.trans hn))

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
