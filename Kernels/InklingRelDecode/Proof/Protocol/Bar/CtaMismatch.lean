-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedLanes
import Kernels.InklingRelDecode.Proof.Protocol.Bar.CtaWorker
import Kernels.InklingRelDecode.Proof.Protocol.Bar.Groups
import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
import Kernels.InklingRelDecode.Proof.Lib.NoBarArrive
import Kernels.InklingRelDecode.Proof.Lib.BarOne
public import Lemmas.Protocol.NamedBarMulti
import Lemmas.Protocol.NamedBarPhaseKeys
import Lemmas.Order.DependencyWitness
import Lemmas.Kernel.Frame

@[expose] public section

/-! # ERR-CTA-BARRIER: no count mismatch on named barrier 0

Barrier 0 serves three groups in turn: all eight warps (the two startup rendezvous), the four
data warps with the count 128 (`Export.barZeroSources`), and all eight warps again for the final
rendezvous. A fault is a pending `bar.sync` lane whose count differs from the open generation's
(`NamedBar.Multi.no_fault_of_mismatch`). With the phased ledger of the data group
(`NamedBar.phased_run`), the data lanes agree on the count of each ordinal (`alpha_agree`), and the
workers' final rendezvous follows every half-CTA rendezvous (`worker_late`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **No count mismatch on a named barrier.** -/
theorem bar_no_mismatch (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (safe : ¬ Race L X) :
    NamedBar.Multi.NoMismatch L X := by
  intro c hc s hrun id g pc k n cnt e hgb he1 hbar hfree hgx hndup hk hn hkn i u t w2 cnt2 lanes2
    g2 e2 hi ha hgen htg hp2 hm2
  have hb256 : L.block = 256 := hp.block
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
    have hSrc := Export.barZeroSources hp hX
    have hprot := hSrc.protocol hX hc
    have hl := NamedBar.phased_run (group_sub hp) (Finset.card_range _) (group_ne hp)
      group_target hprot hrun
    have hlive : CtaBarrier.warpLive L.block s.exited (g / 32) :=
      NamedBar.warpLive_of_lane hgb hgx
    have hlast : ¬ e.2 + 1 < (X.tr e.1).length :=
      barrier_unrecorded_last hX hbar (by rw [hdivE]; exact hfree)
    have hord := NamedBar.Multi.pending_ordinal hX hc hrun hgb he1 hbar hfree hgx
    have hse := hSrc e pc cnt ⟨.sync, hbar⟩ hge
    rw [hmodE] at hse
    obtain ⟨hql, hq2, hqw, -, hord2, hle2⟩ := NamedBar.record_ordinal hX hc hrun hi ha hm2
    simp only at hord2
    have hse2 := hSrc e2 pc2 cnt2 ⟨mode2, hb2⟩ hge2
    rw [hmodE2, ← hord2, hqw] at hse2
    have hne : cnt ≠ cnt2 := by
      rintro rfl
      exact hkn (Except.ok.inj (htg.symm.trans hn))
    have hwrange : ∀ {w : Nat}, w ∈ Finset.range 4 ↔ w < 4 := by
      intro w
      simp
    by_cases hD : g < 128
    · -- the pending arrival is a data warp's
      have hwD : g / 32 ∈ Finset.range 4 := hwrange.mpr (by omega)
      have hbal := hl.balD (g / 32) hwD hlive
      simp only [hndup, ↓reduceIte, Nat.add_zero] at hbal
      have hoe : ((X.tr e.1).take e.2).countP (Execution.isBarId 0) =
          (s.slots 0).generation := hord.trans hbal
      by_cases hw2D : w2 ∈ Finset.range 4
      · have hg2 := NamedBar.gen_of_record (group_sub hp) (Finset.card_range _) (group_ne hp)
          group_target hprot ha hp2 (.inl hw2D)
        have hg2d : g2 < 128 := by have := hwrange.mp hw2D; omega
        exact hne (alpha_agree hp hX hf safe (by rw [hdivE, hdivE2]) (by rw [hmodE]; exact hD)
          (by rw [hmodE2]; exact hg2d) hbar hb2 (by omega))
      · have hg2d : 128 ≤ g2 := by
          have := hwrange.not.mp hw2D
          omega
        by_cases hN2 : ((X.tr e2.1).take e2.2).countP (Execution.isBarId 0) < 2
        · have hg2 := NamedBar.gen_of_record (group_sub hp) (Finset.card_range _) (group_ne hp)
            group_target hprot ha hp2 (.inr (by omega))
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
            exact hlast (worker_late hp hX words (g := e2.1) (by rw [hmodE2]; exact hg2d) hb2
              hge2' (by rw [hdivE, hdivE2]) hbar)
          · have hc1 : cnt = none := by
              rcases hse with h | ⟨h, -, -⟩
              · exact h
              · exact absurd h hc128
            have hc2 : cnt2 = none := by
              rcases hse2 with h | ⟨-, h, -⟩
              · exact h
              · exact absurd h hw2D
            exact hne (hc1.trans hc2.symm)
    · -- the pending arrival is a worker's: the open generation is a data generation
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
      have hw2D : w2 ∈ Finset.range 4 := by
        rcases hse2 with h | ⟨-, h, -⟩
        · exact absurd h (by simp)
        · exact h
      have hg2d : g2 < 128 := by have := hwrange.mp hw2D; omega
      have hpass := worker_late hp hX words (g := e.1) (by rw [hmodE]; exact hgw) hbar hoe
        (by rw [hdivE, hdivE2]) hbar2
      have hg2 := NamedBar.gen_of_record (group_sub hp) (Finset.card_range _) (group_ne hp)
        group_target hprot ha hp2 (.inl hw2D)
      obtain ⟨key, hk', hdone⟩ := ctaBarDone_of_returned hX hbar2 hpass
      have hkeq := NamedBar.D_arrival_key hX hSrc (group_sub hp) (Finset.card_range _)
        (group_ne hp) group_target hb2 (by rw [hmodE2]; exact hwrange.mpr (by omega))
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
      rcases Lib.recorded_bar hX hb256 hbar with ⟨-, ⟨-, h, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩
      · exact h
      · exact absurd h0 hid
      · exact absurd h0 hid
    have hc2 : cnt2 = none := by
      rcases Lib.recorded_bar hX hb256 hbar2 with ⟨-, ⟨-, h, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩
      · exact h
      · exact absurd h0 hid
      · exact absurd h0 hid
    subst hc1 hc2
    exact hkn (Except.ok.inj (htg.symm.trans hn))

/-- **No CTA barrier arrival faults.** -/
theorem no_cta_bar_fault (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (safe : ¬ Race L X) : ¬ CtaBarFault L X :=
  NamedBar.Multi.no_fault_of_mismatch hX (bar_no_mismatch hp hX hf words safe)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
