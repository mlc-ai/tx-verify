-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Cnt9
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Bar

@[expose] public section

/-! # The barrier-9 event after an odd number of barrier-9 events

A warpgroup-0 lane's barrier-9 events sit at pc 256 (`bar0`, even counts `2 r`), 569 (`bar2`,
`2 r + 1`), 1154 (`2 R`), 1156 (`2 R + 1`) and the output's four barriers (`2 R + 2` and more).
So a barrier-9 event after `2 r + 1` earlier ones, `r` at most the CTA's block count `R`, is at pc
569 or 1156. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem nine_site (s : Wg0.Site)
    (h : s.pc ∈ [256, 569, 1154, 1156, 1342, 1502, 1659, 1817]) :
    s = .bar0 ∨ s = .bar2 ∨ s = .ebar0 ∨ s = .ebar1 ∨ ∃ c, s = .obar c := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- **A barrier-9 event after `2 r + 1` barrier-9 events** (`r ≤ R`) is at pc 569 or 1156. -/
theorem wg0_bar9_odd (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc r : Nat} {kd : Kind}
    (he : X.get (g, k) = some ⟨pc, kd⟩) (hr : 103 ≤ pc ∧ pc < 1842)
    (hb : Execution.isBarId 9 ⟨pc, kd⟩ = true)
    (hcnt : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 1)
    (hrR : r ≤ blocksOf P L (g / L.block)) : pc = 569 ∨ pc = 1156 := by
  have hub : ∀ f, kd ≠ .ub f := fun f h => by subst h; simp [Execution.isBarId] at hb
  obtain ⟨d, hRf, ⟨hpc, hk⟩, hw⟩ := wg0_at hp hX hFw he hub hr
  obtain ⟨hC, hL, -, ht⟩ := hRf (wg0_take_noUb hX he)
  have hB : w0BarCnt X g k = Wg0.barOrd d := ht
  rw [w0_idCnt hp hX hFw hw (le_refl 9) (by omega) k (noUbBefore_of_get hX he), hB] at hcnt
  have hbar : Execution.isBar ⟨pc, kd⟩ = true := by
    revert hb; cases kd <;> simp [Execution.isBarId, Execution.isBar]
  simp only at hpc
  rcases Wg0.evK_bar hub hk hbar with ⟨hmem, -⟩ | ⟨-, hk2⟩ | ⟨-, hk2⟩
  · have hl2 : 2 ≤ d.site.lens := by
      rcases nine_site d.site hmem with h | h | h | h | ⟨c, h⟩ <;> rw [h] <;> simp [Wg0.Site.lens]
    have hepi : d.site.reg = Wg0.Reg.epi → Wg0.barOrd d = 3 * blocksOf P L (g / L.block) +
        d.site.bidx := fun hk => by
      have hR := Wg0.rounds_blocks hL hl2
      simp only [Wg0.barOrd, hk, hR]
    rcases nine_site d.site hmem with h | h | h | h | ⟨c, h⟩
    · obtain ⟨r', hrR', ho, -⟩ := barOrd_loop hC hL (by rw [h]; rfl) hl2
      simp only [h, Wg0.Site.bidx] at ho
      rw [ho, Nat.add_zero, w0Cnt9_loop _ _ _ hrR'.le] at hcnt
      omega
    · rw [h] at hpc
      exact .inl hpc
    · have ho := hepi (by rw [h]; rfl)
      simp only [h, Wg0.Site.bidx] at ho
      have h0 := w0Cnt9_epi (blocksOf P L (g / L.block)) (MbarRow.warp L g % 2) 0 (by omega)
      rw [ho] at hcnt
      simp only [Nat.add_zero] at hcnt h0
      omega
    · rw [h] at hpc
      exact .inr hpc
    · have ho := hepi (by rw [h]; rfl)
      simp only [h, Wg0.Site.bidx] at ho
      have hc4 := c.isLt
      have h0 := w0Cnt9_epi (blocksOf P L (g / L.block)) (MbarRow.warp L g % 2) (2 + c.val)
        (by omega)
      rw [ho] at hcnt
      omega
  · simp only at hk2
    subst hk2
    simp only [Execution.isBarId] at hb
    have := Wg0.barW_warp hp (g := g)
    simp only [beq_iff_eq] at hb
    omega
  · simp only at hk2
    subst hk2
    simp [Execution.isBarId] at hb
/-- **The events at pc 569 and 1156 are barrier-9 events.** -/
theorem wg0_bar9_of_pc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) (hpc : e.pc = 569 ∨ e.pc = 1156) :
    Execution.isBarId 9 e = true := by
  obtain ⟨d, -, ⟨hpc', hk⟩, -⟩ := wg0_at hp hX hFw he hub (by omega)
  have hmem : d.site.pc ∈ [256, 569, 1154, 1156, 1342, 1502, 1659, 1817] := by
    rw [← hpc']
    rcases hpc with h | h <;> rw [h] <;> decide
  obtain ⟨pc, kd⟩ := e
  rcases nine_site d.site hmem with h | h | h | h | ⟨c, h⟩ <;>
    simp only [Wg0.EvK, h] at hk <;> simp [Execution.isBarId, hk]

/-- **The stores of the exchange (pc 566, 1155) are no barrier-9 events.** -/
theorem wg0_store_notBar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 566 ∨ e.pc = 1155) :
    Execution.isBarId 9 e = false := by
  by_cases hub : ∀ f, e.kind ≠ .ub f
  swap
  · obtain ⟨u, hu⟩ := not_forall.mp hub
    obtain ⟨pc, kd⟩ := e
    obtain rfl : kd = .ub u := not_not.mp hu
    rfl
  obtain ⟨d, -, ⟨hpc', hk⟩, -⟩ := wg0_at hp hX hFw he hub (by omega)
  have hs : d.site = .mst ∨ d.site = .est := by
    have h2 : d.site.pc = 566 ∨ d.site.pc = 1155 := by rw [← hpc']; exact hpc
    revert h2
    generalize d.site = s
    cases s
    all_goals repeat' (rename_i x; fin_cases x)
    all_goals decide
  obtain ⟨pc, kd⟩ := e
  rcases hs with h | h <;> simp only [Wg0.EvK, h, WrAt] at hk <;>
    rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩ <;> simp [Execution.isBarId]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
