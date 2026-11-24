-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.lead_lt

@[expose] public section

/-! One step of `ConsumerEntry`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- From the tile test (the instruction after the group barrier's branch on the first thread),
the claimed tile is set in the next-tile registers and the accumulator poll is reached. -/
theorem tile_seg {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {s : Site}
    {m n m' n' cp ap : Nat} {resp : Value} {x : Nat} {acc : Nat → Value} {base : Value} {t : TState}
    (hpre : Pre P L mem0) (hi : Inv ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩)
    (h : At t (Flow.bra_721 + 8)
      (factsAt L g (Flow.bra_721 + 8) ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩)) :
    ∃ k t', run kernel Prod L g k t = some t' ∧
      At t' Site.accWait.pc (facts L g ⟨.accWait, m, n,
        (nextTile ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩).1,
        (nextTile ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩).2, cp, ap, resp, x, acc, base⟩) :=
          by
  have hm : m < 16 := hi.1
  have hn : n < 32 := hi.2
  have hx : x < 2 ^ 32 := hi.7
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  -- the three moves after the group's branch, then the test for the claimed CTA
  obtain ⟨tA, hrA, htA⟩ : ∃ tA, run kernel Prod L g 3 t = some tA ∧
      At tA Flow.bra_732 ((9, .pred (decide (x = Loader.none32))) :: (892, b32 m) ::
        (891, b32 n) :: Flow.factsFrom
          ((((Flow.live Flow.bra_732).erase 9).erase 891).erase 892)
          (valueOf L g ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩)) := by
    cons_seg h hpre
  have hp9 : tA.regs 9 = some (.pred (decide (x = Loader.none32))) :=
    holds_mem htA.2.2.2.2 (List.mem_cons.mpr (Or.inl rfl))
  by_cases hnone : x = Loader.none32
  · -- no claimed CTA: the tile is the current one
    have hd : decide (x = Loader.none32) = true := by simp [hnone]
    obtain ⟨t1, hr1, ht1⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_732
      (decide (x = Loader.none32)) htA hp9 (prod_localRule_bra L g _ _ _)
    rw [hd] at ht1
    simp only [↓reduceIte] at ht1
    obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel Prod L g 2 t1 = some t2 ∧
        At t2 Site.accWait.pc (facts L g ⟨.accWait, m, n, m, n, cp, ap, resp, x, acc, base⟩) := by
      cons_seg ht1 hpre [cmp_ne_zero (tidOf L g / 32 % 4 ||| tidOf L g % 32) (lead_lt (tidOf L g))]
    have hnt : nextTile ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ = (m, n) := by
      simp [nextTile, hnone]
    refine ⟨_, t2, run_comp (run_comp hrA hr1) hr2, ?_⟩
    rw [hnt]
    exact ht2
  · have hd : decide (x = Loader.none32) = false := by simp [hnone]
    obtain ⟨t1, hr1, ht1⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_732
      (decide (x = Loader.none32)) htA hp9 (prod_localRule_bra L g _ _ _)
    rw [hd] at ht1
    simp only [Bool.false_eq_true, ↓reduceIte] at ht1
    -- the two moves and the test for a claimed CTA beyond the grid
    obtain ⟨tB, hrB, htB⟩ : ∃ tB, run kernel Prod L g 3 t1 = some tB ∧
        At tB Flow.bra_736 ((10, .pred (decide (x > 1023))) :: (892, b32 0) ::
          (891, b32 0) :: Flow.factsFrom
            ((((Flow.live Flow.bra_736).erase 10).erase 891).erase 892)
            (valueOf L g ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩)) := by
      cons_seg ht1 hpre
    have hp10 : tB.regs 10 = some (.pred (decide (x > 1023))) :=
      holds_mem htB.2.2.2.2 (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨t3, hr3, ht3⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_736
      (decide (x > 1023)) htB hp10 (prod_localRule_bra L g _ _ _)
    by_cases hbig : x > 1023
    · have hd' : decide (x > 1023) = true := by simp [hbig]
      rw [hd'] at ht3
      simp only [↓reduceIte] at ht3
      obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel Prod L g 2 t3 = some t4 ∧
          At t4 Site.accWait.pc (facts L g ⟨.accWait, m, n, 0, 0, cp, ap, resp, x, acc, base⟩) := by
        cons_seg ht3 hpre [cmp_ne_zero (tidOf L g / 32 % 4 ||| tidOf L g % 32)
          (lead_lt (tidOf L g))]
      have hnt : nextTile ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ = (0, 0) := by
        simp [nextTile, Loader.claimM, Loader.claimN, hnone, hbig]
      refine ⟨_, t4, run_comp (run_comp (run_comp (run_comp hrA hr1) hrB) hr3) hr4, ?_⟩
      rw [hnt]
      exact ht4
    · have hd' : decide (x > 1023) = false := by simp [hbig]
      rw [hd'] at ht3
      simp only [Bool.false_eq_true, ↓reduceIte] at ht3
      have hx' : x < 1024 := by omega
      obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel Prod L g 9 t3 = some t4 ∧
          At t4 Site.accWait.pc (facts L g ⟨.accWait, m, n, x / 512 % 2 * 8 + x / 2 % 8,
            x / 16 % 32,
            cp, ap, resp, x, acc, base⟩) := by
        cons_seg ht3 hpre [Loader.claim_bits x hx', claimN_bits x hx',
          cmp_ne_zero (tidOf L g / 32 % 4 ||| tidOf L g % 32) (lead_lt (tidOf L g))]
      have hnt : nextTile ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ =
          (x / 512 % 2 * 8 + x / 2 % 8, x / 16 % 32) := by
        simp [nextTile, Loader.claimM, Loader.claimN, hnone, hbig]
      refine ⟨_, t4, run_comp (run_comp (run_comp (run_comp hrA hr1) hrB) hr3) hr4, ?_⟩
      rw [hnt]
      exact ht4

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
