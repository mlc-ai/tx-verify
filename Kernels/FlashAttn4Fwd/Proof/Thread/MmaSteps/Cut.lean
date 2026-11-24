-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Base

@[expose] public section

/-! The two steps of asm block 2 (PV0 of a loop trip) that `site_cases` does not take: after
the block's last MMA, and after the inner P-ready poll of the lanes not elected, the local code
advances the next K use's slot; its wrap test is cut, and its predicate is a case. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The loop trip's state at the end of PV block 0. -/
abbrev dPv0 (i tr : Nat) (base : Value) (pro : Nat → Value) : D :=
  ⟨.mma 2 7, i, tr, base, pro⟩

/-- The lanes not elected for PV block 0, past its last two MMAs after the inner poll. -/
theorem seg_pv0skip (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) :
    Seg kernel asms L g 7 (Flow.mbarWait_18 + 1)
      ((5399, .pred true) :: facts L g ⟨.p2Wait 0 false, i, tr, base, pro⟩) (Flow.mma_23 + 1)
      (factsAt L g (Flow.mma_23 + 1) (dPv0 i tr base pro)) := by
  mma_close hpre hg

/-- After PV block 0: the next K use's slot increment, to its wrap test (`selp` on
`slot + 1 = 6`, cut as in `Ring.lean`). -/
theorem seg_pv0a (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) :
    Seg kernel asms L g 2 (Flow.mma_23 + 1)
      (factsAt L g (Flow.mma_23 + 1) (dPv0 i tr base pro)) (Flow.mma_23 + 3)
      (Flow.factsFrom (Flow.live (Flow.mma_23 + 3))
        (valueSel L g (dPv0 i tr base pro) 114
          (decide (kvSlot L i (1 + 2 * tr) + 1 = 6)))) := by
  intro t h
  mma_seg_s h hpre hg [valueSel]

/-- From the wrap test to the next K poll. -/
theorem seg_pv0b (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) (b : Bool) (hb : decide (kvSlot L i (1 + 2 * tr) + 1 = 6) = b) :
    Seg kernel asms L g 6 (Flow.mma_23 + 3)
      (Flow.factsFrom (Flow.live (Flow.mma_23 + 3))
        (valueSel L g (dPv0 i tr base pro) 114 b))
      (Site.kvWait 2).pc (facts L g ⟨.kvWait 2, i, tr, base, pro⟩) := by
  intro t h
  have hw : b = true ↔ (kvBase L i + (1 + 2 * tr)) % 6 = 5 := by
    rw [← hb]; simp [kvSlot, kvUse]
  cases b
  · have hw' : (kvBase L i + (1 + 2 * tr)) % 6 ≠ 5 := fun h => absurd (hw.mpr h) (by decide)
    mma_seg_s h hpre hg [valueSel, kvUse, xor_bit_zero (kvPar_lt L i (1 + 2 * tr))]
  · have hw' : (kvBase L i + (1 + 2 * tr)) % 6 = 5 := hw.mp rfl
    mma_seg_s h hpre hg [valueSel, kvUse, xor_bit_one (kvPar_lt L i (1 + 2 * tr))]

theorem stepOk_mma2_7 (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value}
    (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.mma 2 7, i, tr, base, pr⟩ :=
  Code.step_issue (dn := ⟨.kvWait 2, i, tr, base, pr⟩) Flow.code_mma_23
    (fun hf => fires_tcMmaTs hf) (fun _ => rfl) rfl rfl
    ⟨fun _ => ⟨_, Seg.weaken_start (Seg.comp (seg_pv0a hpre hg i tr base pr)
      (seg_pv0b hpre hg i tr base pr _ rfl))
      fun _ hR => Flow.holds_factsFrom_mono hR (by table_decide)⟩, rfl, rfl, by mma_inv⟩

theorem stepOk_p2Wait0_false (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value}
    (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.p2Wait 0 false, i, tr, base, pr⟩ :=
  Code.step_wait (dok := ⟨.kvWait 2, i, tr, base, pr⟩) (dfail := ⟨.p2Wait 0 false, i, tr, base, pr⟩)
    Flow.code_mbarWait_18 (by fact_free) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rfl rfl
    ⟨fun _ => ⟨_, Seg.comp (Seg.comp (seg_pv0skip hpre hg i tr base pr)
      (seg_pv0a hpre hg i tr base pr)) (seg_pv0b hpre hg i tr base pr _ rfl)⟩, rfl, rfl, by mma_inv⟩
    ⟨fun _ => by site_norm; seg_auto using mma_close hpre hg, rfl, rfl, by mma_inv⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
