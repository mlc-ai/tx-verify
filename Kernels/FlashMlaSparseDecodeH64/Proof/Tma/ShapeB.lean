-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ev
public import Lemmas.Flow.Step.ShapeClasses
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The TMA warp's shape obligations in a block: reads, gathers, arrivals

The coordinate elements read their words (`fires_rd_at`) or fault; a gather issues on the raw
tile's `raw_ready` word or faults; the two arrivals are on `raw_ready` with `expect_tx 36864`
and on `valid_coord_free` (words that are multiples of 8 whatever the slots, `Lib/Mod8.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_coord (d : D)
    (hs : ∃ k, d.site = .coord0 k ∨ d.site = .coord1 k ∨ d.site = .coord2 k ∨ d.site = .coord3 k) :
    (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  obtain ⟨k, hs | hs | hs | hs⟩ := hs <;> cases hs <;> fin_cases k <;> tma_openS <;>
    change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf <;>
    exact fires_rd_at (rg 782) (by decide) rfl hsub hf

theorem shapeAt_gather (hp : Pre P L m) (d : D) (hs : ∃ k, d.site = .gather k) :
    (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  obtain ⟨k, hs⟩ := hs
  cases hs
  fin_cases k <;> tma_open <;>
    exact shape_cpTensor (P := fun e : Event => (∃ a s, e.kind = .tensorIssue a s ∧
      s.mbar = smLoc L g (rawW L ⟨.gather 0, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩) 0) ∨
        ∃ f, e.kind = .ub f)
      hf (fun a s h => Or.inl ⟨a, s, rfl, by
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        rw [mbarLoc_bits (rg 696) (al8 (m8_addi (m8_tileB hp _) (by decide)))] at h
        exact (Except.ok.inj h).symm⟩) (fun f => Or.inr ⟨f, rfl⟩)

theorem shapeAt_rawArrive (hp : Pre P L m) (d : D) (hs : d.site = .rawArrive) :
    (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  cases hs
  tma_open
  exact shape_arrive (P := fun e : Event => e.kind = .arrive (smLoc L g (rawW L
      ⟨.rawArrive, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩) 0)
      36864 1 true .cta)
    hf (by rw [hpc]; decide) (readBits_reg (rg 772)) rfl
    (mbarLoc_bits (rg 696) (al8 (m8_addi (m8_tileB hp _) (by decide)))) rfl

theorem shapeAt_coordFree (hp : Pre P L m) (d : D) (hs : d.site = .coordFree) :
    (code P L g).ShapeAt (EvK L g) d := by
  tma_state d
  cases hs
  tma_open
  exact shape_arrive (P := fun e : Event => e.kind = .arrive (smLoc L g (cfreeW L
      ⟨.coordFree, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩) 0)
      0 1 true .cta)
    hf (by rw [hpc]; decide) rfl rfl
    (mbarLoc_bits (rg 773) (al8 (m8_addi (m8_mad32 (m8_i32 (by decide))
      (m8_mad32 (m8_i32 (by decide)) (m8_ringB hp _))) (by decide)))) rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
