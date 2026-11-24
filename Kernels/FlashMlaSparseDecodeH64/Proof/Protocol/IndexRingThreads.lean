-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue

@[expose] public section

/-! # Threads participating in one CTA's index ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingThreads

open PTX

/-- All 32 lanes of warp 7 publish each index slot. -/
def producerThread (L : Launch) (cta : Nat) (lane : Fin 32) : Nat :=
  cta * L.block + 224 + lane.val

/-- The releases come from warpgroup 0 and the chosen lane of the TMA warp. -/
def consumerThread (L : Launch) (cta : Nat) (tmaLane : Fin 32) (consumer : Fin 129) : Nat :=
  cta * L.block + if consumer.val < 128 then consumer.val else 160 + tmaLane.val

theorem producerThread_injective (L : Launch) (cta : Nat) :
    Function.Injective (producerThread L cta) := by
  intro a b h
  apply Fin.ext
  unfold producerThread at h
  omega

theorem consumerThread_injective (L : Launch) (cta : Nat) (tmaLane : Fin 32) :
    Function.Injective (consumerThread L cta tmaLane) := by
  intro a b h
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  unfold consumerThread at h
  split_ifs at h <;> omega

variable {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
include hpre

theorem producerThread_facts {cta : Nat} (hcta : cta < L.grid) (p : Fin 32) :
    producerThread L cta p < L.threads ∧ ctaOf L (producerThread L cta p) = cta ∧
      warpOf L (producerThread L cta p) = 7 := by
  have hp := p.isLt
  simp only [producerThread, Launch.threads, ctaOf, warpOf, tidOf_eq hpre, hpre.block]
  omega

theorem consumerThread_facts {cta : Nat} (hcta : cta < L.grid) (tmaLane : Fin 32) (q : Fin 129) :
    consumerThread L cta tmaLane q < L.threads ∧
      ctaOf L (consumerThread L cta tmaLane q) = cta := by
  have hl := tmaLane.isLt
  simp only [consumerThread, Launch.threads, ctaOf, hpre.block]
  split_ifs <;> omega

/-- A warp-7 thread of the CTA has its lane's producer index. -/
theorem producer_of_warp {g cta : Nat} (hc : ctaOf L g = cta) (hw : warpOf L g = 7) :
    ∃ lane : Fin 32, g = producerThread L cta lane := by
  refine ⟨⟨g % 32, Nat.mod_lt _ (by decide)⟩, ?_⟩
  simp only [ctaOf, hpre.block] at hc
  simp only [warpOf, tidOf_eq hpre] at hw
  simp only [producerThread, hpre.block]
  omega

/-- A warpgroup-0 thread of the CTA is one of its first 128 consumers. -/
theorem consumer_of_wg0 {g cta : Nat} (hc : ctaOf L g = cta) (hw : wgOf L g = 0) (tmaLane : Fin 32)
    :
    ∃ q : Fin 129, q.val < 128 ∧ g = consumerThread L cta tmaLane q := by
  simp only [ctaOf, hpre.block] at hc
  simp only [wgOf, tidOf_eq hpre] at hw
  have hg : g % 384 < 128 := by omega
  refine ⟨⟨g % 384, by omega⟩, hg, ?_⟩
  simp only [consumerThread, hpre.block, hg, ↓reduceIte]
  omega

/-- The elected lane of warp 5 is the remaining consumer. -/
theorem consumer_of_elected {g cta : Nat} (hc : ctaOf L g = cta) (hw : warpOf L g = 5)
    (tmaLane : Fin 32) (hl : laneOf L g = tmaLane.val) :
    g = consumerThread L cta tmaLane ⟨128, by decide⟩ := by
  simp only [ctaOf, hpre.block] at hc
  simp only [warpOf, tidOf_eq hpre] at hw
  simp only [laneOf, tidOf_eq hpre] at hl
  simp [consumerThread, hpre.block]
  omega

theorem sameCta {cta : Nat} (hc : cta < L.grid) (tmaLane : Fin 32) (p : Fin 32) (q : Fin 129) :
    SameCta L (producerThread L cta p) (consumerThread L cta tmaLane q) := by
  obtain ⟨hp, hcp, _⟩ := producerThread_facts hpre hc p
  obtain ⟨hq, hcq⟩ := consumerThread_facts hpre hc tmaLane q
  exact ⟨hp, hq, hcp.trans hcq.symm⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingThreads
