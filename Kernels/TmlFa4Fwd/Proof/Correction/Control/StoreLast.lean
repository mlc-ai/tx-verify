-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.VectorStore
public import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreSpan
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S0H0J0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S0H1J0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S0H1J4
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S0H1J8
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S0H1J12
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S1H0J0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S1H1J0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S1H1J4
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S1H1J8
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreRows.S1H1J12
import Lemmas.Flow.LandsU

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof

private theorem store_span {p L g v} (st : Fin 2) (j : Fin 16) (h : Fin 2) :
    StoreSpan p L g v st j h := by
  by_cases hj : 4 ≤ j.val ∧ h = 0
  · obtain ⟨hj,rfl⟩ := hj
    exact store_span_copy hj
  fin_cases st <;> fin_cases h <;> fin_cases j
  · exact store_0_0_0
  · exact store_0_1_0
  · exact store_0_2_0
  · exact store_0_3_0
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact store_0_0_1
  · exact store_0_1_1
  · exact store_0_2_1
  · exact store_0_3_1
  · exact store_0_4_1
  · exact store_0_5_1
  · exact store_0_6_1
  · exact store_0_7_1
  · exact store_0_8_1
  · exact store_0_9_1
  · exact store_0_10_1
  · exact store_0_11_1
  · exact store_0_12_1
  · exact store_0_13_1
  · exact store_0_14_1
  · exact store_0_15_1
  · exact store_1_0_0
  · exact store_1_1_0
  · exact store_1_2_0
  · exact store_1_3_0
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact (hj ⟨by decide, rfl⟩).elim
  · exact store_1_0_1
  · exact store_1_1_1
  · exact store_1_2_1
  · exact store_1_3_1
  · exact store_1_4_1
  · exact store_1_5_1
  · exact store_1_6_1
  · exact store_1_7_1
  · exact store_1_8_1
  · exact store_1_9_1
  · exact store_1_10_1
  · exact store_1_11_1
  · exact store_1_12_1
  · exact store_1_13_1
  · exact store_1_14_1
  · exact store_1_15_1

theorem stepAt_fstU {p L g} (st : Fin 2) (j : Fin 16) (h : Fin 2) (k : Fin 4) (v : V) :
    (code p L g).StepAtU ⟨.fst st j h, v, k⟩ := by
  by_cases hk : k.val < 3
  · exact stepAt_fst_midU st j h k hk v
  have hk3 : k = 3 := by apply Fin.ext; change k.val = 3; omega
  subst k
  obtain ⟨a, hc, hs, hn, hl⟩ := vector_store st j h
  refine ⟨fun _ => ⟨_, hc, hl, trivial⟩, ?_⟩
  intro t e u ins hat _ hins hf
  obtain ⟨hpcAt, hsubAt, haccAt, hfaultAt, hregsAt⟩ := hat
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨_, _, rfl, rfl⟩ := fires_st hs hf
  rw [afterStore_last (by rw [hsubAt, hn]; change ¬ 3 + 1 < 4; decide)]
  obtain ⟨u, ht, hu⟩ := Code.landsU (C := code p L g) (d := ⟨afterStoreSite st j h, v, 0⟩)
    (u := { t with pc := t.pc + 1, sub := 0 })
    ⟨congrArg (· + 1) hpcAt, rfl, haccAt, hfaultAt, hregsAt⟩
    (store_span st j h) (.inl rfl) rfl rfl
  refine .inl (.inr ⟨_, u, ?_, ht, hu⟩)
  fin_cases h <;> by_cases hj : j.val = 15 <;>
    simp only [code, succ, Correction.succ, D.scheduler, afterStoreSite, hj, ↓reduceIte,
      V.scheduler, Correction.D.mk'] <;> rfl

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
