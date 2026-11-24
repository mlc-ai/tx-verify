-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Order

@[expose] public section

/-! # The accumulator ring's order

An MMA is its buffer's producer's, holding the buffer: its successful polls of the empty barrier
are one more than its accumulator commits before it, its batch `p` (`ThreadFacts.mma_acc_batch`).
A Tensor Memory load is a consumer's, holding its accumulator: its successful polls of its full
barrier are one more than its arrivals on the empty barrier before it, its tile `q`, and it is
followed by its wait (`ThreadFacts.cons_load`). When `p ≤ q` the consumer has polled the full
barrier more than `p` times, and the MMA is observed complete before the load
(`mma_before_load`); when `q < p` the producer has polled the empty barrier at least `q + 2`
times, and the load is finished before the MMA (`load_before_mma`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The accumulator ring is ordered** (`TmemOrdered`). -/
theorem tmemOrdered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : TmemOrdered L X := by
  intro g k h k' d s acc mask a vals sh hmma hld hcl hwj
  have hblock := hpre.block
  -- the MMA's side
  obtain ⟨pcm, hem⟩ := hmma
  have hg := Frame.lt_of_get hX hem
  obtain ⟨dm, hσm⟩ := Frame.event_state ht.sound hX ht.tracked hem (by simp)
  obtain ⟨hw89, hlead, hbatch⟩ := ht.mma_acc_batch hg hem hσm rfl
  set c := g / L.block / 2 with hc
  set j : Fin 2 := ⟨g % L.block / 32 % 2, Nat.mod_lt _ (by decide)⟩ with hj
  have hgc : g / L.block = 2 * c := by omega
  have hempty : Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, false⟩ =
      (slot L c j).empty 0 := by
    simp only [slot, hgc, hj]
  have hfull : Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩ =
      (slot L c j).full 0 := by
    simp only [slot, hgc, hj, Fin.val_zero, Nat.add_zero]
  rw [hempty, hfull] at hbatch
  have hprod : producerThread L c j g = true := by
    simp only [producerThread, decide_eq_true_eq, hj]
    omega
  obtain ⟨jp, pcp, pp, acqp, scp, -, hep⟩ := exists_okPoll (X := X) (g := g) (k := k)
    (m := (slot L c j).empty 0) (by omega)
  have hgp : g = producer L X c j := producer_eq hX ht hprod hep
  -- the load's side
  obtain ⟨pcl, hel⟩ := hld
  have hh := Frame.lt_of_get hX hel
  obtain rfl := ht.ld_shape hh hel
  obtain ⟨dl, hσl⟩ := Frame.event_state ht.sound hX ht.tracked hel (by simp)
  obtain ⟨hw8, htile, hwait⟩ := ht.cons_load hh hel hσl
  have hcl' : h / L.block / 2 = c := hcl
  have hwj' : h % L.block / 32 / 4 = j.val := hwj
  set b : Fin 256 := ⟨(h / L.block - 2 * c) * 128 + h % L.block % 128, by omega⟩ with hbdef
  have hb : consumerOf L c j b = h := consumerOf_of hcl' hwj'
  have hfull' : Bar.loc L (h / L.block) ⟨.acc, h % L.block / 32 / 4, true⟩ =
      (slot L c j).full ((slot L c j).owner b) := by
    have hcta : 2 * c + b.val / 128 = h / L.block := by simp only [hbdef]; omega
    show _ = Bar.loc L (2 * c + b.val / 128) ⟨.acc, j.val, true⟩
    rw [hcta, hwj']
  have hempty' : Bar.loc L (2 * (h / L.block / 2)) ⟨.acc, h % L.block / 32 / 4, false⟩ =
      (slot L c j).empty 0 := by
    simp only [slot, hcl', hwj']
  rw [hfull', hempty'] at htile
  rw [hempty', hfull]
  rw [← hb] at hel htile hwait ⊢
  rw [hgp] at hem hbatch ⊢
  have hR : X.TcAsync (producer L X c j, k) := .inl ⟨d, s, acc, mask, pcm, hem⟩
  have hsucc : ((X.tr (producer L X c j)).take (k + 1)).countP (commitsTo ((slot L c j).full 0)) =
      ((X.tr (producer L X c j)).take k).countP (commitsTo ((slot L c j).full 0)) := by
    rw [List.take_add_one, show (X.tr (producer L X c j))[k]? = _ from hem]
    simp [commitsTo]
  refine ⟨fun hpq => ?_, fun hqp => ?_⟩
  · exact mma_before_load hpre hX ht hR (len_of_get hel) (by rw [hsucc, htile]; omega)
  · exact load_before_mma hpre hX ht hel hwait (len_of_get hem) (by rw [← hbatch]; omega)

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
