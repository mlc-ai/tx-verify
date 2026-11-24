-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Bounds
public import Lemmas.Protocol.MbarRingBlocker

@[expose] public section

/-! # Who blocks an MMA warp at its accumulator-empty wait

The MMA warp of accumulator buffer `j` (warp `8 + j` of the leader CTA) polls buffer `j`'s empty
barrier before each tile. A failed poll of a barrier whose phase is not ready for its parity has
the barrier one phase behind the warp's successful polls (`acc_blocker`): the phase is at most
the producer's successful polls (`empty_phase_le`) and at least the phase its latest successful
poll found (`prod_poll_phase`). Then the barrier's 256 pending arrivals are not all in, and by
pigeonhole one consumer of the buffer has arrived exactly as many times as the barrier's phase
(`MbarRing.Blocker.units_lt`).
The polls of the barrier are one thread's, the polling lane of the warp (`mma_unique`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The accumulator-empty blocker.** An MMA thread `g` of warp `8 + j` of the leader CTA,
stopped at a failed poll of its buffer's empty barrier whose phase is not ready for its parity,
has polled successfully once more than the barrier's phase; and some consumer of the buffer has
arrived on the barrier exactly the barrier's phase many times. -/
theorem acc_blocker (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g : Nat} (hg : g < L.threads) {c : Nat} {j : Fin 2}
    (hc : g / L.block = 2 * c) (hw : g % L.block / 32 = 8 + j.val) {d : ThreadD}
    (hσp : Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some d))
    {pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hlast : (X.tr g).getLast? = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.acc, j.val, false⟩) p false acq sc⟩)
    {before : State}
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.acc, j.val, false⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.acc, j.val, false⟩)).length = some before)
    (hpar : before.phase % 2 = p % 2) :
    before.phase + 1 = okPolls (Bar.loc L (g / L.block) ⟨.acc, j.val, false⟩) (X.tr g) ∧
    ∃ b : Fin 256, Flow.arrivals (Bar.loc L (g / L.block) ⟨.acc, j.val, false⟩)
      (X.tr (consumerOf L c j b)) = before.phase := by
  classical
  have hblock := hpre.block
  have hE : Bar.loc L (g / L.block) ⟨.acc, j.val, false⟩ = (slot L c j).empty 0 := by
    rw [hc]
    rfl
  rw [hE] at hlast hstate ⊢
  have hch := X.objects_checked hX ((slot L c j).empty 0)
  have hni := objects_noInval hX ht ((slot L c j).empty 0)
  -- the failed poll is the last event, after the successful polls `ys`
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (X.tr g).length - 1 = ys.length := by
    rw [hys]
    simp
  have htake : (X.tr g).take ((X.tr g).length - 1) = ys := by
    rw [hlen, hys, List.take_left' rfl]
  have hok : okPolls ((slot L c j).empty 0) (X.tr g) = okPolls ((slot L c j).empty 0) ys := by
    rw [hys, okPolls_snoc]
    simp [okPoll, sourceWaitSuccess]
  have hget : X.get (g, (X.tr g).length - 1) = some
      ⟨pc, .wait ((slot L c j).empty 0) p false acq sc⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hj := j.isLt
  have hpoll := ht.poll_parity (b := ⟨.acc, j.val, false⟩) (cta := 2 * c) hg hget hσp rfl hj
  have hpoll' : p % 2 = (okPolls ((slot L c j).empty 0) (X.tr g) + 1) % 2 := by
    rw [hok, ← htake]
    exact hpoll
  have hgsel : producerThread L c j g = true := by
    simp only [producerThread, decide_eq_true_eq]
    exact ⟨hc, hw⟩
  have hle := empty_phase_le hpre hX ht hstate
  -- the polling thread is the producer
  have hgp : g = producer L X c j := by
    by_cases hN : 0 < okPolls ((slot L c j).empty 0) (X.tr g)
    · obtain ⟨jj, pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := g)
        (k := (X.tr g).length) (m := (slot L c j).empty 0) (by rw [List.take_length]; exact hN)
      exact producer_eq hX ht hgsel he'
    · by_cases hM : 0 < okPolls ((slot L c j).empty 0) (X.tr (producer L X c j))
      · obtain ⟨jj, pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X)
          (g := producer L X c j) (k := (X.tr (producer L X c j)).length)
          (m := (slot L c j).empty 0) (by rw [List.take_length]; exact hM)
        have hps := producer_thread (X := X) hpre c j
        simp only [producerThread, decide_eq_true_eq] at hps
        exact mma_unique hX ht (hc.trans hps.1.symm) (hw.trans hps.2.symm) (by omega) hget he'
          rfl rfl
      · omega
  rw [← hgp] at hle
  set N := okPolls ((slot L c j).empty 0) (X.tr g) with hNdef
  -- the latest successful poll found phase `N - 1`
  have hge : N - 1 ≤ before.phase := by
    rcases Nat.lt_or_ge N 2 with h2 | h2
    · omega
    have hlt : N - 1 < okPolls ((slot L c j).empty 0) (X.tr (producer L X c j)) := by
      rw [← hgp]; omega
    obtain ⟨k, w, hk, -, -, -, st, hst, hph⟩ := prod_poll_phase hpre hX ht (n := N - 1) (by omega)
      hlt
    obtain ⟨s2, hs2, hmono⟩ := hch.phase_mono hni (List.getElem?_eq_some_iff.mp hk).1.le le_rfl hst
    rw [hstate] at hs2
    cases hs2
    omega
  have hT : before.phase + 1 = N := by omega
  refine ⟨hT, ?_⟩
  -- every consumer arrived at least `before.phase` times
  have hlo : ∀ b : Fin 256, before.phase ≤
      Flow.arrivals ((slot L c j).empty 0) (X.tr (consumerOf L c j b)) := by
    intro b
    rcases Nat.eq_zero_or_pos before.phase with h0 | hpos
    · omega
    have hpres : X.RefPresent (.thread ((ring hpre hX ht c j).wE 0 (before.phase - 1 + 1))) := by
      refine (MbarRing.Poll.nth_present (X := X)).mpr ?_
      rw [← hgp]
      omega
    obtain ⟨hy, -⟩ := ((ring hpre hX ht c j).content_empty hX.depAcyclic hpres).2 b
    obtain ⟨pca, rel, sca, he, hcnt⟩ := emptyItems_arrive hX ht hy
    have h1 := countP_take_succ (p := arrivesOn ((slot L c j).empty 0)) he (by simp [sourceArrive])
    have h2 := countP_take_mono (p := arrivesOn ((slot L c j).empty 0)) (X.tr (consumerOf L c j b))
      (show arriveAt L X c j b (before.phase - 1) + 1 ≤ (X.tr (consumerOf L c j b)).length from
        len_of_get he)
    rw [List.take_length] at h2
    change arrivals _ _ = _ at hcnt
    unfold arrivals at hcnt ⊢
    simp only at hcnt h1
    omega
  by_contra hne
  push Not at hne
  have hge' : ∀ b : Fin 256, before.phase + 1 ≤
      Flow.arrivals ((slot L c j).empty 0) (X.tr (consumerOf L c j b)) := fun b => by
    have := hlo b
    have := hne b
    omega
  -- then the barrier has `256 · (phase + 1)` counted arrivals, completing its phase
  let T : Finset (Fin 256 × Nat) := allCons ×ˢ Finset.range (before.phase + 1)
  have hTS : ∀ y ∈ T, y ∈ emptyItems L X c j := fun y hy => by
    obtain ⟨-, hy2⟩ := Finset.mem_product.mp hy
    have := hge' y.1
    exact emptyItems_of_arrival hpre hX ht (by rw [Finset.mem_range] at hy2; omega)
  have hcard := card_le_positions (log := X.objects ((slot L c j).empty 0)) T
    (fun y => arriveRef L X c j y.1 y.2)
    ((arriveRef_inj hpre hX ht).mono (fun y hy => hTS y hy))
    ((Finset.range (X.objects ((slot L c j).empty 0)).length).filter
      (fun i => ((X.objects ((slot L c j).empty 0))[i]?).any isArrival = true))
    (fun y hy => by
      obtain ⟨i, r, hi, hid, harr⟩ := emptyItems_record hX ht (hTS y hy)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1,
        by simp [hi, harr]⟩, r, hi, hid⟩)
  rw [← units_card hX ht (m := (slot L c j).empty 0) (j := j) (cta := 2 * c) (f := false)
    rfl] at hcard
  have hTc : T.card = 256 * (before.phase + 1) := by
    rw [Finset.card_product, card_allCons, Finset.card_range]
  have hlt := MbarRing.Blocker.units_lt hch hni hstate (tx_zero_acc (cta := 2 * c) (f := false)
    hX ht hstate)
  have hexp := expected_eq (cta := 2 * c) (f := false) hpre hX ht _ before hstate
  change before.expected = 256 at hexp
  rw [hexp] at hlt
  rw [unitsBefore, List.take_length] at hcard
  have hinc := incrementsBefore_zero hX ht ((slot L c j).empty 0)
  omega

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
