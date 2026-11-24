-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaInputWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaInputOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReuseHistory

public section

/-! # A pending MMA dequantization wait finds an earlier dequantizer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Protocol GemmRing

/-- A pending MMA input wait for dequantization has an earlier pending producer lane. -/
theorem pending_mma_dequant_wait_earlier {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg1Mma.D}
    (hp : PendingState P L X g (.mma d)) (hRel : PTX.Step.Released L X g)
    (hd : d.site = .kvWait) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧ priority P L h q < priority P L g (.mma d) := by
  have hX := hmax.1
  let cta := ctaOf L g
  let slot := rawSlot d.i
  let m := full L cta slot
  obtain ⟨lane, hShort⟩ :=
    pending_mma_wait_short (w := .dequant) hpre hmax hs ht hp.1 hRel hp.2 hd
  let h := GemmRing.producer L cta lane
  change PTX.Flow.arrivals m (X.tr h) ≤ d.i / 2 at hShort
  have hl : 256 + lane.val < L.block := by
    have := lane.isLt
    rw [hpre.block]
    omega
  have hShape : h = cta * L.block + (256 + lane.val) := by
    change cta * L.block + 256 + lane.val = _
    omega
  have hh : h < L.threads := by
    rw [hShape]
    exact NamedBar.cta_thread_lt (NamedBar.cta_lt hp.1.1) hl
  have hc : ctaOf L h = cta := by
    change h / L.block = cta
    rw [hShape, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hl),
      Nat.div_eq_of_lt hl, Nat.zero_add]
  have hCta : SameCta L g h := ⟨hp.1.1, hh, hc.symm⟩
  have hWg : wgOf L h = 2 := producer_wg2 hpre cta lane
  have hHub := Safety.no_ub hpre hX hs ht
  obtain ⟨t, htRun⟩ := Frame.run_some hX hHub hp.1
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hp.1.1 htRun hp.2
  have hMma : Wg1Mma.Inv P L g d := hInv
  have hBlock := hMma.i_lt (by rw [hd]; trivial)
  have hTotal :
      totalBlocks (P.topkLen (Wg2.eOf L h)) (P.extraTopkLen (Wg2.eOf L h)) =
        Wg1Mma.blocks P L g := by
    rw [StageAfterPv.block_count_eq (P := P) (g := h) (h := g) hc.symm]
    rfl
  let hTrace := (hs h hh).machine.produces (hX.thr h hh)
  have hCount {i : Nat} {q : Wg2.D}
      (hq : Frame.stateAt (Machine.code P L) X h i = some (some (.wg2 q))) :
      PTX.Flow.arrivals m ((X.tr h).take i) =
        (Wg2GemmTrace.publishedBlocks q + (1 - slot.val)) / 2 := by
    have hz := Wg2GemmTrace.dequant_arrivals_of_state hpre slot hTrace hq
    rw [hc] at hz
    exact hz
  have noFinished {i : Nat} {q : Wg2.D} (hi : i ≤ (X.tr h).length)
      (hQ : Frame.stateAt (Machine.code P L) X h i = some (some (.wg2 q)))
      (hSite : q.site = .free)
      (hEnd : q.block + 1 =
        totalBlocks (P.topkLen (Wg2.eOf L h)) (P.extraTopkLen (Wg2.eOf L h))) : False := by
    have hMono := countP_take_mono (arrivesOn m) (X.tr h) hi
    rw [List.take_length] at hMono
    change PTX.Flow.arrivals m ((X.tr h).take i) ≤ PTX.Flow.arrivals m (X.tr h) at hMono
    rw [hCount hQ] at hMono
    simp only [Wg2GemmTrace.publishedBlocks, hSite, hEnd, hTotal] at hMono
    change (Wg1Mma.blocks P L g + (1 - d.i % 2)) / 2 ≤ _ at hMono
    omega
  have hPending : Frame.Pending L X h := by
    refine ⟨hh, ?_, ?_⟩
    · rintro ⟨_, _, hCanceled⟩
      obtain ⟨i, spec, targets, _, hIssue, _⟩ := hX.clc.canceled_has_issue hCanceled
      exact GlobalWrites.no_clc (i := i) (s := spec) (tg := targets) hX hIssue
    · intro tag he
      rw [List.getLast?_eq_getElem?] at he
      obtain ⟨i, _, q, _, hGet, hQ, hSite, hEnd⟩ :=
        Wg2ReuseHistory.last_free_before_exit hpre hX hs ht hWg he
      exact noFinished (PTX.len_of_get hGet).le hQ hSite hEnd
  obtain ⟨q, hQ⟩ := pending_followed hpre hX hs ht hPending
  have hRole := Wg2ReuseHistory.role_state hpre hX hs hh hWg hQ
  rcases hRole with ⟨s, rfl⟩ | ⟨p, rfl⟩ | rfl
  · refine ⟨h, .prologue s, hCta, ⟨hPending, hQ⟩, ?_⟩
    simp only [priority, matmulTime, hd, Bound.mmaOrdinal, blockTime]
    omega
  · by_cases hSite : p.site = .barrier
    · obtain ⟨i, _, r, _, hGet, hR, hFree, hEnd⟩ :=
        Wg2ReuseHistory.last_free_before_barrier_state hX hs ht hh le_rfl hQ hSite
      exact (noFinished (PTX.len_of_get hGet).le hR hFree hEnd).elim
    · have hCnt := hCount hQ
      rw [List.take_length] at hCnt
      change PTX.Flow.arrivals m (X.tr h) =
        (Wg2GemmTrace.publishedBlocks p + (1 - d.i % 2)) / 2 at hCnt
      have hN : Wg2GemmTrace.publishedBlocks p ≤ d.i := by omega
      exact ⟨h, .wg2 p, hCta, ⟨hPending, hQ⟩, dequant_before_mma_wait hd hSite hN⟩
  · obtain ⟨i, _, p, _, hGet, hR, hSite, hEnd⟩ :=
      Wg2ReuseHistory.last_free_before_done hpre hX hs ht hh le_rfl hWg hQ
    exact (noFinished (PTX.len_of_get hGet).le hR hSite hEnd).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
