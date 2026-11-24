-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaInputWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaInputOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Launch

public section

/-! # A pending MMA score wait finds an earlier softmax lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Protocol GemmRing

private theorem published_at_epilogue {q : Wg0.D} (hepi : q.site.inEpilogue = true) :
    Wg0GemmTrace.publishedBlocks q = q.block + 1 := by
  cases hSite : q.site <;> simp_all [Wg0GemmTrace.publishedBlocks, Wg0.Site.inEpilogue]

/-- A pending MMA input wait for scores has an earlier pending softmax lane. -/
theorem pending_mma_score_wait_earlier {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg1Mma.D}
    (hp : PendingState P L X g (.mma d)) (hRel : PTX.Step.Released L X g)
    (hd : d.site = .soWait) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧ priority P L h q < priority P L g (.mma d) := by
  have hX := hmax.1
  let cta := ctaOf L g
  let slot := rawSlot d.i
  let m := Object.soReady.loc L cta slot
  obtain ⟨lane, hShort⟩ :=
    pending_mma_wait_short (w := .score) hpre hmax hs ht hp.1 hRel hp.2 hd
  let h := softmax L cta lane
  change PTX.Flow.arrivals m (X.tr h) ≤ d.i / 2 at hShort
  have hl : lane.val < L.block := by rw [hpre.block]; exact lane.isLt.trans (by decide)
  have hh : h < L.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hp.1.1) hl
  have hc : ctaOf L h = cta := by
    change (cta * L.block + lane.val) / L.block = cta
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hl),
      Nat.div_eq_of_lt hl, Nat.zero_add]
  have hCta : SameCta L g h := ⟨hp.1.1, hh, hc.symm⟩
  have hWg : wgOf L h = 0 := softmax_wg0 hpre cta lane
  have hHub := Safety.no_ub hpre hX hs ht
  obtain ⟨t, htRun⟩ := Frame.run_some hX hHub hp.1
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hp.1.1 htRun hp.2
  have hMma : Wg1Mma.Inv P L g d := hInv
  have hBlock := hMma.i_lt (by rw [hd]; trivial)
  have hTotal : Wg1Mma.blocks P L g = Wg0.blocksOf P L h :=
    StageAfterPv.block_count_eq (P := P) (g := h) (h := g) hc.symm
  let hTrace := (hs h hh).machine.produces (hX.thr h hh)
  have hCount {i : Nat} {q : Wg0.D}
      (hq : Frame.stateAt (Machine.code P L) X h i = some (some (.wg0 q))) :
      PTX.Flow.arrivals m ((X.tr h).take i) =
        (Wg0GemmTrace.publishedBlocks q + (1 - slot.val)) / 2 := by
    have hz := Wg0GemmTrace.score_arrivals_of_state hpre slot hTrace hq
    rw [hc] at hz
    exact hz
  have noFinished {i : Nat} {q : Wg0.D} (hi : i ≤ (X.tr h).length)
      (hQ : Frame.stateAt (Machine.code P L) X h i = some (some (.wg0 q)))
      (hEpi : q.site.inEpilogue = true) (hI : Wg0.Inv P L h q) : False := by
    have hMono := countP_take_mono (arrivesOn m) (X.tr h) hi
    rw [List.take_length] at hMono
    change PTX.Flow.arrivals m ((X.tr h).take i) ≤ PTX.Flow.arrivals m (X.tr h) at hMono
    rw [hCount hQ, published_at_epilogue hEpi, hI.epilogueLast hEpi, ← hTotal] at hMono
    change (Wg1Mma.blocks P L g + (1 - d.i % 2)) / 2 ≤ _ at hMono
    omega
  have noClosing {i tag : Nat} (he : X.get (h, i) = some ⟨tag, .bar 12 none .sync⟩) : False := by
    obtain ⟨role, hState, hSite, _, _⟩ := ScoreClosingGate.closing_at hpre hX hs ht he
    rcases Wg0.state_of_wg hWg hTrace hState with ⟨s, rfl⟩ | ⟨q, rfl⟩ | rfl
    · exact hSite.elim
    · have hSite' : q.site = .everyone := hSite
      obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hState
      exact noFinished (PTX.len_of_get he).le hState (by simp [hSite', Wg0.Site.inEpilogue]) hInv
    · exact hSite.elim
  have hPending : Frame.Pending L X h := by
    refine ⟨hh, ?_, ?_⟩
    · rintro ⟨_, _, hCanceled⟩
      obtain ⟨i, spec, targets, _, hIssue, _⟩ := hX.clc.canceled_has_issue hCanceled
      exact GlobalWrites.no_clc (i := i) (s := spec) (tg := targets) hX hIssue
    · intro tag he
      rw [List.getLast?_eq_getElem?] at he
      obtain ⟨i, _, tag', hb⟩ := ClosingOrder.arrival_before_exit hpre hX hs ht he
      exact noClosing hb
  obtain ⟨q, hQ⟩ := pending_followed hpre hX hs ht hPending
  rcases Wg0.state_of_wg hWg hTrace hQ with ⟨s, rfl⟩ | ⟨p, rfl⟩ | rfl
  · refine ⟨h, .prologue s, hCta, ⟨hPending, hQ⟩, ?_⟩
    simp only [priority, matmulTime, hd, Bound.mmaOrdinal, blockTime]
    omega
  · obtain ⟨u, hRun⟩ := Frame.run_some hX hHub hPending
    obtain ⟨_, _, _, _, hInvP, _, _⟩ := Frame.end_at hs hh hRun hQ
    have hInvP : Wg0.Inv P L h p := hInvP
    cases hEpi : p.site.inEpilogue with
    | true => exact (noFinished le_rfl hQ hEpi hInvP).elim
    | false =>
      have hCnt := hCount hQ
      rw [List.take_length] at hCnt
      change PTX.Flow.arrivals m (X.tr h) =
        (Wg0GemmTrace.publishedBlocks p + (1 - d.i % 2)) / 2 at hCnt
      have hN : Wg0GemmTrace.publishedBlocks p ≤ d.i := by omega
      exact ⟨h, .wg0 p, hCta, ⟨hPending, hQ⟩, softmax_before_mma_wait hd hEpi hInvP.subLt hN⟩
  · obtain ⟨i, _, tag, hb⟩ :=
      ClosingOrder.arrival_before_state hpre hX (hs h hh).machine hh hQ (by trivial)
    exact (noClosing hb).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
