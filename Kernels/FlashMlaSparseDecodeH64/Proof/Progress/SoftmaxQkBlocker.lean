-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.SoftmaxQkWait
public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarUnitFaults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0GemmPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarPublished
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryMmaCandidate
import Lemmas.Protocol.NotifyBlocker

public section

/-! # Descending from a missing QK issue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow AsyncCopy MBarrier Protocol GemmRing PTX.MbarRing
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 4096

set_option linter.unusedSimpArgs false in
private theorem mma_before_qk_wait {g h : Nat} {d : Wg0.D} {q : Wg1Mma.D}
    (hd : d.site = .qkDone) (hq : q.site ≠ .outBar) (hExit : q.site ≠ .exit)
    (hProgress : q.i < d.block ∨
      q.i = d.block ∧ Wg1MmaGemmTrace.completed .qk q.site = false) :
    priority P L h (.mma q) < priority P L g (.wg0 d) := by
  cases hSite : q.site
  all_goals try exact (hq hSite).elim
  all_goals try exact (hExit hSite).elim
  all_goals
    simp only [priority, softmaxTime, matmulTime, hd, hSite, wg0Ordinal, mmaOrdinal,
      Wg1MmaGemmTrace.completed, Bool.true_eq_false, and_false, or_false, blockTime] at hProgress ⊢
    omega

private theorem qk_issue_wait_earlier (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g issuer : Nat} {d : Wg0.D}
    (hp : PendingState P L X g (.wg0 d)) (hd : d.site = .qkDone)
    (hIssuer : MmaIssuer P L X (ctaOf L g) issuer)
    (hShort : (X.tr issuer).countP (commitsTo (qk L (ctaOf L g) (rawSlot d.block))) ≤ d.block / 2) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧
      priority P L h q < priority P L g (.wg0 d) := by
  let cta := ctaOf L g
  let slot := rawSlot d.block
  let m := qk L cta slot
  let sound := fun h hh => (hs h hh).machine
  have hc := NamedBar.cta_lt hp.1.1
  obtain ⟨lane, _, _, hTail⟩ := QueryMmaCandidate.select_mma (cta := cta) hpre hX hs ht
    (fun _ h => pending_followed hpre hX hs ht h) hc
  let h := cta * L.block + 128 + lane.val
  obtain ⟨hh, hCta, _, _⟩ := QueryMmaCandidate.lane_geometry hpre hc lane
  change ctaOf L h = cta at hCta
  have hSameCta : SameCta L g h := ⟨hp.1.1, hh, hCta.symm⟩
  have hHub := Safety.no_ub hpre hX hs ht
  obtain ⟨t, hRun⟩ := Frame.run_some hX hHub hp.1
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hp.1.1 hRun hp.2
  have hInv : Wg0.Inv P L g d := hInv
  have hBlocks := hInv.blockLt
  have hTotal : Wg1Mma.blocks P L h = Wg0.blocksOf P L g :=
    StageAfterPv.block_count_eq (P := P) (g := g) (h := h) hCta
  let hTrace := (sound h hh).produces (hX.thr h hh)
  have hShortAt {q : Wg1Mma.D} {i : Nat} (hi : i ≤ (X.tr h).length)
      (hQ : Frame.stateAt (Machine.code P L) X h i = some (some (.mma q)))
      (hSite : q.site ≠ .elect) :
      (q.i + (1 - d.block % 2)) / 2 +
        (if q.i % 2 = d.block % 2 ∧ Wg1MmaGemmTrace.completed .qk q.site then 1 else 0) ≤
        d.block / 2 := by
    have hId := hIssuer h i q hCta hQ hSite
    have hCount := Wg1MmaGemmTrace.qk_commits_of_state hpre hh slot hTrace hQ
    change ((X.tr h).take i).countP
      (commitsTo (qk L (ctaOf L h) slot)) = _ at hCount
    rw [hCta] at hCount
    have hMono := countP_take_mono (commitsTo m) (X.tr h) hi
    rw [List.take_length] at hMono
    have hSmall : (X.tr h).countP (commitsTo m) ≤ d.block / 2 := by
      rw [hId]
      exact hShort
    rw [hCount] at hMono
    exact hMono.trans hSmall
  have noExitState {j : Nat} {p : Wg1Mma.D} (hj : j ≤ (X.tr h).length)
      (hP : Frame.stateAt (Machine.code P L) X h j = some (some (.mma p)))
      (hExit : p.site = .exit) : False := by
    obtain ⟨i, _, e, q, he, hQ, hOut⟩ :=
      ClosingOrder.mma_out_bar_before_exit_state hpre ht hh hj hP hExit
    obtain ⟨_, _, _, _, hI, _, _⟩ := Frame.fired_site hs hX he hQ
    have hI : Wg1Mma.Inv P L h q := hI
    have hN := hShortAt (PTX.len_of_get he).le hQ (by simp [hOut])
    simp only [hOut, Wg1MmaGemmTrace.completed, Bool.false_eq_true, and_false, ↓reduceIte,
      Nat.add_zero, hI.end_i hOut, hTotal] at hN
    omega
  rcases hTail with ⟨i, tag, q, he, hState, hSite⟩ | ⟨q, hPending, hQ, hActive⟩
  · exact (noExitState (PTX.len_of_get he).le hState hSite).elim
  · refine ⟨h, q, hSameCta, ⟨hPending, hQ⟩, ?_⟩
    cases hActive with
    | launch s =>
      simp only [priority, softmaxTime, hd, wg0Ordinal, blockTime]
      omega
    | dispatch =>
      simp only [priority, softmaxTime, hd, wg0Ordinal, blockTime]
      omega
    | mma p =>
      by_cases hElect : p.site = .elect
      · simp only [priority, softmaxTime, matmulTime, hd, hElect, mmaOrdinal, wg0Ordinal, blockTime]
        omega
      have hN := hShortAt le_rfl hQ hElect
      have hP : p.i < d.block ∨
          p.i = d.block ∧ Wg1MmaGemmTrace.completed .qk p.site = false := by
        by_cases hEarlier : p.i < d.block
        · exact .inl hEarlier
        right
        have hpBlock : p.i = d.block := by split at hN <;> omega
        refine ⟨hpBlock, ?_⟩
        rw [hpBlock] at hN
        simp only [true_and] at hN
        split at hN
        · omega
        · simpa only [Bool.not_eq_true] using ‹¬ Wg1MmaGemmTrace.completed .qk p.site = true›
      have hnExit : p.site ≠ .exit := noExitState le_rfl hQ
      have hnOut : p.site ≠ .outBar := by
        intro hOut
        obtain ⟨v, hRun⟩ := Frame.run_some hX hHub hPending
        obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hh hRun hQ
        have hInv : Wg1Mma.Inv P L h p := hInv
        have hend := (hInv.end_i hOut).trans hTotal
        rcases hP with hlt | ⟨heq, _⟩ <;> omega
      exact mma_before_qk_wait hd hnOut hnExit hP

/-- A missing QK publication identifies either an earlier issuer state or an unfinished
operation tracked by the exact QK commit. -/
theorem pending_softmax_qk_blocker (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg0.D} (hp : PendingState P L X g (.wg0 d))
    (hRel : PTX.Step.Released L X g) (hd : d.site = .qkDone) :
    (∃ h q, SameCta L g h ∧ PendingState P L X h q ∧
      priority P L h q < priority P L g (.wg0 d)) ∨
    (∃ i op sp, X.Commit i sp ∧ TcCommit.target sp 0 = some (qk L (ctaOf L g) (rawSlot d.block)) ∧
      TracksMma X op i ∧ X.async.mmaDone op = false) := by
  classical
  obtain ⟨issuer, hIssuer, hShort | ⟨sp, hi, hTarget, hMissing⟩⟩ :=
    pending_softmax_qk_missing hpre hmax hs ht hp hRel hd
  · exact .inl (qk_issue_wait_earlier hpre hmax.1 hs ht hp hd hIssuer hShort)
  · right
    by_contra hNone
    apply hMissing (completed_commit_notified hpre hmax hs
      ht hi hTarget ?_)
    intro op hop
    cases hDone : X.async.mmaDone op
    · exact (hNone ⟨_, op, sp, hi, hTarget, hop, hDone⟩).elim
    · rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
