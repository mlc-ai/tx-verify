-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetimeCompletion
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaGemmTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Lemmas.Protocol.UnitNotify
import Lemmas.Protocol.ObservedSync
import Lemmas.Protocol.NamedBarSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmScoreRing
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0GemmTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GemmTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReuseHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmDequantRing

public section

/-! # QK notifications observed by the closing softmax lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime

open PTX PTX.Flow PTX.AsyncCopy PTX.MbarRing Protocol GemmRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem counted_commit (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {g i : Nat} {d : Wg1Mma.D} {sp : TcCommit.Spec} {m : Loc} {rank : Fin 16}
    (stream : Wg1MmaGemmTrace.Stream)
    (hSite : (stream = .qk ∧ d.site = .qkCommit) ∨ (stream = .pv ∧ d.site = .pvCommit))
    (hi : X.Commit (g, i) sp)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hTarget : TcCommit.target sp rank = some m) :
    Notify.it X m g m (d.i / 2) = .async (g, i) (.tcNotify rank) := by
  have hg := Frame.lt_of_get hX hi.choose_spec
  have htrace := (hs g hg).machine.produces (hX.thr g hg)
  obtain ⟨_, hf⟩ := htrace.fired_at hi.choose_spec hd
  obtain ⟨hm, q, hEq, hCase⟩ := RingCommitEvents.commit_source hpre hg hf rfl hTarget
  obtain rfl := Machine.ThreadD.mma.inj hEq
  let slot := rawSlot d.i
  have hAddr : m = stream.loc L g slot := by
    rcases hSite with ⟨rfl, hK⟩ | ⟨rfl, hK⟩
    · rcases hCase with ⟨hQ, _⟩ | ⟨_, ha⟩ | ⟨hP, _⟩
      · rw [hK] at hQ
        cases hQ
      · exact ha
      · rw [hK] at hP
        cases hP
    · rcases hCase with ⟨hQ, _⟩ | ⟨hQ, _⟩ | ⟨_, ha⟩
      · rw [hK] at hQ
        cases hQ
      · rw [hK] at hQ
        cases hQ
      · exact ha
  have hCount := Wg1MmaGemmTrace.composed_count_here hpre hg stream htrace hd
    (slot := slot) rfl
  have hOrd : ((X.tr g).take i).countP (commitsTo m) = d.i / 2 := by
    rw [hAddr]
    rcases hSite with ⟨rfl, h⟩ | ⟨rfl, h⟩
    all_goals
      change ((X.tr g).take i).countP (commitsTo _) = _ at hCount
      simpa only [h, Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero] using hCount
  have hTick : commitsTo m ⟨hi.choose, .tc (.commit sp)⟩ = true := by
    simp [commitsTo, hm]
  have hNth := nthEv_eq hi.choose_spec hTick
  rw [hOrd] at hNth
  have hCM : Notify.cm X g m (d.i / 2) = i := hNth
  have hAt : X.get (g, Notify.cm X g m (d.i / 2)) = some ⟨hi.choose, .tc (.commit sp)⟩ := by
    rw [hCM]
    exact hi.choose_spec
  have hRank := Notify.rank_of hAt hTarget
  simp only [Notify.it, hCM, hRank]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) {g i : Nat}
    {d : Wg1Mma.D} {sp : TcCommit.Spec} {m : Loc} {rank : Fin 16} (hi : X.Commit (g, i) sp)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
include hpre hX hs ht hi hd

/-- An actual QK commit is observed by a softmax lane before that CTA exits. -/
theorem qk_commit_exit_order (hSite : d.site = .qkCommit)
    (hTarget : TcCommit.target sp rank = some m) (hx : CtaExited L X (ctaOf L g)) :
    RecordExitOrder L X (.async (g, i) (.tcNotify rank)) (ctaOf L g) := by
  let c := ctaOf L g
  let slot := rawSlot d.i
  let hSound := fun t ht' => (hs t ht').machine
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hc : c < L.grid := NamedBar.cta_lt hg
  obtain ⟨h, j, _, hCTA, hDealloc⟩ := dealloc_of_cta_exited hpre hX hs ht hc hx
  obtain ⟨closing, _, p, _, hBar, hState, hClosing⟩ :=
    ScoreReleaseTrace.barrier_before_dealloc hpre hX hs ht hDealloc
  obtain ⟨o, hf⟩ := ((hs g hg).machine.produces (hX.thr g hg)).fired_at hi.choose_spec hd
  have hInv : Wg1Mma.Inv P L g d := hf.choose_spec.1.2
  have hBlock := hInv.i_lt (by rw [hSite]; trivial)
  rw [StageAfterPv.block_count_eq (P := P) hCTA.symm] at hBlock
  obtain ⟨w, tag, parity, sc, q, _, hw, hSt, hQ, hIdx⟩ :=
    QueryOperandLifetime.qk_wait_before_closing hpre hX hs ht hBar hState hClosing hBlock
  have hh := Frame.lt_of_get hX hw
  have hwg : wgOf L h = 0 := RingRoleGeometry.of_trace hX hh (hs h hh).machine hSt
  obtain ⟨lane, hLane⟩ := softmax_thread hpre hCTA hwg
  have hw' : X.get (softmax L c lane, w) =
      some ⟨tag, .wait (GemmRing.qk L c slot) parity true true sc⟩ := by
    rw [← hLane]
    simpa only [hCTA] using hw
  have count := Wg0GemmTrace.composed_qk_counts hpre
    ((hs h hh).machine.produces (hX.thr h hh)) hSt hQ
  rw [hIdx, hCTA, hLane] at count
  have hCount : okPolls (GemmRing.qk L c slot) ((X.tr (softmax L c lane)).take w) = d.i / 2 :=
    count
  obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := c) hpre hX hSound
  have hgEq := hIssuer g i d rfl hd (by simp [hSite])
  subst issuer
  have hObs := acquire_qk hpre hX hSound ht hIssuer hw' hCount
  have hM : m = GemmRing.qk L c slot := by
    obtain ⟨_, q, hEq, hCase⟩ := RingCommitEvents.commit_source hpre hg hf rfl hTarget
    obtain rfl := Machine.ThreadD.mma.inj hEq
    rcases hCase with ⟨hQ, _⟩ | ⟨_, hA⟩ | ⟨hP, _⟩
    · rw [hSite] at hQ
      cases hQ
    · exact hA
    · rw [hSite] at hP
      cases hP
  rw [← hM, counted_commit hpre hX hs .qk (.inl ⟨rfl, hSite⟩) hi hd hTarget, ← hLane] at hObs
  obtain ⟨hp, hWait⟩ := hObs.waitObserves_tcNotify hw
  have hExit : CtaExited L X (ctaOf L h) := hCTA ▸ hx
  simpa only [hCTA, c] using
    record_exit_order hX (ref := .async (g, i) (.tcNotify rank)) hp hWait hExit

/-- The observed commit satisfies the shared lifetime check. -/
theorem qk_commit_finished (hSite : d.site = .qkCommit) (hTarget : TcCommit.target sp rank = some m)
    (hx : CtaExited L X (ctaOf L g)) :
    SharedFinished L kernel Assumptions.all X (.async (g, i) (.tcNotify rank)) (ctaOf L g) :=
  (qk_commit_exit_order hpre hX hs ht hi hd hSite hTarget hx).finished

/-- The last PV commit is observed by a softmax lane before its CTA exits. -/
theorem final_pv_commit_exit_order (hSite : d.site = .pvCommit)
    (hTarget : TcCommit.target sp rank = some m) (hBlock : d.i + 1 = Wg1Mma.blocks P L g)
    (hx : CtaExited L X (ctaOf L g)) :
    RecordExitOrder L X (.async (g, i) (.tcNotify rank)) (ctaOf L g) := by
  let c := ctaOf L g
  let hSound := fun t ht' => (hs t ht').machine
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hc : c < L.grid := NamedBar.cta_lt hg
  obtain ⟨h, j, _, hCTA, hDealloc⟩ := dealloc_of_cta_exited hpre hX hs ht hc hx
  obtain ⟨closing, _, p, _, hBar, hState, hClosing⟩ :=
    ScoreReleaseTrace.barrier_before_dealloc hpre hX hs ht hDealloc
  obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := ctaOf L h) hpre hX hSound
  have hgEq := hIssuer g i d hCTA.symm hd (by simp [hSite])
  subst issuer
  obtain ⟨w, wt, k, kt, sc, sp', rank', q, _, hWait, hCommit, hTarget', _, hPV, hQ,
      hQst, hObs, _⟩ :=
    StageAfterPv.final_commit_before_closing hpre hX hs ht hIssuer hBar hState hClosing
  have hh := Frame.lt_of_get hX hBar
  obtain ⟨_, hfClose⟩ := ((hs h hh).machine.produces (hX.thr h hh)).fired_at hBar hState
  have hInvClose : Wg0.Inv P L h p := hfClose.choose_spec.1.2
  have hLast := hInvClose.epilogueLast (by rw [hClosing]; rfl)
  rw [StageAfterPv.block_count_eq (P := P) hCTA.symm, ← hLast] at hBlock
  have hdq : d.i = q.i := by omega
  obtain ⟨_, hf⟩ := ((hs g hg).machine.produces (hX.thr g hg)).fired_at hi.choose_spec hd
  obtain ⟨_, q', hEq, hCase⟩ := RingCommitEvents.commit_source hpre hg hf rfl hTarget
  obtain rfl := Machine.ThreadD.mma.inj hEq
  have hM : m = GemmRing.empty L (ctaOf L h) (rawSlot p.block) := by
    rcases hCase with ⟨hQ, _⟩ | ⟨hQ, _⟩ | ⟨_, hm⟩
    · rw [hSite] at hQ
      cases hQ
    · rw [hSite] at hQ
      cases hQ
    · rw [hm, hCTA, hdq, hQ]
      rfl
  have hRef := counted_commit hpre hX hs .pv (.inr ⟨rfl, hSite⟩) hi hd hTarget
  have hRef' := counted_commit hpre hX hs .pv (.inr ⟨rfl, hPV⟩) ⟨kt, hCommit⟩ hQst hTarget'
  rw [hM, hdq, hRef'] at hRef
  obtain ⟨hp, hRecord⟩ := hObs.waitObserves_tcNotify hWait
  change X.RefPresent (.async (g, k) (.tcNotify rank')) at hp
  rw [hRef] at hp hRecord
  have hExit : CtaExited L X (ctaOf L h) := hCTA ▸ hx
  simpa only [hCTA, c] using record_exit_order hX hp hRecord hExit

/-- The observed commit satisfies the shared lifetime check. -/
theorem final_pv_commit_finished (hSite : d.site = .pvCommit)
    (hTarget : TcCommit.target sp rank = some m) (hBlock : d.i + 1 = Wg1Mma.blocks P L g)
    (hx : CtaExited L X (ctaOf L g)) :
    SharedFinished L kernel Assumptions.all X (.async (g, i) (.tcNotify rank)) (ctaOf L g) :=
  (final_pv_commit_exit_order hpre hX hs ht hi hd hSite hTarget hBlock hx).finished

/-- A PV commit whose buffer is reused is observed by an exiting dequantizer at that reuse. -/
theorem reused_pv_commit_finished (hSite : d.site = .pvCommit)
    (hTarget : TcCommit.target sp rank = some m) (hBlock : d.i + 2 < Wg1Mma.blocks P L g)
    (hx : CtaExited L X (ctaOf L g)) :
    SharedFinished L kernel Assumptions.all X (.async (g, i) (.tcNotify rank)) (ctaOf L g) := by
  let c := ctaOf L g
  let slot := rawSlot d.i
  let lane : Fin 128 := 0
  let w := GemmRing.producer L c lane
  let hSound := fun t ht' => (hs t ht').machine
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hc : c < L.grid := NamedBar.cta_lt hg
  have hSpan := Nat.mul_le_mul_right L.block (show c + 1 ≤ L.grid by omega)
  have hW : w < L.threads := by
    change c * L.block + 256 + 0 < L.grid * L.block
    rw [Nat.add_mul, Nat.one_mul] at hSpan
    have hSize := hpre.block
    omega
  have hCTA : ctaOf L w = c := by
    simp [w, lane, RawRing.consumer, ctaOf, hpre.block, Nat.mul_comm c 384,
      Nat.mul_add_div]
  have hWg : wgOf L w = 2 := GemmRing.producer_wg2 hpre c lane
  obtain ⟨tag, hLast⟩ := hx w hW hCTA
  rw [List.getLast?_eq_getElem?] at hLast
  have hExit : X.get (w, (X.tr w).length - 1) = some ⟨tag, .exit⟩ := hLast
  obtain ⟨j, _, p, _, _, hp, hSiteP, hEnd⟩ :=
    Wg2ReuseHistory.last_free_before_exit hpre hX hs ht hWg hExit
  have hE : Wg1Mma.eOf L g = Wg2.eOf L w := by
    simp only [Wg1Mma.eOf, Wg1Mma.batchOf, Wg2.eOf, ctaidY, hCTA, c]
    rfl
  have hPadded (n : Nat) : Wg1Mma.pad64 n = ceilToMultiple n topkBlock := by
    unfold Wg1Mma.pad64 ceilToMultiple topkBlock
    rw [show n + 64 - 1 = n + 63 by omega]
  have hTotal : Wg1Mma.blocks P L g = p.block + 1 := by
    rw [hEnd]
    unfold Wg1Mma.blocks Wg1Mma.total Wg1Mma.len0 Wg1Mma.len1 totalBlocks origPadded
    rw [hE, hPadded, hPadded]
    rfl
  rw [hTotal] at hBlock
  have hCount := Wg2GemmTrace.composed_reuse_polls_through_free hpre slot
    ((hs w hW).machine.produces (hX.thr w hW)) hp hSiteP
  rw [hCTA] at hCount
  let m' := GemmRing.empty L c slot
  change okPolls m' ((X.tr w).take j) = _ at hCount
  have hEnough : d.i / 2 + 1 + 1 ≤ okPolls m' ((X.tr w).take j) := by
    rw [hCount]
    change d.i / 2 + 1 + 1 ≤ (p.block + 1 + (1 - d.i % 2)) / 2
    omega
  obtain ⟨u, wt, parity, acq, sc, _, hWait, hOrd⟩ := Poll.exists_nth hEnough
  have hwg := Frame.lt_of_get hX hWait
  obtain ⟨_, rfl⟩ := GemmRing.poll (obj := .svDone) hpre hX (hs w hwg).machine ht hWait rfl
  obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := c) hpre hX hSound
  have hgEq := hIssuer g i d rfl hd (by simp [hSite])
  subst issuer
  have hObs := GemmRing.acquire_reuse hpre hX hSound hIssuer hWait hOrd
  obtain ⟨_, hf⟩ := ((hs g hg).machine.produces (hX.thr g hg)).fired_at hi.choose_spec hd
  obtain ⟨_, q, hQ, hCase⟩ := RingCommitEvents.commit_source hpre hg hf rfl hTarget
  obtain rfl := Machine.ThreadD.mma.inj hQ
  have hM : m = m' := by
    rcases hCase with ⟨hQ, _⟩ | ⟨hQ, _⟩ | ⟨_, hm⟩
    · rw [hSite] at hQ
      cases hQ
    · rw [hSite] at hQ
      cases hQ
    · exact hm
  change Witness L X (Notify.it X m' g m' (d.i / 2)) (w, u) at hObs
  rw [← hM, counted_commit hpre hX hs .pv (.inr ⟨rfl, hSite⟩) hi hd hTarget] at hObs
  obtain ⟨hp', hRecord⟩ := hObs.waitObserves_tcNotify hWait
  have hExit' : CtaExited L X (ctaOf L w) := hCTA ▸ hx
  simpa only [hCTA, c] using
    record_finished hX (ref := .async (g, i) (.tcNotify rank)) hp' hRecord hExit'

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime
