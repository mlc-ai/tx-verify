-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0MaxReadback
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerContinuation
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerQkValues
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MaxTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput
import Lemmas.Flow.SetpCore

@[expose] public section

/-! # The successor of the actual peer maximum load -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0MaxSuccessor

open PTX PTX.Proof PTX.Flow PTX.Assumption Wg0 MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i : Nat} {d : D} {e : Event}

private theorem decode_peak (p : WithBot ℝ) : decodePeak (peakVal p) = some p := by
  cases p with
  | bot => rfl
  | coe x =>
    have hn : fl x ≠ negInf := by intro h; cases h
    change decodePeak (fl x) = some ↑x
    simp [decodePeak, hn, valFloat_fl, Except.toOption]
    rfl

private theorem peak_sub_reference (p : WithBot ℝ) (d : D) :
    ∃ gap : WithBot ℝ, subE true (peakVal p) (miVal d) = .ok (peakVal gap) := by
  cases p with
  | bot =>
    refine ⟨⊥, ?_⟩
    have hNeg : readEReal .f32 negInf = some (.ok (⊥ : EReal)) := rfl
    rw [subE, idealSub, show peakVal ⊥ = negInf from rfl, hNeg,
      readEReal_of_valFloat (valFloat_miVal d)]
    simp [bindRead, addEReal, pure, Except.pure, ← EReal.coe_neg]
    rfl
  | coe x =>
    refine ⟨↑(x - reference d), ?_⟩
    exact subE_fin (valFloat_fl x) (valFloat_miVal d)

private theorem peak_vote (gap : WithBot ℝ) :
    ∃ test, setpE (.ord .gt) true (peakVal gap) (b32 1086324736) = .ok test := by
  have hThreshold : ∃ y : EReal, readEReal .f32 (b32 1086324736) = some (.ok y) :=
    ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := hThreshold
  have hGap : ∃ x : EReal, readEReal .f32 (peakVal gap) = some (.ok x) := by
    cases gap with
    | bot => exact ⟨⊥, rfl⟩
    | coe x => exact ⟨x, readEReal_of_valFloat (valFloat_fl x)⟩
  obtain ⟨x, hx⟩ := hGap
  exact ⟨erealCompare .gt x y, by
    simp only [setpE, idealSetp, fcmpBase, hx, hy, bindRead, pure, Except.pure]⟩

/-- The vote input accepts two finite-or-masked row maxima. Its block maximum stays in that form. -/
theorem withPeerMax_of_peaks {d : D} {own peer : WithBot ℝ}
    (hOwn : rowLocalMax L d = peakVal own) :
    ∃ d', withPeerMax L d (peakVal peer) = some d' ∧
      d'.blockMax = peakVal (max own peer) ∧ d'.peak = max d.peak (max own peer) := by
  let m := max own peer
  obtain ⟨gap, hGap⟩ := peak_sub_reference m d
  obtain ⟨test, hTest⟩ := peak_vote gap
  refine ⟨{ d with blockMax := peakVal m, peak := max d.peak m, voteTest := test }, ?_, rfl, rfl⟩
  simp only [withPeerMax, hOwn, peerMaxE_peak, show max own peer = m from rfl,
    Except.toOption, bind, Option.bind, decode_peak, hGap, hTest]
  rfl

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- Read-back identifies the paired lane's peak, and the actual memory event advances to the vote
if each local maximum has the canonical representation. -/
theorem actual_next_of_peak_values (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hOwn : ∃ v : WithBot ℝ, rowLocalMax L d = peakVal v)
    (hPeer : ∀ j (q : D) fp,
      Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j = some (some (.wg0 q)) →
      q.site = .rowMax → q.block = d.block →
      X.Writes (Wg0PeerSources.partner L g, j) fp (rowLocalMax L q).toBytes →
      baseCausality L X (Wg0PeerSources.partner L g, j) (g, i) →
      ∃ v : WithBot ℝ, rowLocalMax L q = peakVal v) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .maxRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d' : D,
        Machine.next P L g (.wg0 d) e = some (some (.wg0 { d' with site := .rescaleVote })) ∧
        (∃ v : WithBot ℝ, d'.blockMax = peakVal v) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (Frame.trace hs hX hg).fired_at he hd
  cases o with
  | none => exact .inl (composed_ending_next hf)
  | some u =>
    obtain ⟨_, _, hat, hInv, hCode, hFire⟩ := Frame.fired_site_of hs hg hf
    obtain ⟨a, bs, hk, hloc, hz, _, _⟩ := fires_maxRead hpre hsite hat hInv hCode hFire
    have hRead : X.Reads (g, i) a bs := by
      cases e
      exact ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hk))⟩
    obtain ⟨j, q, fp, hQ, hQS, hQB, hw, hBefore, hRebuild⟩ :=
      Wg0MaxReadback.actual_readback_value hpre hX hs hRead hd hsite le_rfl
        (PTX.len_of_get he) hPrior
    obtain ⟨peer, hp⟩ := hPeer j q fp hQ hQS hQB hw hBefore
    obtain ⟨own, ho⟩ := hOwn
    obtain ⟨d', hMax, hBlock, _⟩ := withPeerMax_of_peaks (peer := peer) ho
    refine .inr ⟨d', ?_, max own peer, hBlock⟩
    rw [hp] at hRebuild
    simp [Machine.next, Wg0.next, nextSite, hsite, hk, siteLoc, hloc, hz, Site.elemBytes,
      hRebuild, hMax, Except.toOption]

omit hpre hX in
/-- The pairs consumed by an actual row-maximum store come from the recorded peer reads. -/
theorem masked_pairs_at_rowMax {cut : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hpeer : Wg0PeerSuccessor.PeerScoresReal P L X)
    (hown : Wg0PeerSuccessor.OwnScoresReal P L X)
    (hg : g < L.threads) (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rowMax) : ∀ k < 16, MaskedPair (d.scoreSums k) := by
  obtain ⟨j, e, q, rfl, he, hq, hqs⟩ :=
    Wg0MaxTrace.peer_before_rowMax hX hs hg (hCut.trans hLen.le) hd hsite
  have hEarlier : j ≤ cut := by omega
  have hp := Wg0PeerSuccessor.actual_prefix_at hpre hX hs hpeer hown hLen hPrior hEarlier hq hqs
  have hstep : Machine.next P L g (.wg0 q) e = some (some (.wg0 d)) := by
    rw [Frame.stateAt_succ he, hq, Option.bind_some] at hd
    exact hd
  rcases Wg0PeerSuccessor.actual_next hpre hX hs hpeer (hown g j q 7 hq hqs) he hq hqs hp
    hEarlier hLen hPrior with
    hdead | ⟨d', hnext, _, hmore | hmax⟩
  · rw [hdead] at hstep
    cases hstep
  · rw [hnext] at hstep
    cases hstep
    obtain ⟨_, hsite', _, _⟩ := hmore
    simp [hsite] at hsite'
  · rw [hnext] at hstep
    cases hstep
    exact hmax.2.2

/-- The actual final QK cells give both lanes' completed pairs and a canonical block maximum
at the rescale vote. -/
theorem actual_next (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hv : Wg0PeerQkValues.QkValues P L X) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .maxRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d' : D, Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
        d'.site = .rescaleVote ∧ (∃ v : WithBot ℝ, d'.blockMax = peakVal v) ∧
        (∀ k < 16, MaskedPair (d.scoreSums k)) := by
  obtain ⟨hpeer, hown⟩ := Wg0PeerQkValues.real_scores hpre hX hs hv
  have hg := Frame.lt_of_get hX he
  have hlen : i ≤ (X.tr g).length := Nat.le_of_lt (PTX.len_of_get he)
  obtain ⟨j, q, hj, hq, hqs, _, hm⟩ :=
    Wg0MaxTrace.rowMax_state_before_maxRead hX hs hg hlen hd hsite
  have hOwn : ∀ k < 16, MaskedPair (d.scoreSums k) := by
    rw [hm]
    exact masked_pairs_at_rowMax (i := j) (cut := i) hpre hX hs hpeer hown hg (by omega)
      (PTX.len_of_get he) hPrior hq hqs
  have hMax := rowLocalMax_of_masked hpre (d := d) hOwn
  have hPeer : ∀ j (q : D) fp,
      Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j = some (some (.wg0 q)) →
      q.site = .rowMax → q.block = d.block →
      X.Writes (Wg0PeerSources.partner L g, j) fp (rowLocalMax L q).toBytes →
      baseCausality L X (Wg0PeerSources.partner L g, j) (g, i) →
      ∃ v : WithBot ℝ, rowLocalMax L q = peakVal v := by
    intro j q fp hq hs' _ hw hBefore
    apply rowLocalMax_of_masked hpre
    exact masked_pairs_at_rowMax hpre hX hs hpeer hown
      (Frame.lt_of_get hX hw.choose_spec) le_rfl
      (PTX.len_of_get hw.choose_spec)
      (fun t ht => hPrior t (ht.trans hBefore)) hq hs'
  rcases actual_next_of_peak_values hpre hX hs hMax hPeer he hd hsite hPrior with
    hdead | ⟨d', hn, hb⟩
  · exact .inl hdead
  · exact .inr ⟨{ d' with site := .rescaleVote }, hn, rfl, hb, hOwn⟩

/-- The maximum successor in a tracked execution. -/
theorem next (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hv : Wg0PeerQkValues.QkValues P L X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .maxRead)
    :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d' : D, Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
        d'.site = .rescaleVote ∧ (∃ v : WithBot ℝ, d'.blockMax = peakVal v) ∧
        (∀ k < 16, MaskedPair (d.scoreSums k)) :=
  actual_next hpre hX hs hv he hd hsite (fun t _ => tracked_not_dismisses hX ht t)

/-- A peer maximum load cannot stop tracking before the vote. -/
theorem never_dismiss (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hv : Wg0PeerQkValues.QkValues P L X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .maxRead)
    :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  rcases next hpre hX hs ht hv he hd hsite with hdead | ⟨_, hn, _⟩
  · rw [hdead]
    intro h
    cases h
  · rw [hn]
    intro h
    cases h

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0MaxSuccessor
