-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0MaxSuccessor
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Probability
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MaxTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch
import Lemmas.Flow.Recip
import Lemmas.Order.OrderBaseCausality

@[expose] public section

/-! # The successor of the actual reference vote -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0VoteSuccessor

open PTX PTX.Proof PTX.Flow PTX.Assumption Wg0 MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i : Nat} {d : D} {e : Event}

private theorem vote_gain_word {d q : D} {r : Bool}
    (h : afterReferenceVote d r = some q) : outputWord q.gainWord = true := by
  cases r
  · have he : q = { d with gainWord := b32 1065353216 } := Option.some.inj h.symm
    rw [he]
    have hShape : Assumptions.scoreHalf (b32 1065353216) := by
      change (BitVec.ofNat 64 1065353216).toNat < 2 ^ 32
      decide
    change decide (Assumptions.scoreHalf (b32 1065353216)) &&
      (valFloat .f32 (.bits 32 (BitVec.ofNat 64 1065353216))).toOption.isSome = true
    rw [decide_eq_true hShape, valFloat_one]
    rfl
  · simp only [afterReferenceVote, ↓reduceIte] at h
    obtain ⟨ref, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mi, _, h⟩ := Option.bind_eq_some_iff.mp h
    by_cases he : ref = fl mi
    · subst ref
      simp only [ite_true] at h
      rw [show (subE true (miVal d) (fl mi)).toOption =
        some (fl (reference d - mi)) from
          congrArg Except.toOption (subE_fin (valFloat_miVal d) (valFloat_fl mi))] at h
      simp only [bind, Option.bind, ex2E_fin (valFloat_fl (reference d - mi)),
        Except.toOption, pure, Option.some.injEq] at h
      subst q
      let x := Real.rpow 2 (reference d - mi)
      change decide (Assumptions.scoreHalf (fl x)) && (valFloat .f32 (fl x)).toOption.isSome = true
      rw [decide_eq_true (show Assumptions.scoreHalf (fl x) from trivial), valFloat_fl]
      rfl
    · simp [he] at h

private theorem probability_gain {q v : D}
    (h : probabilityUpdate L g q = some v) : v.gainWord = q.gainWord := by
  simp only [probabilityUpdate, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

/-- A vote that advanced to a probability store already produced a finite gain. -/
theorem gain_of_accepted_vote {q u : D} {e : Event}
    (hSite : q.site = .rescaleVote)
    (hNext : Machine.next P L g (.wg0 q) e = some (some (.wg0 u))) :
    outputWord u.gainWord = true := by
  cases hk : e.kind <;> simp only [Machine.next, Wg0.next, nextSite, hSite, hk] at hNext
  all_goals try (cases hNext)
  rename_i mode mask p r
  cases hv : afterReferenceVote q r with
  | none => simp [hv] at hNext
  | some v =>
    cases hp : probabilityUpdate L g { v with voteTaken := r } with
    | none => simp [hv, hp] at hNext
    | some s =>
      simp only [hv, Option.bind_some, hp, Option.map_some, Option.some.injEq,
        Machine.ThreadD.wg0.injEq] at hNext
      cases hNext
      change outputWord s.gainWord = true
      rw [probability_gain hp]
      change outputWord v.gainWord = true
      exact vote_gain_word hv

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
include hpre hX hs

/-- The actual peer maximum event supplies the row maximum and all the exponent operands. -/
private theorem actual_inputs_of_vote (hv : Wg0PeerQkValues.QkValues P L X)
    (heVote : X.get (g, i) = some e) (hNoAccess : e.acc = none)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    (∃ m : WithBot ℝ, d.blockMax = peakVal m) ∧ (∀ k < 16, MaskedPair (d.scoreSums k)) := by
  have hg := Frame.lt_of_get hX heVote
  have hlen : i < (X.tr g).length := PTX.len_of_get heVote
  obtain ⟨j, ev, q, rfl, he, hq, hqs, hm⟩ :=
    Wg0MaxTrace.maxRead_before_vote hX hs hg hlen.le hd hsite
  have hNone : (X.get (g, j + 1)).bind Event.acc = none := by
    rw [heVote]
    exact hNoAccess
  have hPo : baseCausality L X (g, j) (g, j + 1) :=
    .single (.inl (po_of_not_access rfl (Nat.lt_succ_self _) hlen hNone))
  have hstep : Machine.next P L g (.wg0 q) ev = some (some (.wg0 d)) := by
    rw [Frame.stateAt_succ he, hq, Option.bind_some] at hd
    exact hd
  rcases Wg0MaxSuccessor.actual_next hpre hX hs hv he hq hqs
    (fun t h => hPrior t (h.trans hPo)) with hdead | ⟨u, hn, _, hb, hPairs⟩
  · rw [hdead] at hstep
    cases hstep
  · rw [hn] at hstep
    cases hstep
    exact ⟨hb, by rw [hm]; exact hPairs⟩

/-- Recover the vote operands in a globally tracked execution. -/
theorem inputs_of_vote (ht : Frame.Tracked (Machine.code P L) X)
    (hv : Wg0PeerQkValues.QkValues P L X) (hg : g < L.threads) (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    (∃ m : WithBot ℝ, d.blockMax = peakVal m) ∧ (∀ k < 16, MaskedPair (d.scoreSums k)) := by
  obtain ⟨j, e, q, rfl, he, hq, hqs, hm⟩ := Wg0MaxTrace.maxRead_before_vote hX hs hg hlen hd hsite
  have hstep : Machine.next P L g (.wg0 q) e = some (some (.wg0 d)) := by
    rw [Frame.stateAt_succ he, hq, Option.bind_some] at hd
    exact hd
  rcases Wg0MaxSuccessor.next hpre hX hs ht hv he hq hqs with hdead | ⟨u, hn, _, hb, hPairs⟩
  · rw [hdead] at hstep
    cases hstep
  · rw [hn] at hstep
    cases hstep
    exact ⟨hb, by rw [hm]; exact hPairs⟩

/-- The actual collective result determines the reference and probability updates, and the next
probability store carries a finite rescale gain. -/
theorem actual_next (hv : Wg0PeerQkValues.QkValues P L X) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t)
    :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d' : D, Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
        d'.site = .pStore 0 ∧ outputWord d'.gainWord = true := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (Frame.trace hs hX hg).fired_at he hd
  cases o with
  | none => exact .inl (composed_ending_next hf)
  | some u =>
    obtain ⟨_, _, ha, _, hc, hFire⟩ := Frame.fired_site_of hs hg hf
    obtain ⟨r, hk, _⟩ := fires_rescaleVote hsite ha hc hFire
    have hNoAccess : e.acc = none := by
      obtain ⟨tag, k⟩ := e
      change k = _ at hk
      rw [hk]
      rfl
    obtain ⟨⟨m, hm⟩, hScores⟩ :=
      actual_inputs_of_vote hpre hX hs hv he hNoAccess hPrior hd hsite
    obtain ⟨q, hq, _, hGain⟩ := Result.afterReferenceVote_ratio m hm r
    let s : D := { q with voteTaken := r }
    have hMask (k : Fin 16) : MaskedPair (s.scoreSums k.val) := by
      have hEq : q.scoreSums = d.scoreSums := by rw [afterReferenceVote_fields hq]
      change MaskedPair (q.scoreSums k.val)
      rw [hEq]
      exact hScores _ k.isLt
    choose lo hi hValues using hMask
    obtain ⟨v, hp, _, _, _⟩ := Result.probabilityUpdate_terms
      (g := g) hpre s lo hi _ hValues hGain
    have hWord : outputWord v.gainWord = true := by
      rw [probability_gain hp]
      change outputWord q.gainWord = true
      exact vote_gain_word hq
    refine .inr ⟨{ v with site := .pStore 0, rescale := wantsRescale v }, ?_, rfl, hWord⟩
    simp [Machine.next, Wg0.next, nextSite, hsite, hk, hq, ← show s = { q with voteTaken := r }
      from rfl, hp]

/-- The reference vote in a globally tracked execution. -/
theorem next (ht : Frame.Tracked (Machine.code P L) X) (hv : Wg0PeerQkValues.QkValues P L X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d' : D, Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
        d'.site = .pStore 0 ∧ outputWord d'.gainWord = true :=
  actual_next hpre hX hs hv he hd hsite (fun t _ => tracked_not_dismisses hX ht t)

/-- A reference vote cannot stop tracking before the probability stores. -/
theorem never_dismiss (ht : Frame.Tracked (Machine.code P L) X)
    (hv : Wg0PeerQkValues.QkValues P L X) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  rcases next hpre hX hs ht hv he hd hsite with hdead | ⟨_, hn, _⟩
  · rw [hdead]
    intro h
    cases h
  · rw [hn]
    intro h
    cases h

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0VoteSuccessor
