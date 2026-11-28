-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollRounds
public import Lemmas.Protocol.Poller

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib.PollEvent
open PTX PTX.Flow

theorem at_iff {e : Event} {pc : Nat} : okPollAt pc e = true ↔
    ∃ l q acq sc, e = ⟨pc,.wait l q true acq sc⟩ := by
  obtain ⟨p,k⟩ := e
  cases k <;> simp [okPollAt]
  case wait _ _ ok _ _ => cases ok <;> simp

theorem obj_iff {e : Event} {l : Loc} : okPoll l e = true ↔
    ∃ pc q acq sc, e = ⟨pc,.wait l q true acq sc⟩ := by
  obtain ⟨p,k⟩ := e
  cases k <;> simp [okPoll,sourceWaitSuccess]
  case wait _ _ ok _ _ => cases ok <;> simp

/-- Count the successful polls of one object along a cyclic sequence of objects. -/
theorem count_index {es : List Event} {l : Loc} {pc : Nat} (index : Nat → Bool)
    (visits : Nat → Nat) (seed : visits 0=0)
    (incr : ∀ n, visits (n+1)=visits n + if index n then 1 else 0)
    (classify : ∀ k e, es[k]?=some e →
      (okPoll l e=true ↔ okPollAt pc e=true ∧ index (pollRound pc (es.take k))=true)) (k : Nat) :
    okPolls l (es.take k)=visits (pollRound pc (es.take k)) := by
  induction k with
  | zero => simp [okPolls, pollRound, seed]
  | succ k ih =>
    by_cases hk : k < es.length
    · have h := classify k es[k] (List.getElem?_eq_getElem hk)
      rw [List.take_succ_eq_append_getElem hk, okPolls_snoc, ih]
      simp only [pollRound, List.countP_append, List.countP_singleton]
      cases hpc : okPollAt pc es[k] <;> simp only [hpc, Bool.false_eq_true, ite_true,
        ite_false, Nat.add_zero] at h ⊢
      · have hn : ¬ okPoll l es[k] = true := fun he => (h.mp he).1
        simp [hn]
      · rw [incr]
        simp only [true_and, pollRound] at h
        by_cases ho : okPoll l es[k] = true
        · simp [ho,h.mp ho]
        · simp [ho]; exact Bool.eq_false_iff.mpr (fun ha => ho (h.mpr ha))
    · rw [List.take_of_length_le (by omega : es.length ≤ k + 1)]
      simpa only [List.take_of_length_le (by omega : es.length ≤ k)] using ih

end PTX.Kernels.InklingRelDecode.Proof.Lib.PollEvent
