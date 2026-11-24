-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteSites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Ordinals

@[expose] public section

/-! # Sparse-block ordinals of the softmax votes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0VoteCount

open PTX PTX.Flow Ledger

/-- The event predicate used by the full-mask vote instance ordinal. -/
def countsVote (e : Event) : Bool :=
  (voteClass e.kind).any (·.mask == 2 ^ 32 - 1)

variable {P : Params}

private theorem vote_false {L : Launch} {g : Nat} {d : Machine.ThreadD} {e : Event}
    {o : Option TState} (hf : (Machine.machine P L g).Fired (some d) e o)
    (hn : ∀ q, d = .wg0 q → q.site ≠ .rescaleVote) : countsVote e = false := by
  unfold countsVote
  cases hc : voteClass e.kind with
  | none => rfl
  | some p =>
    have hv : voteClass e.kind ≠ none := by simp [hc]
    obtain ⟨q, _, hq, hs, _⟩ := Wg0VoteSites.of_fired hf hv
    exact (hn q hq hs).elim

private theorem vote_step_kind {L : Launch} {g : Nat} {d d' : Wg0.D} {e : Event}
    (hs : Wg0.next P L g d e = some (some d')) (hv : d.site = .rescaleVote) :
    ∃ mode mask test r, e.kind = .voteMode mode mask test r := by
  cases he : e.kind <;> simp [Wg0.next, Wg0.nextSite, hv, he] at hs ⊢

private theorem counts_vote_of_kind {e : Event} {mask : Nat} {p r : Bool}
    (hk : e.kind = .voteMode .any mask p r) :
    (voteClass e.kind).any (·.mask == mask) = true := by
  simp only [hk, voteClass, Option.any_some, beq_self_eq_true]

/-- Each lane issues one full-mask reference vote for every preceding block. -/
theorem count_of_trace {L : Launch} {X : Execution} {g k : Nat} {d : Wg0.D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init (X.tr g))
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) :
    ((X.tr g).take k).countP (countsVote) = ordinal d :=
  Ledger.wg0 (Z := (· = .vote))
    (fun _ _ _ _ hf hc => by subst hc; exact vote_false hf fun _ h => by cases h)
    ht (fun d n => n .vote = ordinal d)
    (fun n hn => (hn _ rfl).trans (Wg0Ordinals.init_zero P L g).2.2.symm)
    (fun d _ n e o hf hs hc => by
      have hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o := hf
      change n .vote + (if countsVote e then 1 else 0) = _
      rw [hc, (Wg0Ordinals.step hs).2.2]
      by_cases hv : d.site = .rescaleVote
      · obtain ⟨mode, mask, test, r, hkind⟩ := vote_step_kind hs hv
        have hcls : voteClass e.kind ≠ none := by simp [hkind, voteClass]
        obtain ⟨q, result, _, _, hk⟩ := Wg0VoteSites.of_fired (P := P) hf hcls
        have hb : countsVote e = true := counts_vote_of_kind hk
        simp [hv, hb]
      · simp [vote_false (P := P) hf (fun q he => by cases he; exact hv), hv]) hst

/-- Each lane issues one full-mask reference vote for every preceding block. -/
theorem count_of_prefix {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hg : g < L.threads) (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) :
    ((X.tr g).take k).countP (countsVote) = ordinal d :=
  count_of_trace (hs.produces (hX.thr g hg)) hst

/-- Each lane issues one full-mask reference vote for every preceding block. -/
theorem count_at_wg0 {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) :
    ((X.tr g).take k).countP (countsVote) = ordinal d :=
  count_of_prefix hX hs (Frame.lt_of_get hX he) hst

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0VoteCount
