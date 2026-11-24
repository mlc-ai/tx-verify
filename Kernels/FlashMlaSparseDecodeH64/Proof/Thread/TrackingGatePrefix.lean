-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
import Lemmas.Flow.TraceInduction
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The actual prologue gate in a followed thread prefix -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

private def beforeGate : Option Machine.ThreadD → Prop
  | some (.prologue (.handoff _)) => False
  | some (.prologue _) | none => True
  | _ => False

private def gate : Event := ⟨97, .bar 0 none .sync⟩

private theorem gate_at_barrier {P : Params} {L : Launch} {g : Nat} {e : Event}
    {o : Option TState} (hf : (Machine.machine P L g).Fired (some (.prologue .barrier)) e o) :
    e = gate := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change Fires t.pc (match kernel.code[97]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [Flow.code_bar_0] at hf
  change (Machine.code P L g).AtD (.prologue .barrier) t at hat
  have hpc : t.pc = 97 := hat.1
  rw [hf.1, hpc]
  rfl

private theorem gate_or_before_next {P : Params} {L : Launch} {g : Nat}
    {q q' : Option Machine.ThreadD} {e : Event} {o : Option TState}
    (hBefore : beforeGate q) (hf : (Machine.machine P L g).Fired q e o)
    (hn : (Machine.machine P L g).next q e = some q') :
    e = gate ∨ beforeGate q' := by
  cases q with
  | none =>
    change some none = some q' at hn
    cases hn
    exact .inr trivial
  | some d =>
    cases d with
    | prologue s =>
      change Machine.next P L g (.prologue s) e = some q' at hn
      cases s
      case handoff w => exact hBefore.elim
      case barrier => exact .inl (gate_at_barrier hf)
      all_goals
        right
        simp only [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hn
        repeat' split at hn
        all_goals cases hn
        all_goals
          first
          | exact (show beforeGate none from trivial)
          | (simp [beforeGate]; done)
          | (rename_i hnext; repeat' split at hnext
             all_goals cases hnext
             all_goals simp only [beforeGate])
    | _ => exact hBefore.elim

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Machine.ThreadD}

private theorem before_gate_or_arrived (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) (hs : (Machine.machine P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d)) :
    beforeGate (some d) ∨ gate ∈ (X.tr g).take i :=
  (hs.produces (hX.thr g hg)).prefix_induction
    (fun q pre => beforeGate q ∨ gate ∈ pre) (.inl trivial)
    (fun q pre e q' o h hf hn => by
      rcases h with h | h
      · rcases gate_or_before_next h hf hn with rfl | h
        · exact .inr (by simp)
        · exact .inl h
      · exact .inr (List.mem_append_left [e] h)) i (some d) hd

private theorem get_gate_of_mem {X : Execution} {g i : Nat}
    (h : gate ∈ (X.tr g).take i) :
    ∃ j, j < i ∧ X.get (g, j) = some gate := by
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp h
  have hji : j < i := by simp at hj; omega
  have hjlen : j < (X.tr g).length := by simp at hj; omega
  exact ⟨j, hji, by
    change (X.tr g)[j]? = some gate
    rw [List.getElem?_eq_getElem hjlen]
    exact congrArg some (by simpa only [List.getElem_take] using hget)⟩

/-- Without an actual launch-gate arrival, a followed thread is still in the initial prologue. -/
theorem state_before_gate_of_missing (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) (hs : (Machine.machine P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hMissing : ∀ j tag, ¬ X.IsBarrier (g, j) 0 none tag) :
    ∃ s : Site, d = .prologue s ∧ ∀ w, s ≠ .handoff w := by
  rcases before_gate_or_arrived hX hg hs hd with h | h
  · cases d
    case prologue s =>
      refine ⟨s, rfl, ?_⟩
      rintro w rfl
      exact h
    all_goals exact h.elim
  · obtain ⟨j, _, hj⟩ := get_gate_of_mem h
    exact (hMissing j _ hj).elim

/-- Every actually followed body event is strictly past an actual prologue gate in that
thread, independently of the roles followed by any other thread. -/
private theorem gate_event_in_prefix (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d)) (hrole : ∀ s, d ≠ .prologue s) :
    ∃ j, j < i ∧ X.get (g, j) = some ⟨97, .bar 0 none .sync⟩ := by
  have h := before_gate_or_arrived hX hg hs hd
  rcases h with h | h
  · cases d
    case prologue s => exact (hrole s rfl).elim
    all_goals exact h.elim
  · exact get_gate_of_mem h

/-- Every followed body state is past its own prologue gate and subsequent handoff. -/
theorem gate_before_followed_state (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d)) (hrole : ∀ s, d ≠ .prologue s) :
    ∃ j, j + 1 < i ∧ X.get (g, j) = some ⟨97, .bar 0 none .sync⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .barrier)) := by
  obtain ⟨j, hj, hbar⟩ := gate_event_in_prefix hX hs hg hd hrole
  obtain ⟨q, hq⟩ := FollowedPrefix.state_at hd hj.le
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX hs hbar hq
  obtain ⟨rfl, _, _⟩ := RingGateEvents.gate_source hf rfl
  refine ⟨j, ?_, hbar, hq⟩
  by_contra! h
  have heq : i = j + 1 := by omega
  have hnext := Frame.stateAt_succ (C := Machine.code P L) hbar
  rw [hq, ← heq, hd] at hnext
  change some (some d) = Machine.next P L g (.prologue .barrier) gate at hnext
  simp only [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hnext
  cases hnext
  exact hrole _ rfl

/-- At a real body event the thread has already passed its own prologue gate. -/
theorem gate_in_followed_prefix {e : Event} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d)) (hrole : ∀ s, d ≠ .prologue s) :
    ∃ j, j + 1 < i ∧ X.get (g, j) = some ⟨97, .bar 0 none .sync⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .barrier)) :=
  gate_before_followed_state hX hs (Frame.lt_of_get hX he) hd hrole

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
