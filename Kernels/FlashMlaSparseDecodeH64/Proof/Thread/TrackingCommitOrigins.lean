-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCommitControl
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCausalInduction
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingArrivals
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaTracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace
import Lemmas.Flow.NotBulk

@[expose] public section

/-! # Actual MMA commit issuers are always followed -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

private theorem dismissal_outsideMma {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Machine.ThreadD} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hn : Machine.next P L g d e = some none) : outsideMma e.pc := by
  have hpc := Frame.event_pc hs hX he hd
  rw [hpc]
  cases d
  case prologue s =>
    exact (PrologueRoleTrace.prologue_next_tracked hpre hX (fun g hg => (hs g hg).machine)
      he hd hn).elim
  case head =>
    exact (PrologueRoleTrace.dispatch_next_tracked hpre hX (fun g hg => (hs g hg).machine)
      he hd hn).elim
  case mma d =>
    exact (MmaTracking.next_tracked hpre hX (hs g (Frame.lt_of_get hX he)).machine he hd hn).elim
  case done => cases hn
  case idle s =>
    change outsideMma s.pc
    cases s <;> unfold outsideMma <;> decide
  all_goals
    rename_i d
    change outsideMma d.site.pc
    cases d.site <;> unfold outsideMma <;>
      first
      | decide
      | (rename_i a; revert a; decide)
      | (rename_i a b; revert a b; decide)
      | (rename_i a b c; revert a b c; decide)

/-- Every actual commit has a followed MMA role state. If a role has dismissed an event, the
concrete continuation cannot return from its control region to a commit instruction. -/
theorem actual_commit_fired {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {e : Event} {sp : TcCommit.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .tc (.commit sp)) :
    ∃ d o, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
      (Machine.machine P L g).Fired (some d) e o := by
  have hlen := PTX.len_of_get he
  have hg := Frame.lt_of_get hX he
  rcases Frame.fired hs hX he with ⟨s, o, hst, hf⟩ | ⟨_, tag, f, heq⟩
  · cases s with
    | some d => exact ⟨d, o, hst, hf⟩
    | none =>
      obtain ⟨j, hj, d, first, hFirst, hState, hNext⟩ := prior_dismissal hlen.le hst
      have hpc := dismissal_outsideMma hpre hX hs hFirst hState hNext
      have hOutside := later_event_in_control_region outsideMma_closed hX hg hFirst he hj hpc
      rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
      · rw [hk] at hf; cases hf
      · exact (no_commit_outsideMma hOutside hc hf hk).elim
  · rw [heq] at hk; cases hk

/-- The observed slot's ready object cannot be notified by an MMA commit, even without tracking
any consumer role. -/
theorem no_ready_commit {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i cta : Nat} {e : Event} {sp : TcCommit.Spec} {rank : Fin 16} {slot : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .tc (.commit sp))
    (hTarget : TcCommit.target sp rank = some (Protocol.IndexRing.ready L cta slot)) : False := by
  obtain ⟨_, _, _, hf⟩ := actual_commit_fired hpre hX hs he hk
  have hbound := Protocol.IndexRing.ring_addr_range (.inl rfl :
    Protocol.IndexRing.ready L cta slot = Protocol.IndexRing.ready L cta slot ∨
      Protocol.IndexRing.ready L cta slot = Protocol.IndexRing.free L cta slot)
  rcases RingCommitEvents.commit_address hpre (Frame.lt_of_get hX he) hf hk hTarget with
    h | ⟨b, h⟩ | ⟨b, h⟩
  all_goals omega

open Protocol.IndexRing in
/-- MMA commits target other barrier families, including after a consumer dismissal. -/
theorem no_free_commit
    {g i cta : Nat} {e : Event} {sp : TcCommit.Spec} {rank : Fin 16} {slot : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .tc (.commit sp))
    (hTarget : TcCommit.target sp rank = some (free L cta slot)) : False := by
  obtain ⟨_, _, _, hf⟩ := actual_commit_fired hpre hX hs he hk
  have hbound := ring_addr_range (.inr rfl :
    free L cta slot = ready L cta slot ∨ free L cta slot = free L cta slot)
  rcases RingCommitEvents.commit_address hpre (Frame.lt_of_get hX he) hf hk hTarget with
    h | ⟨b, h⟩ | ⟨b, h⟩
  all_goals omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
