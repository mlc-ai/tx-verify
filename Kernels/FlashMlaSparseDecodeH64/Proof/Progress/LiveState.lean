-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Resource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbMmaReturn
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0
import Lemmas.Flow.Final

public section

/-! # A pending thread has a represented tail state -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem pending_event_returns (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) {g i : Nat} {e : Event} (hp : Frame.Pending L X g)
    (he : X.get (g, i) = some e) : ¬ Ends e := by
  intro hEnd
  obtain ⟨tag, kind⟩ := e
  rcases hEnd with ⟨fault, hKind⟩ | hKind
  · change kind = .ub fault at hKind
    subst kind
    exact hub ⟨(g, i), tag, fault, he⟩
  · change kind = .exit at hKind
    subst kind
    obtain ⟨_, hrun⟩ := hX.thr g hp.1
    have hLast := PTX.Flow.Run.end_last hrun he (.inr rfl)
    apply hp.2.2 tag
    rw [List.getLast?_eq_getElem?, ← hLast]
    simpa only [Nat.add_sub_cancel, Execution.get] using he

/-- Every pending lane of a consistent followed execution has a represented next event site. -/
theorem pending_followed (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} (hp : Frame.Pending L X g) :
    ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d) := by
  cases hTail : Frame.stateAt (Machine.code P L) X g (X.tr g).length with
  | some state =>
    cases state with
    | none => exact (ht g _ hp.1 hTail).elim
    | some d => exact ⟨d, rfl⟩
  | none =>
    obtain ⟨i, d, hi, hBefore, hAfter⟩ := Frame.first_stop ht hp.1 hTail
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hi⟩
    have hub := Safety.no_ub hpre hX hs ht
    have hReturns := pending_event_returns hX hub hp he
    have hLive := UbRoles.next_live hpre hX hs ht (Safety.no_resourceUnsafe hpre hX hs ht)
      (UbWg0.next_live hpre hX hs) (UbMma.next_live hpre hX hs) he hBefore hReturns
    have hNext := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hBefore, hAfter] at hNext
    exact (hLive hNext.symm).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
