-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WyState
public import Kernels.InklingRelDecode.Proof.Interface.ShapeOdone

@[expose] public section

/-!
# `PollsBlocked` from the blocker clause

`Sched.PollBlocked` has three parts: the next event of the thread is the poll of one object with one
parity (`poll_next`), the object has a final state (`pollAt_final`), and when that state's phase
has the poll's parity the thread has a blocker. The first two are proved for the six polls; the
third is `PollsRest`, stated with the object and parity of `PollAt`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wy
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The blocker clause of the polls**: a released pending thread of a maximal execution at a
poll of `m` with parity `par` (`PollAt`) has a blocker when the final phase of `m` has the parity
`par`. -/
def PollsRest (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g s m par before, Maximal L kernel asms mem0 X → Frame.Pending L X g →
    Step.Released L X g → St Q L X g (X.tr g).length = some (some s) → PollAt L g s m par →
    MBarrier.stateBefore (X.objects m) (X.objects m).length = some before →
    before.phase % 2 = par % 2 → Sched.Blk (timed T Q L) X g

/-- **`PollsBlocked` from the blocker clause.** -/
theorem pollsBlocked_of (hpre : Pre Q L mem0)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hF : ∀ X, Consistent L kernel asms mem0 X → ThreadFacts Q L mem0 X)
    (hR : ∀ X, Consistent L kernel asms mem0 X → RoleReads L X)
    (hub : ∀ X, Consistent L kernel asms mem0 X → ¬ HasUb X)
    (h : PollsRest T Q L mem0) : PollsBlocked T Q L mem0 := by
  intro X g s hmax hp hrel hσ hk
  have hX := hmax.1
  have hf := hF X hX
  obtain ⟨m, pcw, par, hat, hpoll⟩ := poll_next hpre hmax hS hf.ldRng hp hrel hσ hk
  obtain ⟨t, hr⟩ := Frame.run_some hX (hub X hX) hp
  obtain ⟨-, -, -, -, hinv, -⟩ := Frame.end_at (C := code L Q) hS hp.1 hr hσ
  obtain ⟨before, hst⟩ := pollAt_final hpre hX hS (hR X hX) hp.1 hσ hinv hat
  exact ⟨m, pcw, par, hpoll, before, hst, h X g s m par before hmax hp hrel hσ hat hst⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wy
