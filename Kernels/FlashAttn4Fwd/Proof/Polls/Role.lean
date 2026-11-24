-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Waits
public import Kernels.FlashAttn4Fwd.Proof.Progress.Collective
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressAsync
public import Kernels.FlashAttn4Fwd.Proof.Protocol.PollState

@[expose] public section

/-! # What every mbarrier poll class uses of the waiter's role state

A thread in a role state has a nonempty trace: its first state is the prologue's
(`ne_nil_of_role`). A thread whose state is later than the register requests' time has made its
request (`reg_of_time`, from `RegWaitFacts.before`), so the table barriers of its CTA have a final
state (`state_of_time`, `InitFirst.state_of_reg`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- A thread in a role state has a nonempty trace. -/
theorem ne_nil_of_role {r : Role} (hσ : St L X g (X.tr g).length = some (some (.inr r))) :
    X.tr g ≠ [] := by
  intro h0
  have h0' : St L X g (X.tr g).length = some (some (.inl ⟨.shfl0⟩)) := by
    rw [h0]
    exact Frame.stateAt_zero
  rw [h0'] at hσ
  cases hσ

/-- A thread at a state later than the register requests' time has made its request. -/
theorem reg_of_time (hW : WaitInputs L X) (hg : g < L.threads) {d : ThreadD}
    (hσ : St L X g (X.tr g).length = some (some d)) (ht : Time.regT < stateTime L g d) :
    ∃ j pc inc n inst, X.get (g, j) = some ⟨pc, .setMaxReg inc n inst⟩ := by
  by_contra hn
  push Not at hn
  have := hW.waits.reg.before hg (fun j pc inc n inst => hn j pc inc n inst)
  rw [endTime_of hσ] at this
  omega

/-- **A table barrier of the CTA of a thread later than the register requests has a final
state.** -/
theorem state_of_time (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hI : AsyncInputs P L X) (hW : WaitInputs L X) (hg : g < L.threads) {d : ThreadD}
    (hσ : St L X g (X.tr g).length = some (some d)) (ht : Time.regT < stateTime L g d)
    (b : FBar) :
    ∃ s, stateBefore (X.objects (b.loc L (ctaOf L g))) (X.objects (b.loc L (ctaOf L g))).length =
      some s := by
  obtain ⟨j, pc, inc, n, inst, he⟩ := reg_of_time hW hg hσ ht
  exact InitFirst.state_of_reg hpre hX hI.cluster hW.tmem hI.init b he rfl

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
